"""Per-kernel CUPTI trace of steady-state speculative decode rounds (throwaway; Main runs it).

Runs INSIDE the image in place of the server (service stopped), like profile_round.py / parity.py:

    python -I -B kernel_trace.py OUT_DIR        # GPU: writes OUT_DIR/kernel-trace.json + trace-<case>.json
    python -I -B kernel_trace.py --check        # CPU-only: imports, hook targets, CUPTI lib, byte table,
                                                # meta model, analyzer self-test on a synthetic trace

Constructs the real serve/exl3_server.Server (same args as profile_round.py), warms up, then for each
case (AIME thinking prompt, 8K context, 32K context) starts torch.profiler (CPU + CUDA activity, CUPTI)
from inside the generator worker thread at a round boundary, profiles 1 pre-roll + 3 measured decode
rounds (one round = one Generator.iterate()), synchronizes, stops. Instrumentation is in-process
monkeypatching only; while no capture is active every wrapper is a plain passthrough.

Attribution: every GPU activity (kernel / memcpy / memset) is joined by CUPTI correlation id to the
API call that launched it (cudaLaunchKernel, cuLaunchKernel(Ex) for Triton, cudaGraphLaunch for the
per-layer CUDA graphs, cudaMemcpyAsync ...). The launch call's CPU timestamp is placed in the innermost
record_function ranges emitted by the wrappers:
  kt:round:<i>   Generator.iterate
  kt:ph:<phase>  draft (dflash gen), draft_forward, draft_sample, gen (iterate_gen), verify_forward
                 (target model.forward), sampler, accept, rewind (GDNState.rewind, incl. commit replay),
                 draft_kv_refresh, ckpt, prefill
  kt:mod:<kind>:L<i>  target block / gdn / attn / mlp / lm_head / top (embedding, final norm)
  kt:dmod:<kind>:L<i> draft modules (sub-labels only)
Kernels launched by a graph share the cudaGraphLaunch correlation id, so they inherit the range of
the module whose forward replayed the graph.

Gap metrics are computed on the union of GPU activity intervals (all streams). A gap is "host-late"
when the launching API call started after the previous activity ended (GPU starved by the host),
otherwise "gpu-side" (work was already queued: pure kernel-boundary cost). Kernel ramp/tail inside a
kernel's own duration is not visible as a gap.
"""

from __future__ import annotations

import argparse
import bisect
import collections
import glob
import hashlib
import json
import random
import re
import statistics
import struct
import sys
import time
from pathlib import Path

LOREM = (
    "The committee reviewed the quarterly logistics report, noting that warehouse "
    "throughput in the northern region rose while spoilage in cold storage declined. "
    "Several appendices list shipment identifiers, carrier delays and customs holds. "
)
AIME = (
    "Find the number of ordered pairs (x, y) of integers with -100 <= x, y <= 100 "
    "such that 12x^2 - xy - 6y^2 = 0. Put the final answer in \\boxed{}."
)
CARRIERS = ["Almeda", "Borealis", "Castell", "Dunmore", "Evander", "Fennick", "Galway", "Hollis"]
PORTS = ["Veyra", "Korsa", "Maridun", "Tolland", "Ossel", "Brevik", "Caldera", "Nyhavn"]
GOODS = ["copper wire", "frozen fish", "textbooks", "turbine blades", "coffee", "glassware",
         "solar panels", "rice", "medical gloves", "bicycle frames"]

TARGET_DIR = "/models/qwen38-27b-exl3"
DRAFT_DIR = "/models/dflash2-exl3"
PEAK_GBS = 936.0
GAP_SMALL_US = 10.0
GAP_BINS_US = [0.0, 1.0, 2.0, 4.0, 10.0, 100.0, 1000.0, float("inf")]
MEASURED_ROUNDS = 3

# (name, prompt kind, max_tokens, decode round index of the pre-roll; measured = next 3)
CASES = [
    ("aime-think", "aime", 512, 40),
    ("ctx-8192", "ctx8", 256, 16),
    ("ctx-32768", "ctx32", 256, 16),
]

perf = time.perf_counter
torch = None  # bound by load_engine()

GEMM_RE = re.compile(r"gemm|gemv", re.I)
LAUNCH_CATS = ("cuda_runtime", "cuda_driver")
GPU_CATS = ("kernel", "gpu_memcpy", "gpu_memset")

BUCKETS = [
    "target_mlp_gemm", "target_mlp_other", "gdn_gemm", "gdn_small", "attn_proj_gemm", "attn_split",
    "attn_combine", "attn_other", "norms_residual", "lm_head", "target_embed", "target_other",
    "draft_forward", "draft_other", "draft_sample_head", "draft_sample_topk", "draft_sample_walk",
    "draft_sample_other", "sampler", "accept", "rewind_replay", "draft_kv_refresh", "ckpt", "prefill",
    "gen_other", "memcpy", "other",
]


# --------------------------------------------------------------------------------------------
# Weight byte table from safetensors headers

def st_header(path: str) -> dict:
    with open(path, "rb") as f:
        n = struct.unpack("<Q", f.read(8))[0]
        h = json.loads(f.read(n))
    h.pop("__metadata__", None)
    return h


DT_BYTES = {"F16": 2, "BF16": 2, "F32": 4, "I16": 2, "I32": 4, "I8": 1, "U8": 1, "F64": 8, "I64": 8}


def tensor_bytes(meta: dict) -> int:
    a, b = meta["data_offsets"]
    n = 1
    for d in meta["shape"]:
        n *= d
    nb = n * DT_BYTES[meta["dtype"]]
    if nb != b - a:
        raise RuntimeError(f"safetensors size mismatch {meta}")
    return nb


def load_tensors(model_dir: str) -> dict[str, int]:
    files = sorted(glob.glob(f"{model_dir}/*.safetensors"))
    if not files:
        raise RuntimeError(f"no safetensors in {model_dir}")
    out = {}
    for f in files:
        for k, v in st_header(f).items():
            out[k] = tensor_bytes(v)
    return out


def linear_bytes(t: dict[str, int], prefix: str) -> int:
    """Streamed bytes of one linear: EXL3 trellis + suh + svh (mul1 is a scalar, not streamed), or a
    dense .weight. Raises if the prefix names no weight."""
    if prefix + ".trellis" in t:
        return t[prefix + ".trellis"] + t.get(prefix + ".suh", 0) + t.get(prefix + ".svh", 0)
    if prefix + ".weight" in t:
        return t[prefix + ".weight"]
    raise KeyError(prefix)


def build_byte_table(target_dir: str = TARGET_DIR, draft_dir: str = DRAFT_DIR) -> dict:
    t = load_tensors(target_dir)
    d = load_tensors(draft_dir)
    lp = "model.language_model.layers"
    n_layers = 1 + max(int(m.group(1)) for k in t if (m := re.match(lp + r"\.(\d+)\.", k)))
    layers = []
    for i in range(n_layers):
        p = f"{lp}.{i}"
        L = {"mlp.gate": linear_bytes(t, f"{p}.mlp.gate_proj"),
             "mlp.up": linear_bytes(t, f"{p}.mlp.up_proj"),
             "mlp.down": linear_bytes(t, f"{p}.mlp.down_proj")}
        if f"{p}.linear_attn.in_proj_qkv.trellis" in t:
            L["kind"] = "gdn"
            L["gdn.qkv"] = linear_bytes(t, f"{p}.linear_attn.in_proj_qkv")
            L["gdn.z"] = linear_bytes(t, f"{p}.linear_attn.in_proj_z")
            L["gdn.ba"] = linear_bytes(t, f"{p}.linear_attn.in_proj_b") + linear_bytes(t, f"{p}.linear_attn.in_proj_a")
            L["gdn.out"] = linear_bytes(t, f"{p}.linear_attn.out_proj")
            L["gdn.conv1d"] = t[f"{p}.linear_attn.conv1d.weight"]
        elif f"{p}.self_attn.q_proj.trellis" in t:
            L["kind"] = "attn"
            L["attn.qkv"] = sum(linear_bytes(t, f"{p}.self_attn.{x}_proj") for x in "qkv")
            L["attn.o"] = linear_bytes(t, f"{p}.self_attn.o_proj")
        else:
            raise RuntimeError(f"layer {i}: neither linear_attn nor self_attn")
        layers.append(L)
    draft_layers = sorted({int(m.group(1)) for k in d if (m := re.match(r"layers\.(\d+)\.", k))})
    draft_fwd = sum(v for k, v in d.items() if k.startswith("layers.") and not k.endswith(".mul1"))
    draft_linear = sum(linear_bytes(d, f"layers.{i}.{m}") for i in draft_layers for m in
                       ("self_attn.q_proj", "self_attn.k_proj", "self_attn.v_proj", "self_attn.o_proj",
                        "mlp.gate_proj", "mlp.up_proj", "mlp.down_proj"))
    tot = collections.Counter()
    for L in layers:
        for k, v in L.items():
            if k != "kind":
                tot[k] += v
    table = {
        "note": "bytes = trellis + suh + svh per EXL3 linear (mul1 scalar excluded); dense fp16/bf16 .weight as stored",
        "target_layers": layers,
        "target_totals_per_forward": dict(tot),
        "target_mlp_per_forward": tot["mlp.gate"] + tot["mlp.up"] + tot["mlp.down"],
        "target_gdn_proj_per_forward": tot["gdn.qkv"] + tot["gdn.z"] + tot["gdn.ba"] + tot["gdn.out"],
        "target_attn_proj_per_forward": tot["attn.qkv"] + tot["attn.o"],
        "lm_head": linear_bytes(t, "lm_head"),
        "embed_tokens": t["model.language_model.embed_tokens.weight"],
        "draft_forward_all_layer_tensors": draft_fwd,
        "draft_forward_linears": draft_linear,
        "draft_fc": linear_bytes(d, "fc"),
        "draft_selector": sum(v for k, v in d.items() if k.startswith("candidate_selector.")),
        "n_target_layers": n_layers,
        "n_gdn_layers": sum(1 for L in layers if L["kind"] == "gdn"),
        "n_attn_layers": sum(1 for L in layers if L["kind"] == "attn"),
        "n_draft_layers": len(draft_layers),
    }
    table["target_weight_gemm_per_forward"] = (table["target_mlp_per_forward"] + table["target_gdn_proj_per_forward"]
                                               + table["target_attn_proj_per_forward"] + table["lm_head"])
    return table


# --------------------------------------------------------------------------------------------
# Capture state and hooks

class Cap:
    armed = False          # hooks may start a capture
    active = False         # ranges are being recorded
    case = None            # dict for the case in progress
    warm_profiler = False


def rf(label):
    return torch.profiler.record_function(label)


def wrap_inst(obj, attr, label_fn, hooked, name):
    orig = getattr(obj, attr)
    def w(*a, **k):
        if not Cap.active:
            return orig(*a, **k)
        with rf(label_fn()):
            return orig(*a, **k)
    setattr(obj, attr, w)
    hooked.append(name)


def wrap_cls(cls, attr, label, hooked):
    orig = getattr(cls, attr)
    def w(self, *a, **k):
        if not Cap.active:
            return orig(self, *a, **k)
        with rf(label):
            return orig(self, *a, **k)
    setattr(cls, attr, w)
    hooked.append(f"{cls.__name__}.{attr} (class)")


def install_hooks(gen, job_cls, sampler_cls, gdn_state_cls) -> list[str]:
    hooked = []
    draft, target = gen.draft_model, gen.model
    orig_iterate = gen.iterate

    def iterate():
        c = Cap.case
        if not Cap.armed or c is None:
            return orig_iterate()
        decode = bool(gen.active_jobs) and not gen.pending_jobs and all(j.is_prefill_done() for j in gen.active_jobs)
        if decode:
            c["decode_idx"] += 1
        idx = c["decode_idx"]
        start = c["preroll"]
        if decode and idx == start and c["prof"] is None and not c["done"]:
            prof = torch.profiler.profile(
                activities=[torch.profiler.ProfilerActivity.CPU, torch.profiler.ProfilerActivity.CUDA],
                record_shapes=False, with_stack=False, profile_memory=False, with_flops=False)
            prof.start()
            c["prof"] = prof
            Cap.active = True
        t0 = perf()
        if Cap.active:
            with rf(f"kt:round:{idx}"):
                y = orig_iterate()
        else:
            y = orig_iterate()
        wall = perf() - t0
        if decode:
            c["walls"].append((idx, Cap.active, wall))
        if Cap.active and idx == start + MEASURED_ROUNDS:
            torch.cuda.synchronize()
            Cap.active = False
            c["prof"].stop()
            c["done"] = True
        return y

    gen.iterate = iterate
    hooked.append("Generator.iterate")

    wrap_inst(gen, "recurrent_checkpoint", lambda: "kt:ph:ckpt", hooked, "Generator.recurrent_checkpoint")
    wrap_inst(gen, "iterate_draftmodel_dflash_gen", lambda: "kt:ph:draft", hooked, "Generator.iterate_draftmodel_dflash_gen")
    wrap_inst(gen, "iterate_gen", lambda: "kt:ph:gen", hooked, "Generator.iterate_gen")
    wrap_inst(gen, "greedy_accept", lambda: "kt:ph:accept", hooked, "Generator.greedy_accept")
    wrap_inst(draft, "forward", lambda: "kt:ph:draft_forward", hooked, "draft_model.forward")
    wrap_inst(draft, "sample_from_state", lambda: "kt:ph:draft_sample", hooked, "draft_model.sample_from_state")
    wrap_inst(draft, "update_kv_from_target", lambda: "kt:ph:draft_kv_refresh", hooked, "draft_model.update_kv_from_target")
    wrap_inst(target, "forward", lambda: "kt:ph:verify_forward", hooked, "model.forward (target)")
    wrap_cls(sampler_cls, "forward", "kt:ph:sampler", hooked)
    wrap_cls(gdn_state_cls, "rewind", "kt:ph:rewind", hooked)
    wrap_cls(job_cls, "prefill", "kt:ph:prefill", hooked)
    hooked += install_module_hooks(target, "kt:mod")
    hooked += install_module_hooks(draft, "kt:dmod")
    return hooked


def module_kind(m, attn=False) -> str:
    n = type(m).__name__
    if attn:
        return "gdn" if ("Delta" in n or "GDN" in n) else "attn"
    return n


def install_module_hooks(model, prefix) -> list[str]:
    """Wrap per-module forwards; label = prefix:kind:L<block index>."""
    labels = collections.Counter()

    def wrap(mod, label):
        orig = mod.forward
        def fwd(*a, **k):
            if not Cap.active:
                return orig(*a, **k)
            with rf(label):
                return orig(*a, **k)
        mod.forward = fwd
        labels[label.rsplit(":L", 1)[0]] += 1

    li = 0
    for m in model.modules:
        attn = getattr(m, "attn", None)
        mlp = getattr(m, "mlp", None)
        if attn is not None or mlp is not None:
            wrap(m, f"{prefix}:block:L{li}")
            if attn is not None:
                wrap(attn, f"{prefix}:{module_kind(attn, True)}:L{li}")
            if mlp is not None:
                wrap(mlp, f"{prefix}:mlp:L{li}")
            li += 1
        elif m.caps.get("logits_output"):
            wrap(m, f"{prefix}:lm_head")
        else:
            wrap(m, f"{prefix}:top.{type(m).__name__}")
    return [f"{k} x{v}" for k, v in sorted(labels.items())]


# --------------------------------------------------------------------------------------------
# Trace analysis (pure Python on the Chrome trace JSON; exercised by --check on a synthetic trace)

def short_name(name: str) -> str:
    s = re.sub(r"^void\s+", "", name.strip())
    m = re.match(r"([A-Za-z_][\w:]*)", s)
    return m.group(1) if m else s[:80]


class Ranges:
    """Innermost-containing lookup over record_function ranges of one kind."""

    def __init__(self, items):
        self.items = sorted(items, key=lambda x: (x[0], -x[1]))
        self.starts = [x[0] for x in self.items]

    def find(self, ts):
        i = bisect.bisect_right(self.starts, ts) - 1
        while i >= 0:
            s, e, label, uid = self.items[i]
            if s <= ts <= e:
                return label, uid
            i -= 1
        return None, None


def classify(cat, name, ph, mod, dmod) -> str:
    lname = name.lower()
    if cat in ("gpu_memcpy", "gpu_memset"):
        return "memcpy"
    if "rewind" in lname or "replay" in lname:
        return "rewind_replay"
    phase = ph.split(":", 2)[2] if ph else None
    kind = mod.split(":")[2].split(".")[0] if mod else None
    gemm = bool(GEMM_RE.search(name))
    if phase == "draft_sample":
        if (mod and kind == "lm_head") or gemm:
            return "draft_sample_head"
        if "topk" in lname:
            return "draft_sample_topk"
        if "walk" in lname:
            return "draft_sample_walk"
        return "draft_sample_other"
    if phase in ("draft_forward", "draft_kv_refresh", "sampler", "accept", "ckpt", "prefill"):
        return phase
    if phase == "rewind":
        return "rewind_replay"
    if phase == "draft":
        return "draft_other"
    if phase == "gen":
        return "gen_other"
    if phase == "verify_forward":
        if kind == "mlp":
            return "target_mlp_gemm" if gemm else "target_mlp_other"
        if kind == "gdn":
            return "gdn_gemm" if gemm else "gdn_small"
        if kind == "attn":
            if gemm:
                return "attn_proj_gemm"
            if "split" in lname:
                return "attn_split"
            if "combine" in lname:
                return "attn_combine"
            return "attn_other"
        if kind == "block":
            return "norms_residual"
        if kind == "lm_head":
            return "lm_head"
        if kind == "top" and mod and "embed" in mod.lower():
            return "target_embed"
        if kind == "top":
            return "norms_residual"
        return "target_other"
    return "other"


def gemm_projection(bucket: str, mod: str | None, name: str, ordinal: int, n_in_call: int) -> str | None:
    """Byte-table key for a weight GEMM kernel; None when the mapping is ambiguous."""
    lname = name.lower()
    if bucket == "target_mlp_gemm":
        if n_in_call == 3:
            return ("mlp.gate", "mlp.up", "mlp.down")[ordinal]
        if n_in_call == 2:
            return ("mlp.gate+up", "mlp.down")[ordinal]
        return None
    if bucket == "gdn_gemm":
        if "ba_gemv" in lname:
            return "gdn.ba"
        if "mgemm" in lname:
            return "gdn.qkv+z"
        return "gdn.out"
    if bucket == "attn_proj_gemm":
        return "attn.qkv" if "mgemm" in lname else "attn.o"
    if bucket in ("lm_head", "draft_sample_head"):
        return "lm_head"
    return None


def proj_bytes(table: dict, key: str, layer: int | None) -> int:
    if key == "lm_head":
        return table["lm_head"]
    L = table["target_layers"][layer]
    return sum(L[k] for k in {"gdn.qkv+z": ["gdn.qkv", "gdn.z"], "mlp.gate+up": ["mlp.gate", "mlp.up"]}.get(key, [key]))


def interval_stats(acts: list[dict], launch_ts: dict) -> dict:
    """Busy/idle on the union of activity intervals, gap census (sorted by start)."""
    acts = sorted(acts, key=lambda a: a["ts"])
    if not acts:
        return {"n": 0}
    busy = 0.0
    cur_s, cur_e = acts[0]["ts"], acts[0]["ts"] + acts[0]["dur"]
    gaps = []  # (gap_us, host_late)
    overlaps = 0
    for a in acts[1:]:
        s, e = a["ts"], a["ts"] + a["dur"]
        if s > cur_e:
            busy += cur_e - cur_s
            lt = launch_ts.get(a["corr"])
            gaps.append((s - cur_e, lt is not None and lt > cur_e))
            cur_s, cur_e = s, e
        else:
            overlaps += 1
            cur_e = max(cur_e, e)
    busy += cur_e - cur_s
    window = cur_e - acts[0]["ts"]
    small = [g for g in gaps if g[0] < GAP_SMALL_US]
    hist = []
    for lo, hi in zip(GAP_BINS_US, GAP_BINS_US[1:]):
        sel = [g for g, _ in gaps if lo <= g < hi]
        hist.append({"range_us": [lo, None if hi == float("inf") else hi], "n": len(sel), "total_us": round(sum(sel), 3)})
    return {
        "n": len(acts),
        "first_ts": acts[0]["ts"], "last_end": cur_e,
        "window_us": round(window, 3), "busy_us": round(busy, 3), "idle_us": round(window - busy, 3),
        "n_gaps": len(gaps), "overlapping_or_touching": overlaps,
        "gaps_lt10": {"n": len(small), "total_us": round(sum(g for g, _ in small), 3),
                      "gpu_side_n": sum(1 for _, h in small if not h),
                      "gpu_side_us": round(sum(g for g, h in small if not h), 3),
                      "host_late_n": sum(1 for _, h in small if h),
                      "host_late_us": round(sum(g for g, h in small if h), 3)},
        "gaps_ge10": {"n": len(gaps) - len(small), "total_us": round(sum(g for g, _ in gaps if g >= GAP_SMALL_US), 3),
                      "host_late_us": round(sum(g for g, h in gaps if g >= GAP_SMALL_US and h), 3)},
        "gap_hist": hist,
    }


def analyze(trace: dict, table: dict | None, measured: list[int]) -> dict:
    ev = trace["traceEvents"] if isinstance(trace, dict) else trace
    rng = {"round": [], "ph": [], "mod": [], "dmod": []}
    launches = {}  # corr -> (ts, name)
    gpu = []
    for i, e in enumerate(ev):
        if e.get("ph") != "X":
            continue
        cat, name = e.get("cat", ""), e.get("name", "")
        if cat == "user_annotation" and name.startswith("kt:"):
            kind = name.split(":")[1]
            if kind in rng:
                rng[kind].append((float(e["ts"]), float(e["ts"]) + float(e.get("dur", 0)), name, i))
        elif cat in LAUNCH_CATS:
            c = (e.get("args") or {}).get("correlation")
            if c is not None:
                launches[c] = (float(e["ts"]), name)
        elif cat in GPU_CATS:
            c = (e.get("args") or {}).get("correlation")
            gpu.append({"cat": cat, "name": name, "ts": float(e["ts"]), "dur": float(e.get("dur", 0)), "corr": c,
                        "args": e.get("args") or {}})
    R = {k: Ranges(v) for k, v in rng.items()}
    graph_api = sum(1 for _, n in launches.values() if "GraphLaunch" in n)
    unlinked = 0
    for a in gpu:
        lt = launches.get(a["corr"])
        a["launch"] = lt[1] if lt else None
        a["graph"] = bool(lt and "GraphLaunch" in lt[1])
        if lt is None:
            unlinked += 1
            a["round"] = a["ph"] = a["mod"] = a["dmod"] = None
            a["mod_uid"] = None
        else:
            ts = lt[0]
            rl, _ = R["round"].find(ts)
            a["round"] = int(rl.split(":")[2]) if rl else None
            a["ph"], _ = R["ph"].find(ts)
            a["mod"], a["mod_uid"] = R["mod"].find(ts)
            a["dmod"], _ = R["dmod"].find(ts)
        a["bucket"] = classify(a["cat"], a["name"], a["ph"], a["mod"], a["dmod"])
    launch_ts = {c: v[0] for c, v in launches.items()}

    meas = [a for a in gpu if a["round"] in measured]
    kern = [a for a in meas if a["cat"] == "kernel"]
    nR = len(measured)
    out = {
        "measured_rounds": measured,
        "graph": {
            "graph_launch_api_calls": graph_api,
            "kernels_from_graphs": sum(1 for a in gpu if a["cat"] == "kernel" and a["graph"]),
            "kernels_total": sum(1 for a in gpu if a["cat"] == "kernel"),
            "graph_arg_keys": sorted({k for a in gpu for k in a["args"] if "graph" in k.lower()}),
        },
        "attribution": {
            "gpu_activities": len(gpu), "unlinked_no_launch_api": unlinked,
            "outside_any_round": sum(1 for a in gpu if a["round"] is None),
            "measured_without_phase": sum(1 for a in meas if a["ph"] is None),
        },
    }
    g = out["graph"]
    g["graph_kernels_visible"] = g["graph_launch_api_calls"] == 0 or g["kernels_from_graphs"] > 0

    # Per round
    rounds = []
    by_round = collections.defaultdict(list)
    for a in gpu:
        if a["round"] is not None:
            by_round[a["round"]].append(a)
    prev_end = None
    for r in sorted(by_round):
        st = interval_stats(by_round[r], launch_ts)
        rk = [a for a in by_round[r] if a["cat"] == "kernel"]
        row = {"round": r, "measured": r in measured, "kernels": len(rk),
               "graph_kernels": sum(1 for a in rk if a["graph"]),
               "memcpy_memset": len(by_round[r]) - len(rk), **st,
               "lead_gap_us": round(st["first_ts"] - prev_end, 3) if prev_end is not None else None}
        verify = [a for a in by_round[r] if a["ph"] == "kt:ph:verify_forward"]
        row["verify_forward"] = {k: v for k, v in interval_stats(verify, launch_ts).items() if k not in ("gap_hist",)}
        row["phases_seen"] = sorted({a["ph"] for a in by_round[r] if a["ph"]})
        prev_end = st["last_end"]
        rounds.append(row)
    out["rounds"] = rounds

    # Per kernel name
    per = {}
    for a in meas:
        k = a["name"] if a["cat"] == "kernel" else f"[{a['cat']}] {a['name']}"
        p = per.setdefault(k, {"name": k, "short": short_name(a["name"]), "cat": a["cat"], "count": 0, "total_us": 0.0,
                               "buckets": collections.Counter()})
        p["count"] += 1
        p["total_us"] += a["dur"]
        p["buckets"][a["bucket"]] += 1
    kl = sorted(per.values(), key=lambda p: -p["total_us"])
    for p in kl:
        p["mean_us"] = round(p["total_us"] / p["count"], 3)
        p["total_us"] = round(p["total_us"], 3)
        p["per_round_us"] = round(p["total_us"] / nR, 3)
        p["per_round_count"] = round(p["count"] / nR, 3)
        p["buckets"] = dict(p["buckets"])
    out["per_kernel"] = kl
    shorts = {}
    for a in meas:
        s = shorts.setdefault(short_name(a["name"]), {"count": 0, "total_us": 0.0})
        s["count"] += 1
        s["total_us"] += a["dur"]
    out["per_kernel_short"] = {k: {"count": v["count"], "total_us": round(v["total_us"], 3),
                                   "mean_us": round(v["total_us"] / v["count"], 3),
                                   "per_round_us": round(v["total_us"] / nR, 3)}
                               for k, v in sorted(shorts.items(), key=lambda kv: -kv[1]["total_us"])}

    # Buckets
    bk = {b: {"count": 0, "total_us": 0.0} for b in BUCKETS}
    for a in meas:
        bk[a["bucket"]]["count"] += 1
        bk[a["bucket"]]["total_us"] += a["dur"]
    out["buckets"] = {b: {"per_round_count": round(v["count"] / nR, 2), "per_round_us": round(v["total_us"] / nR, 3),
                          "total_us": round(v["total_us"], 3)} for b, v in bk.items() if v["count"]}

    # Achieved GB/s of weight GEMMs
    out["gemm_bandwidth"] = gemm_bandwidth(meas, table, nR) if table else None
    # Kernel-boundary census over measured rounds (sum of per-round figures)
    mr = [r for r in rounds if r["measured"]]
    out["boundary_gaps"] = {
        "per_round_mean": {
            "gaps_lt10_n": round(sum(r["gaps_lt10"]["n"] for r in mr) / max(len(mr), 1), 2),
            "gaps_lt10_us": round(sum(r["gaps_lt10"]["total_us"] for r in mr) / max(len(mr), 1), 3),
            "gaps_lt10_gpu_side_us": round(sum(r["gaps_lt10"]["gpu_side_us"] for r in mr) / max(len(mr), 1), 3),
            "gaps_lt10_host_late_us": round(sum(r["gaps_lt10"]["host_late_us"] for r in mr) / max(len(mr), 1), 3),
            "gaps_ge10_n": round(sum(r["gaps_ge10"]["n"] for r in mr) / max(len(mr), 1), 2),
            "gaps_ge10_us": round(sum(r["gaps_ge10"]["total_us"] for r in mr) / max(len(mr), 1), 3),
            "verify_gaps_lt10_n": round(sum(r["verify_forward"].get("gaps_lt10", {}).get("n", 0) for r in mr) / max(len(mr), 1), 2),
            "verify_gaps_lt10_us": round(sum(r["verify_forward"].get("gaps_lt10", {}).get("total_us", 0) for r in mr) / max(len(mr), 1), 3),
        },
        "note": "gaps between consecutive activities on the union timeline; kernel ramp/tail inside durations is not visible here",
    }
    return out


def gemm_bandwidth(meas, table, nR) -> dict:
    calls = collections.defaultdict(list)
    for a in meas:
        if a["cat"] == "kernel" and a["bucket"] in ("target_mlp_gemm", "gdn_gemm", "attn_proj_gemm", "lm_head",
                                                    "draft_sample_head", "draft_forward"):
            calls[(a["bucket"], a["mod_uid"] if a["bucket"] != "draft_forward" else a["round"])].append(a)
    proj = collections.defaultdict(lambda: {"bytes": 0, "us": 0.0, "kernels": 0})
    unmapped = collections.Counter()
    draft = {"us": 0.0, "kernels": 0, "forwards": 0}
    for (bucket, _), ks in calls.items():
        if bucket == "draft_forward":
            gk = [a for a in ks if GEMM_RE.search(a["name"])]
            draft["us"] += sum(a["dur"] for a in gk)
            draft["kernels"] += len(gk)
            draft["forwards"] += 1
            continue
        ks.sort(key=lambda a: a["ts"])
        for i, a in enumerate(ks):
            if not GEMM_RE.search(a["name"]) and bucket in ("lm_head", "draft_sample_head"):
                unmapped[f"{bucket}:non-gemm:{short_name(a['name'])}"] += 1
                continue
            key = gemm_projection(bucket, a["mod"], a["name"], i, len(ks))
            if key is None:
                unmapped[f"{bucket}:{short_name(a['name'])}:n{len(ks)}"] += 1
                continue
            layer = int(a["mod"].rsplit(":L", 1)[1]) if a["mod"] and ":L" in a["mod"] else None
            pk = f"{'draft_sample.' if bucket == 'draft_sample_head' else ''}{key}"
            proj[pk]["bytes"] += proj_bytes(table, key, layer)
            proj[pk]["us"] += a["dur"]
            proj[pk]["kernels"] += 1
    out = {}
    groups = {"target_mlp": ("mlp.",), "target_gdn_proj": ("gdn.",), "target_attn_proj": ("attn.",),
              "target_lm_head": ("lm_head",), "draft_sample_lm_head": ("draft_sample.lm_head",)}
    for gname, prefixes in groups.items():
        sel = [v for k, v in proj.items() if k.startswith(prefixes)]
        b, us = sum(v["bytes"] for v in sel), sum(v["us"] for v in sel)
        if us:
            out[gname] = {"bytes_per_round": b // nR, "gemm_us_per_round": round(us / nR, 3),
                          "GBps": round(b / us / 1e3, 1), "pct_of_936": round(100 * b / us / 1e3 / PEAK_GBS, 1),
                          "floor_us_per_round": round(b / nR / PEAK_GBS / 1e3, 3)}
    tw = [v for k, v in proj.items() if not k.startswith("draft_sample.")]
    b, us = sum(v["bytes"] for v in tw), sum(v["us"] for v in tw)
    if us:
        out["target_all_weight_gemms"] = {"bytes_per_round": b // nR, "gemm_us_per_round": round(us / nR, 3),
                                          "GBps": round(b / us / 1e3, 1), "pct_of_936": round(100 * b / us / 1e3 / PEAK_GBS, 1),
                                          "floor_us_per_round": round(b / nR / PEAK_GBS / 1e3, 3)}
    out["per_projection"] = {k: {"kernels_per_round": round(v["kernels"] / nR, 2), "bytes_per_kernel": v["bytes"] // max(v["kernels"], 1),
                                 "us_per_kernel": round(v["us"] / max(v["kernels"], 1), 3),
                                 "GBps": round(v["bytes"] / v["us"] / 1e3, 1) if v["us"] else None,
                                 "pct_of_936": round(100 * v["bytes"] / v["us"] / 1e3 / PEAK_GBS, 1) if v["us"] else None}
                             for k, v in sorted(proj.items())}
    if draft["forwards"]:
        b = table["draft_forward_linears"] * draft["forwards"]
        out["draft_forward_linears"] = {"forwards": draft["forwards"], "gemm_kernels_per_forward": draft["kernels"] / draft["forwards"],
                                        "bytes_per_forward": table["draft_forward_linears"],
                                        "gemm_us_per_forward": round(draft["us"] / draft["forwards"], 3),
                                        "GBps": round(b / draft["us"] / 1e3, 1) if draft["us"] else None}
    out["unmapped_gemm_kernels"] = dict(unmapped)
    return out


# --------------------------------------------------------------------------------------------
# Workloads (identical to profile_round.py)

def records_prompt(server, s, target_tokens: int, seed: int):
    rng = random.Random(seed)
    lines = []
    for i in range(20000):
        lines.append(
            f"Record {seed:02d}-{i:05d}: shipment {rng.choice('KXQZMBTR')}{rng.choice('ABCDEFGH')}-"
            f"{rng.randrange(10000, 99999)} of {rng.choice(GOODS)} via carrier {rng.choice(CARRIERS)}, "
            f"{rng.randrange(3, 900)} pallets, held {rng.randrange(0, 12)} days at port {rng.choice(PORTS)}."
        )
    head = f"Archive {seed:02d} ({hashlib.sha256(str(seed).encode()).hexdigest()[:12]}). "

    def render(n):
        body = {"messages": [{"role": "user", "content": head + "\n".join(lines[:n]) +
                              "\nQuestion: which carriers had the longest holds, and at which ports? "
                              "Answer with a short analysis."}],
                "chat_template_kwargs": {"enable_thinking": False}}
        return server.render_chat(s.parse_chat(body))

    n = 64
    ids = render(n)
    for _ in range(4):
        per = (ids.shape[-1] - render(1).shape[-1]) / max(n - 1, 1)
        n = max(1, int(n + (target_tokens - ids.shape[-1]) / per))
        ids = render(n)
    while ids.shape[-1] > target_tokens and n > 1:
        n -= 1
        ids = render(n)
    return ids


def load_engine():
    global torch
    import torch as _torch
    torch = _torch
    sys.path.insert(0, "/opt/qwen/serve")
    import exl3_server as s
    from exllamav3 import Job, Generator, Model
    from exllamav3.generator.sampler.custom import CustomSampler
    from exllamav3.generator.sampler.presets import ArgmaxSampler
    from exllamav3.modules.gated_delta_net import GDNState
    return s, Job, Generator, Model, CustomSampler, ArgmaxSampler, GDNState


def run_case(server, s, name, ids, max_tokens, preroll, created, out_dir: Path, table) -> dict:
    c = {"decode_idx": 0, "preroll": preroll, "prof": None, "done": False, "walls": []}
    Cap.case = c
    Cap.armed = True
    t0 = time.monotonic()
    try:
        result = server.submit(ids, s.Options(max_tokens, False, False, True))
    finally:
        Cap.armed = False
        Cap.case = None
        if c["prof"] is not None and not c["done"]:
            Cap.active = False
            torch.cuda.synchronize()
            c["prof"].stop()
    wall = time.monotonic() - t0
    torch.cuda.synchronize()
    if not c["done"]:
        raise RuntimeError(f"{name}: capture incomplete (decode rounds={c['decode_idx']}, need {preroll + MEASURED_ROUNDS})")
    job = created[-1]
    trace_path = out_dir / f"trace-{name}.json"
    c["prof"].export_chrome_trace(str(trace_path))
    measured = list(range(preroll + 1, preroll + 1 + MEASURED_ROUNDS))
    rec = analyze(json.loads(trace_path.read_text()), table, measured)
    got = {r["round"]: r for r in rec["rounds"]}
    bad = [r for r in measured if r not in got or got[r]["kernels"] == 0
           or "kt:ph:verify_forward" not in got[r]["phases_seen"] or "kt:ph:draft_forward" not in got[r]["phases_seen"]]
    if bad:
        raise RuntimeError(f"{name}: measured rounds {bad} have no CUPTI kernels or lack draft/verify phases "
                           f"(trace {trace_path}; attribution {rec['attribution']})")
    prof_w = [w for i, a, w in c["walls"] if i in measured]
    base_w = [w for i, a, w in c["walls"] if not a and (i < preroll or i > preroll + MEASURED_ROUNDS + 2)]
    rec.update({
        "name": name, "prompt_tokens": result.prompt_tokens, "completion_tokens": result.completion_tokens,
        "finish_reason": result.finish_reason, "exl3_spec": result.usage()["exl3_spec"],
        "engine_decode_tok_s": round(result.completion_tokens / job.time_generate, 3) if job.time_generate else None,
        "submit_wall_s": round(wall, 3), "trace_file": trace_path.name,
        "round_wall_ms": {"profiled": [round(w * 1e3, 3) for w in prof_w],
                          "unprofiled_median": round(statistics.median(base_w) * 1e3, 3) if base_w else None,
                          "unprofiled_n": len(base_w)},
    })
    print(f"{name}: prompt={rec['prompt_tokens']} gen={rec['completion_tokens']} decode={rec['engine_decode_tok_s']} tok/s "
          f"captured rounds {measured} wall={wall:.1f}s", flush=True)
    return rec


def print_case(c: dict) -> None:
    print(f"\n== {c['name']}  prompt={c['prompt_tokens']}  graph: {json.dumps(c['graph'])}")
    print(f"attribution: {json.dumps(c['attribution'])}")
    print(f"round wall ms profiled={c['round_wall_ms']['profiled']} unprofiled median={c['round_wall_ms']['unprofiled_median']}")
    print(f"{'round':>5s} {'meas':>4s} {'kern':>5s} {'graph':>5s} {'window_ms':>9s} {'busy_ms':>8s} {'idle_ms':>8s} "
          f"{'lead_ms':>8s} {'g<10 n':>6s} {'g<10 us':>8s} {'gpu-side':>8s} {'host-late':>9s} {'g>=10 n':>7s} {'g>=10 us':>8s} {'verify_ms':>9s}")
    for r in c["rounds"]:
        v = r["verify_forward"]
        print(f"{r['round']:5d} {str(r['measured'])[0]:>4s} {r['kernels']:5d} {r['graph_kernels']:5d} {r['window_us'] / 1e3:9.3f} "
              f"{r['busy_us'] / 1e3:8.3f} {r['idle_us'] / 1e3:8.3f} "
              f"{'' if r['lead_gap_us'] is None else format(r['lead_gap_us'] / 1e3, '8.3f'):>8s} "
              f"{r['gaps_lt10']['n']:6d} {r['gaps_lt10']['total_us']:8.1f} {r['gaps_lt10']['gpu_side_us']:8.1f} "
              f"{r['gaps_lt10']['host_late_us']:9.1f} {r['gaps_ge10']['n']:7d} {r['gaps_ge10']['total_us']:8.1f} "
              f"{v.get('window_us', 0) / 1e3:9.3f}")
    print(f"{'bucket':22s} {'n/round':>8s} {'ms/round':>9s}")
    for b, v in c["buckets"].items():
        print(f"{b:22s} {v['per_round_count']:8.1f} {v['per_round_us'] / 1e3:9.3f}")
    gb = c.get("gemm_bandwidth") or {}
    print(f"{'weight GEMM group':26s} {'MB/round':>9s} {'ms/round':>9s} {'floor_ms':>9s} {'GB/s':>7s} {'%936':>6s}")
    for k, v in gb.items():
        if isinstance(v, dict) and "GBps" in v and "bytes_per_round" in v:
            print(f"{k:26s} {v['bytes_per_round'] / 1e6:9.1f} {v['gemm_us_per_round'] / 1e3:9.3f} "
                  f"{v['floor_us_per_round'] / 1e3:9.3f} {v['GBps']:7.1f} {v['pct_of_936']:6.1f}")
    for k, v in (gb.get("per_projection") or {}).items():
        print(f"  {k:24s} n/round={v['kernels_per_round']:6.1f} {v['us_per_kernel']:8.2f} us/kernel {v['GBps']} GB/s ({v['pct_of_936']}%)")
    if gb.get("draft_forward_linears"):
        print(f"  draft forward linears: {json.dumps(gb['draft_forward_linears'])}")
    if gb.get("unmapped_gemm_kernels"):
        print(f"  unmapped GEMM kernels: {json.dumps(gb['unmapped_gemm_kernels'])}")
    print(f"boundary gaps: {json.dumps(c['boundary_gaps']['per_round_mean'])}")
    print(f"{'kernel (short)':48s} {'count':>6s} {'total_us':>10s} {'mean_us':>8s} {'us/round':>9s}")
    for k, v in list(c["per_kernel_short"].items())[:30]:
        print(f"{k[:48]:48s} {v['count']:6d} {v['total_us']:10.1f} {v['mean_us']:8.2f} {v['per_round_us']:9.1f}")


def produce(out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    table = build_byte_table()
    s, Job, Generator, Model, CustomSampler, ArgmaxSampler, GDNState = load_engine()
    args = argparse.Namespace(target=TARGET_DIR, draft=DRAFT_DIR, model_name="qwen3.8-27b",
                              max_model_len=262144, cache_tokens=270336, cq=3)
    server = s.Server(args)
    if not server.gen.dflash_draft or server.gen.draft_calibrator is not None:
        raise RuntimeError("Expected fixed-window DFlash drafting")
    created = []
    job_type = server.job_type
    def recording_job(**kwargs):
        job = job_type(**kwargs)
        created.append(job)
        return job
    server.job_type = recording_job

    think = {"chat_template_kwargs": {"enable_thinking": True}}
    prompts = {
        "aime": server.render_chat(s.parse_chat({"messages": [{"role": "user", "content": AIME}], **think})),
        "ctx8": records_prompt(server, s, 8192, 8),
        "ctx32": records_prompt(server, s, 32768, 32),
    }
    warm_ids = server.render_chat(s.parse_chat({"messages": [{"role": "user", "content":
        "Explain in detail how a B-tree handles insertion and node splits."}],
        "chat_template_kwargs": {"enable_thinking": False}}))
    server.submit(warm_ids, s.Options(256, False, False, True))
    # CUPTI/kineto one-time init outside any measured window
    with torch.profiler.profile(activities=[torch.profiler.ProfilerActivity.CPU, torch.profiler.ProfilerActivity.CUDA]):
        (torch.ones(1024, device="cuda") * 2).sum().item()
    hooked = install_hooks(server.gen, Job, CustomSampler, GDNState)

    cases = []
    for name, kind, max_tokens, preroll in CASES:
        cases.append(run_case(server, s, name, prompts[kind], max_tokens, preroll, created, out_dir, table))
    payload = {"doc": __doc__, "hooked": hooked, "byte_table": {k: v for k, v in table.items() if k != "target_layers"},
               "variant": "candidate" if server.verified_acceptance else "baseline", "cases": cases}
    path = out_dir / "kernel-trace.json"
    path.write_text(json.dumps(payload, indent=1))
    for c in cases:
        print_case(c)
    missing = [c["name"] for c in cases if not c["graph"]["graph_kernels_visible"]]
    if missing:
        print(f"WARNING: CUDA graph launches seen but NO graph-launched kernels in the trace for {missing}")
    else:
        print("\nCUDA graph kernels visible in CUPTI trace: " +
              ", ".join(f"{c['name']}={c['graph']['kernels_from_graphs']}/{c['graph']['kernels_total']} "
                        f"(graph launches {c['graph']['graph_launch_api_calls']})" for c in cases))
    print(f"wrote {path}")


# --------------------------------------------------------------------------------------------
# --check (CPU only)

def synthetic_trace() -> tuple[dict, list[int]]:
    """Two rounds: round 1 pre-roll, round 2 measured; one graph-launched MLP (3 GEMMs + silu),
    one GDN graph, an attention split/combine, a draft sample head/topk/walk, a memcpy, a replay."""
    E = []
    def X(cat, name, ts, dur, **args):
        E.append({"ph": "X", "cat": cat, "name": name, "ts": ts, "dur": dur, "pid": 0, "tid": 1, "args": args})
    corr = [100]
    def launch(api, ts, kernels):
        corr[0] += 1
        c = corr[0]
        X("cuda_runtime", api, ts, 2.0, correlation = c)
        for (name, s, d, cat) in kernels:
            X(cat, name, s, d, correlation = c)
    for r, base in ((1, 0.0), (2, 1000.0)):
        X("user_annotation", f"kt:round:{r}", base, 900.0)
        X("user_annotation", "kt:ph:draft", base + 1, 100.0)
        X("user_annotation", "kt:ph:draft_sample", base + 2, 50.0)
        X("user_annotation", "kt:mod:lm_head", base + 3, 10.0)
        launch("cudaLaunchKernel", base + 4, [("void exl3_gemm_kernel<4>(half*)", base + 10, 100.0, "kernel")])
        launch("cuLaunchKernel", base + 20, [("dflash2_topk_kernel", base + 112, 20.0, "kernel")])
        launch("cudaLaunchKernel", base + 21, [("dflash2_selector_walk_kernel", base + 133, 30.0, "kernel")])
        launch("cudaMemcpyAsync", base + 22, [("Memcpy DtoH (Device -> Pinned)", base + 170, 5.0, "gpu_memcpy")])
        X("user_annotation", "kt:ph:gen", base + 200, 600.0)
        X("user_annotation", "kt:ph:verify_forward", base + 201, 300.0)
        X("user_annotation", "kt:mod:block:L0", base + 202, 35.0)
        X("user_annotation", "kt:mod:gdn:L0", base + 203, 10.0)
        launch("cudaGraphLaunch", base + 204, [("void exl3_mgemm_kernel<4>()", base + 300, 40.0, "kernel"),
                                              ("gdn_ba_gemv_kernel", base + 342, 5.0, "kernel"),
                                              ("gated_rms_norm_kernel<32>", base + 347, 3.0, "kernel"),
                                              ("void exl3_gemm_kernel<4>(half*)", base + 351, 20.0, "kernel")])
        X("user_annotation", "kt:mod:mlp:L0", base + 215, 10.0)
        launch("cudaGraphLaunch", base + 216, [("void exl3_gemm_kernel<4>(half*)", base + 380, 50.0, "kernel"),
                                              ("void exl3_gemm_kernel<4>(half*)", base + 432, 50.0, "kernel"),
                                              ("silu_mul_kernel", base + 490, 4.0, "kernel"),
                                              ("void exl3_gemm_kernel<4>(half*)", base + 495, 50.0, "kernel")])
        launch("cudaLaunchKernel", base + 230, [("rms_norm_kernel", base + 546, 2.0, "kernel")])
        X("user_annotation", "kt:mod:block:L3", base + 240, 20.0)
        X("user_annotation", "kt:mod:attn:L3", base + 241, 10.0)
        launch("cudaGraphLaunch", base + 242, [("_paged_attn_decode_split_kernel", base + 560, 30.0, "kernel"),
                                              ("attn_combine_kernel", base + 591, 5.0, "kernel")])
        X("user_annotation", "kt:ph:rewind", base + 600, 20.0)
        launch("cudaLaunchKernel", base + 700, [("batched_state_replay_kernel", base + 702, 30.0, "kernel")])
    return {"traceEvents": E}, [2]


def self_test(table: dict | None) -> list[str]:
    errs = []
    trace, measured = synthetic_trace()
    fake = table or {"lm_head": 1_000_000, "target_layers": [
        {"mlp.gate": 100, "mlp.up": 100, "mlp.down": 100, "gdn.qkv": 50, "gdn.z": 30, "gdn.ba": 5, "gdn.out": 30}] * 4}
    res = analyze(trace, fake, measured)
    b = res["buckets"]
    want = {"draft_sample_head": 1, "draft_sample_topk": 1, "draft_sample_walk": 1, "memcpy": 1, "gdn_gemm": 3,
            "gdn_small": 1, "target_mlp_gemm": 3, "target_mlp_other": 1, "norms_residual": 1, "attn_split": 1,
            "attn_combine": 1, "rewind_replay": 1}
    for k, n in want.items():
        if b.get(k, {}).get("per_round_count") != n:
            errs.append(f"selftest bucket {k}: {b.get(k)} != {n}")
    extra = set(b) - set(want)
    if extra:
        errs.append(f"selftest unexpected buckets {extra}")
    g = res["graph"]
    if g["kernels_from_graphs"] != 20 or g["graph_launch_api_calls"] != 6 or not g["graph_kernels_visible"]:
        errs.append(f"selftest graph {g}")
    r2 = [r for r in res["rounds"] if r["round"] == 2][0]
    if r2["kernels"] != 15 or r2["memcpy_memset"] != 1 or r2["graph_kernels"] != 10:
        errs.append(f"selftest round kernels {r2['kernels']} {r2['memcpy_memset']}")
    # union: 1010-1110,1112-1132,1133-1163,1170-1175,1300-1340,1342-1347,1347-1350(touching),1351-1371,
    # 1380-1430,1432-1482,1490-1494,1495-1545,1546-1548,1560-1590,1591-1596,1702-1732
    busy = 100 + 20 + 30 + 5 + 40 + 5 + 3 + 20 + 50 + 50 + 4 + 50 + 2 + 30 + 5 + 30
    if abs(r2["busy_us"] - busy) > 1e-6 or abs(r2["window_us"] - (1732 - 1010)) > 1e-6:
        errs.append(f"selftest busy {r2['busy_us']} != {busy} or window {r2['window_us']}")
    # gaps 2,1,7,125,2,1,9,2,8,1,1,12,1,106; all <10 gaps are gpu-side (launched early);
    # 125 (mgemm graph launched at 1204 > 1175) and 106 (replay launched at 1700 > 1596) are host-late
    small = [2, 1, 7, 2, 1, 9, 2, 8, 1, 1, 1]
    lt = r2["gaps_lt10"]
    if lt["n"] != len(small) or abs(lt["total_us"] - sum(small)) > 1e-6 or lt["host_late_n"] != 0 \
            or r2["overlapping_or_touching"] != 1:
        errs.append(f"selftest gaps_lt10 {lt} != {len(small)}/{sum(small)}")
    ge = r2["gaps_ge10"]
    if ge["n"] != 3 or abs(ge["total_us"] - 243) > 1e-6 or abs(ge["host_late_us"] - 231) > 1e-6:
        errs.append(f"selftest gaps_ge10 {ge}")
    if r2["lead_gap_us"] is None or abs(r2["lead_gap_us"] - (1010 - 732)) > 1e-6:
        errs.append(f"selftest lead gap {r2['lead_gap_us']}")
    if table is None:
        pp = res["gemm_bandwidth"]["per_projection"]
        exp = {"mlp.gate": 100, "mlp.up": 100, "mlp.down": 100, "gdn.qkv+z": 80, "gdn.ba": 5, "gdn.out": 30,
               "draft_sample.lm_head": 1_000_000}
        for k, v in exp.items():
            if pp.get(k, {}).get("bytes_per_kernel") != v:
                errs.append(f"selftest projection {k}: {pp.get(k)} != {v}")
    import contextlib
    import io
    res.update(name = "synthetic", prompt_tokens = 0, round_wall_ms = {"profiled": [0.9], "unprofiled_median": 0.9})
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            print_case(res)
    except Exception as exc:
        errs.append(f"selftest print_case: {type(exc).__name__}: {exc}")
    return errs


def check() -> None:
    missing = []
    info = {}
    s, Job, Generator, Model, CustomSampler, ArgmaxSampler, GDNState = load_engine()
    from exllamav3 import Config
    for obj, attrs in [
        (Generator, ["iterate", "recurrent_checkpoint", "iterate_draftmodel_dflash_gen", "iterate_gen",
                     "_greedy_verify_eligible"]),
        (Job, ["receive_sample", "prefill", "is_prefill_done"]),
        (CustomSampler, ["forward"]),
        (GDNState, ["rewind"]),
        # commit replay (0003/0004): batched_state_replay_kernel is bucketed by name wherever it launches
        (__import__("exllamav3.modules.gated_delta_net", fromlist = ["GDNLayerState"]).GDNLayerState,
         ["commit_pending", "replay_job", "rewind_replay_job"]),
        (Model, ["forward", "prefill"]),
        (s.Server, ["submit", "render_chat", "_worker"]),
        (s, ["parse_chat", "Options"]),
    ]:
        for a in attrs:
            if not hasattr(obj, a):
                missing.append(f"{getattr(obj, '__name__', obj)}.{a}")
    if ArgmaxSampler.forward is not CustomSampler.forward:
        missing.append("ArgmaxSampler does not inherit CustomSampler.forward")
    import inspect
    src = inspect.getsource(Generator.iterate_gen)
    for needle in ["self.greedy_accept(", "job.sampler.forward(", "self.model.forward(",
                   "self.draft_model.update_kv_from_target(", ".rewind("]:
        if needle not in src:
            missing.append(f"iterate_gen lacks {needle}")
    src = inspect.getsource(Generator.iterate_draftmodel_dflash_gen)
    for needle in ["self.draft_model.forward(", "self.draft_model.sample_from_state("]:
        if needle not in src:
            missing.append(f"dflash_gen lacks {needle}")
    if "self.greedy_accept = GreedyAccept" not in inspect.getsource(Generator.__init__):
        missing.append("Generator.__init__ lacks greedy_accept (not candidate engine?)")
    # CUPTI / kineto
    import torch.autograd
    info["torch"] = torch.__version__
    info["kineto_available"] = bool(torch.autograd.kineto_available())
    if not info["kineto_available"]:
        missing.append("kineto not available")
    site = Path(torch.__file__).parent.parent
    cupti = sorted({str(p) for pat in ("nvidia/*/lib/libcupti.so*", "nvidia/*/*/lib/libcupti.so*", "torch/lib/libcupti*.so*")
                    for p in site.glob(pat)} | set(glob.glob("/usr/local/cuda*/**/libcupti.so*", recursive = True)))
    info["libcupti"] = cupti
    if not cupti:
        missing.append("libcupti not found")
    info["supported_activities_without_gpu"] = sorted(str(a) for a in torch._C._autograd._supported_activities())
    # Byte table
    table = None
    if Path(f"{TARGET_DIR}/config.json").exists():
        table = build_byte_table()
        info["byte_table"] = {k: v for k, v in table.items() if k not in ("target_layers", "note")}
        info["byte_table"]["target_weight_gemm_floor_ms_per_forward"] = round(table["target_weight_gemm_per_forward"] / PEAK_GBS / 1e6, 3)
        info["byte_table"]["target_layer0"] = table["target_layers"][0]
        info["byte_table"]["target_layer3"] = table["target_layers"][3]
        tm = Model.from_config(Config.from_directory(TARGET_DIR))
        dm = Model.from_config(Config.from_directory(DRAFT_DIR))
        cap_state = Cap.active
        labels_t = install_module_hooks(tm, "kt:mod")
        labels_d = install_module_hooks(dm, "kt:dmod")
        Cap.active = cap_state
        info["target_module_labels"] = labels_t
        info["draft_module_labels"] = labels_d
        n_gdn = next((int(x.split(" x")[1]) for x in labels_t if x.startswith("kt:mod:gdn ")), 0)
        n_attn = next((int(x.split(" x")[1]) for x in labels_t if x.startswith("kt:mod:attn ")), 0)
        if (n_gdn, n_attn) != (table["n_gdn_layers"], table["n_attn_layers"]):
            missing.append(f"module kinds gdn/attn {n_gdn}/{n_attn} != safetensors {table['n_gdn_layers']}/{table['n_attn_layers']}")
        for i, m in enumerate(b for b in tm.modules if getattr(b, "attn", None) is not None):
            k = module_kind(m.attn, True)
            if k != table["target_layers"][i]["kind"]:
                missing.append(f"block {i}: module {k} vs safetensors {table['target_layers'][i]['kind']}")
                break
        for a in ("forward", "sample_from_state", "update_kv_from_target"):
            if not hasattr(dm, a):
                missing.append(f"draft.{a}")
    else:
        missing.append(f"{TARGET_DIR} not mounted")
    errs = self_test(None)
    if table is not None:
        errs += [e for e in self_test(table) if not e.startswith("selftest projection")]
    info["selftest"] = "ok" if not errs else errs
    missing += errs
    print(json.dumps({"missing": missing, **info}, indent = 1))
    raise SystemExit(1 if missing else 0)


if __name__ == "__main__":
    if sys.argv[1:2] == ["--check"]:
        check()
    elif len(sys.argv) == 2:
        produce(Path(sys.argv[1]))
    else:
        raise SystemExit(__doc__)
