"""Throwaway GPU harness (Invariance): is the target's greedy output independent of speculation?

Runs INSIDE a serving image in place of the server (stop the service first). Builds the real
serve/exl3_server.Server, then drives server.gen directly, one process, several draft arms:

  normal  the engine's own DFlash2 proposals
  cap     proposals kept only up to k = (3 * round) % 8 positions, the rest replaced by a wrong
          token: acceptance per round is capped by a varying k, so rounds are cut differently
  wrong0  every proposal replaced by a wrong token: each round commits exactly 1 token, i.e.
          every token is verified as row 0 of its own 8-row round
  m1      no draft at all: the generator's regular M=1 decode (its own kernel set; needs
          EXL3_TREE=0: a tree engine refuses a round without a draft). Reported as a distance with
          the logit margin at the first divergence, not required to match: the claim tested here is
          that the draft never changes the output, and m1 runs other kernels (other rounding)

Draft perturbation is done in the harness (no engine knob), on the ids the draft sampler
returns (Arms below): replaced rows get distinct valid ids from REPLACE_BASE up that differ from
every drafted id; if one happens to be the target's argmax it is simply accepted (still a valid
round cut).

Requirement: for every case, ids(normal) == ids(cap) == ids(wrong0) exactly. For every
divergent pair a probe re-runs both arms and captures, per module (Python forward calls, in
call order) and per absolute position in [P + t - 8, P + t - 1], the output row (plus the
pending deferred residual addend), and the logits top-8 at P + t - 1; the report names the
first module whose output differs between the arms at the earliest differing position, and
in which (round start, row) each arm computed it.

Subcommands:
  run   [--arms normal,cap,wrong0[,m1]] [--cases a,b] [--bench DIR --tiny 3,10] [--no-probe]
  oob   partial_o / partial_ml extent vs backing for every BC attention slot configured during
        a short warm run, and the CUDA allocator blocks (with allocation stacks) that lie in
        any out-of-bounds range

    python -I -B /work/invariance.py run --out /work/out/run-g7n
    python -I -B /work/invariance.py oob --out /work/out/oob-g7n
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import sys
import time
import traceback
import uuid

SERVER_PY = "/opt/qwen/serve/exl3_server.py"
PARITY_PY = "/parity/parity.py"
TARGET = "/models/qwen38-27b-exl3"
DRAFT = "/models/dflash2-exl3"
TRACES = "tiny-math/aime25/aime25--qwen3.8-27b--null--f4fcb374/traces.jsonl"
REQUIRED_EQUAL = ("cap", "wrong0")
REPORTED = ("m1",)  # probed when divergent (first module, logit margin), never fails the gate


def fail(msg):
    raise SystemExit(f"FAIL: {msg}")


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod  # dataclass resolution looks the module up by name
    spec.loader.exec_module(mod)
    return mod


def make_server(srv):
    # prefix_cache=None: the elpis server (9501b) reads args.prefix_cache; the gate must run without persistence
    ns = argparse.Namespace(target=TARGET, draft=DRAFT, model_name=srv.MODEL_NAME,
                            max_model_len=srv.CONTEXT, cache_tokens=srv.CACHE_TOKENS, cq=3, prefix_cache=None)
    server = srv.Server(ns)
    if getattr(server, "persist", None) is not None:
        fail("prefix-cache persistence is active; the invariance gate needs it off")
    return server


def workloads(srv, server, args):
    """(name, prompt ids [1, P], max_tokens) for the parity cases and optional tiny-math calls."""
    parity = load_module("parity", PARITY_PY)
    out = []
    want = set(args.cases.split(",")) if args.cases else None
    for name, body, max_tokens in parity.cases(False):
        if want is not None and name not in want:
            continue
        ids = server.render_chat(srv.parse_chat(body))
        out.append((name, ids if ids.ndim == 2 else ids.unsqueeze(0), max_tokens))
    if args.bench:
        by_idx = {}
        for line in open(os.path.join(args.bench, TRACES)).read().splitlines():
            o = json.loads(line)
            by_idx[o["task"]["data"]["idx"]] = o
        for idx in [int(v) for v in args.tiny.split(",") if v]:
            t = by_idx[idx]["traces"][0]
            c = t["calls"][0]
            user = t["nodes"][0]["message"]
            body = {
                "model": t["agent"]["config"]["model"],
                "messages": [{"role": user["role"], "content": user["content"]}],
                "max_tokens": c["sampling"]["max_tokens"],
                "chat_template_kwargs": t["agent"]["config"]["sampling"]["extra_body"]["chat_template_kwargs"],
            }
            ids = server.render_chat(srv.parse_chat(body))
            if ids.shape[-1] != c["usage"]["prompt_tokens"]:
                fail(f"aime{idx}: rendered {ids.shape[-1]} prompt tokens, benchmark {c['usage']['prompt_tokens']}")
            out.append((f"aime{idx}", ids if ids.ndim == 2 else ids.unsqueeze(0), body["max_tokens"]))
    if want is not None and {n for n, _, _ in out} != want:
        fail(f"unknown cases {sorted(want - {n for n, _, _ in out})}")
    return out


# ---------------------------------------------------------------- draft arms

REPLACE_BASE = 247000   # replacement ids: valid (< 248320), chosen per round to differ from every row of the record


def perturb_rows(rows, k):
    """rows: the round's drafted row tokens [anchor, d1, .., dW] (host ints). Returns the new list: rows 1..k kept,
    rows k+1..W replaced by ids that differ from every original and every other replacement, so a replaced row
    never repeats a sibling (tree record rule: children of one parent carry distinct tokens) and never equals its
    old (possibly correct) token. Row 0 (the anchor) is never touched."""
    used = set(rows)
    out = list(rows)
    cand = REPLACE_BASE
    for r in range(k + 1, len(rows)):
        while cand in used:
            cand += 1
        out[r] = cand
        used.add(cand)
        cand += 1
    return out


class Arms:
    """Perturbs the draft INSIDE draft_model.sample_from_state, i.e. on the tensor the draft sampler returns before
    iterate_draftmodel_dflash_gen copies it anywhere. On tree engines (ext 9008 + exl3 0006) that tensor is a view
    of the builder record (gen.tree_out, rows 1..7 at byte 8: generator.iterate_draftmodel_dflash_gen checks
    new_ids.data_ptr() == tree_out.data_ptr() + 8), so the record, its pinned readback and the drafted ids stay one
    and the same (the verify path requires drafted ids == record rows 1..7 and tree_round.check_output requires
    distinct sibling tokens). The forced chain (EXL3_TREE_FORCE_CHAIN=1) runs the same builder in mode 0, so the
    same hook covers it; engines without the tree get the same perturbation on their own sampler output.
      cap    rows 1..k kept, k = (3 * round) % 8, rows k+1..7 forced wrong
      wrong0 rows 1..7 forced wrong (every round commits exactly the target's own token)
      m1     no draft at all (regular decode)"""

    def __init__(self, gen):
        self.gen = gen
        self.orig_gen = gen.iterate_draftmodel_dflash_gen
        dm = gen.draft_model
        self.orig_sample = dm.sample_from_state
        self.arm = "normal"
        self.round = 0
        self.rewritten = 0
        gen.iterate_draftmodel_dflash_gen = self.wrapped_gen
        dm.sample_from_state = self.wrapped_sample

    def wrapped_gen(self, results):
        if self.arm == "m1":
            return None
        return self.orig_gen(results)

    def wrapped_sample(self, *a, **kw):
        new_ids = self.orig_sample(*a, **kw)
        if self.arm not in ("cap", "wrong0"):
            return new_ids
        import torch
        window = new_ids.shape[-1] - 1
        k = (3 * self.round) % (window + 1) if self.arm == "cap" else 0
        self.round += 1
        if k >= window:
            return new_ids
        if new_ids.is_cuda:
            torch.cuda.current_stream(new_ids.device).synchronize()
        rows = [int(v) for v in new_ids[0].cpu().tolist()]
        out = perturb_rows(rows, k)
        new_ids[0].copy_(torch.tensor(out, dtype=new_ids.dtype), non_blocking=False)
        self.rewritten += 1
        return new_ids


# ---------------------------------------------------------------- per-module capture (probe)

class Capture:
    """Wraps every target module's forward; while armed, stores output rows at chosen positions."""

    def __init__(self, model):
        self.positions = set()
        self.rows = {}      # position -> {module key: (call index, tensor)}; last write wins
        self.where = {}     # position -> (round start, row)
        self.enabled = False
        self.calls = 0
        self.mods = []
        for m in model:
            orig = m.forward
            key = getattr(m, "key", None) or type(m).__name__
            m.forward = self._wrap(m, key, orig)
            self.mods.append((m, orig))

    def _wrap(self, m, key, orig):
        import torch

        def fwd(x, params, *a, **kw):
            y = orig(x, params, *a, **kw)
            if not self.enabled or not isinstance(y, torch.Tensor) or y.dim() < 2:
                return y
            seqlens = params.get("cache_seqlens")
            if seqlens is None:
                return y
            start = int(seqlens[0].item()) if seqlens.device.type == "cpu" else int(seqlens[0].cpu().item())
            q = y.shape[-2] if y.dim() == 3 else y.shape[0]
            pend = params.get("pending_mlp_residual")
            for r in range(q):
                p = start + r
                if p not in self.positions:
                    continue
                row = (y[0, r] if y.dim() == 3 else y[r]).detach().float().cpu().clone()
                extra = None
                if pend is not None and isinstance(pend[1], torch.Tensor) and pend[1].dim() == 3:
                    extra = pend[1][0, r].detach().float().cpu().clone()
                self.calls += 1
                self.rows.setdefault(p, {})[key] = (self.calls, row, extra)
                self.where[p] = (start, r)
            return y
        return fwd

    def arm(self, positions):
        self.positions = set(positions)
        self.rows = {}
        self.where = {}
        self.calls = 0
        self.enabled = True

    def disarm(self):
        self.enabled = False

# ---------------------------------------------------------------- one generation

def generate(server, arms, arm, ids, max_tokens, capture=None, capture_positions=None, stop_at=None):
    import torch
    gen = server.gen
    arms.arm = arm
    arms.round = 0
    job = server.job_type(
        input_ids=ids,
        max_new_tokens=max_tokens if stop_at is None else min(max_tokens, stop_at),
        sampler=server.sampler_type(),
        stop_conditions=server.stop_ids,
        decode_special_tokens=False,
        identifier=uuid.uuid4().hex,
    )
    if capture is not None:
        capture.arm(capture_positions)
    # Fresh prefill for every generation: no prompt-page or recurrent-stash reuse across arms, so
    # every arm computes the prompt identically and only the decode rounds differ
    if gen.num_remaining_jobs():
        fail("generator not idle")
    gen.pagetable.reset_page_table()
    n_rounds0 = len(getattr(job, "draft_stats", []) or [])
    final = None
    t0 = time.perf_counter()
    try:
        gen.enqueue(job)
        while gen.num_remaining_jobs():
            for e in gen.iterate():
                if e.get("identifier") == job.identifier and e.get("eos"):
                    final = e
                if e.get("stage") == "error" and e.get("job") is job:
                    raise RuntimeError(f"generator reaped the job: {e.get('error')!r}")
    except BaseException:
        # leave the generator idle for whatever runs next (the error is re-raised to the caller)
        try:
            gen.cancel(job)
        except Exception:
            pass
        raise
    finally:
        if capture is not None:
            capture.disarm()
        arms.arm = "normal"
    wall = time.perf_counter() - t0
    if final is None:
        fail("no terminal event")
    P = ids.shape[-1]
    out = job.sequences[0].sequence_ids.torch().flatten()[P:].tolist()
    rounds = []
    for s in (job.draft_stats or [])[n_rounds0:]:
        new_after, win, accepted = s
        rounds.append([P + new_after - (accepted + 1), accepted + 1])
    return {"ids": [int(v) for v in out], "wall_s": wall, "rounds": rounds,
            "new_tokens": final.get("new_tokens"), "eos_reason": final.get("eos_reason")}


def first_diff(a, b):
    for i, (x, y) in enumerate(zip(a, b)):
        if x != y:
            return i
    return None if len(a) == len(b) else min(len(a), len(b))


def probe(server, arms, capture, name, ids, max_tokens, arm_a, arm_b, t):
    P = ids.shape[-1]
    lo = max(P, P + t - 8)
    positions = list(range(lo, P + t))
    caps = {}
    for arm in (arm_a, arm_b):
        r = generate(server, arms, arm, ids, max_tokens, capture, positions, stop_at=t + 1)
        caps[arm] = ({p: dict(v) for p, v in capture.rows.items()}, dict(capture.where), r["ids"])
    ra, wa, ia = caps[arm_a]
    rb, wb, ib = caps[arm_b]
    report = {"case": name, "arms": [arm_a, arm_b], "t": t, "prompt": P,
              "tokens_at_t": [ia[t] if t < len(ia) else None, ib[t] if t < len(ib) else None],
              "positions": []}
    earliest = None
    for p in positions:
        ma, mb = ra.get(p, {}), rb.get(p, {})
        order = sorted(set(ma) & set(mb), key=lambda k: ma[k][0])
        first = None
        for k in order:
            xa, ea = ma[k][1], ma[k][2]
            xb, eb = mb[k][1], mb[k][2]
            same = xa.shape == xb.shape and bool((xa == xb).all()) and \
                ((ea is None and eb is None) or (ea is not None and eb is not None and bool((ea == eb).all())))
            if not same:
                d = float((xa - xb).abs().max()) if xa.shape == xb.shape else None
                first = {"module": k, "max_abs_diff": d}
                break
        entry = {"pos": p, "where": {arm_a: wa.get(p), arm_b: wb.get(p)},
                 "modules_compared": len(order), "first_diff": first}
        report["positions"].append(entry)
        if first is not None and earliest is None:
            earliest = entry
    report["earliest"] = earliest
    report["logits_at_t_minus_1"] = {arm_a: logits_top_rows(ra, P + t - 1), arm_b: logits_top_rows(rb, P + t - 1)}
    return report


def logits_top_rows(rows_by_pos, pos):
    import torch
    rows = rows_by_pos.get(pos, {})
    if not rows:
        return None
    key, (idx, v, _) = max(rows.items(), key=lambda kv: kv[1][0])
    if v.numel() < 100000:
        return {"module": key, "note": "last captured module is not the head"}
    top = torch.topk(v, 8)
    return {"module": key, "top": [[int(i), float(x)] for x, i in zip(top.values, top.indices)],
            "margin": float(top.values[0] - top.values[1])}


def run(args):
    import torch
    srv = load_module("exl3_server", SERVER_PY)
    server = make_server(srv)
    gen = server.gen
    gen.record_draft_stats = True
    if not hasattr(gen, "greedy_verify_rounds"):
        fail("engine lacks greedy_verify_rounds (not the candidate engine)")
    arms = Arms(gen)
    capture = Capture(gen.model)
    ws = workloads(srv, server, args)
    arm_list = args.arms.split(",")
    if arm_list[0] != "normal":
        fail("the first arm must be normal (the reference)")
    if "m1" in arm_list and getattr(gen, "tree", False):
        fail("the m1 arm needs EXL3_TREE=0 (the tree verify has no serial decode)")
    os.makedirs(args.out, exist_ok=True)
    result = {"arms": arm_list, "cases": {}, "probes": [], "errors": []}
    ok = True
    for name, ids, max_tokens in ws:
        rec = {"prompt_tokens": ids.shape[-1], "max_tokens": max_tokens, "arms": {}}
        for arm in arm_list:
            try:
                r = generate(server, arms, arm, ids, max_tokens)
            except SystemExit:
                raise
            except Exception as e:
                result["errors"].append({"case": name, "arm": arm, "error": repr(e),
                                         "trace": traceback.format_exc()})
                print(f"[{name}] {arm}: ERROR {e!r}", flush=True)
                # an arm error fails the gate: record it, write the partial result, stop the payload
                result["cases"][name] = rec
                result["pass"] = False
                with open(os.path.join(args.out, "result.json"), "w") as f:
                    json.dump(result, f)
                fail(f"{name}/{arm}: {e!r}")
            r["ids_sha256"] = hashlib.sha256(json.dumps(r["ids"]).encode()).hexdigest()
            rec["arms"][arm] = r
            ref = rec["arms"].get("normal")
            d = None if ref is None or arm == "normal" else first_diff(ref["ids"], r["ids"])
            r["first_diff_vs_normal"] = d
            r["equal_to_normal"] = ref is not None and r["ids"] == ref["ids"]
            if arm in REQUIRED_EQUAL and not r["equal_to_normal"]:
                ok = False
            cpr = sum(c for _, c in r["rounds"]) / max(len(r["rounds"]), 1)
            print(f"[{name}] {arm}: {len(r['ids'])} tok, {len(r['rounds'])} rounds "
                  f"({cpr:.2f}/round), {r['wall_s']:.1f}s, equal={r['equal_to_normal']} "
                  f"first_diff={d}", flush=True)
        result["cases"][name] = rec
        with open(os.path.join(args.out, "result.json"), "w") as f:
            json.dump(result, f)
        if args.no_probe:
            continue
        ref = rec["arms"].get("normal")
        for arm in REQUIRED_EQUAL + REPORTED:
            r = rec["arms"].get(arm)
            if ref is None or r is None or r["equal_to_normal"]:
                continue
            t = r["first_diff_vs_normal"]
            if t is None or t >= min(len(ref["ids"]), len(r["ids"])):
                continue
            try:
                pr = probe(server, arms, capture, name, ids, max_tokens, "normal", arm, t)
            except Exception as e:
                result["errors"].append({"case": name, "probe": arm, "error": repr(e),
                                         "trace": traceback.format_exc()})
                continue
            result["probes"].append(pr)
            e = pr["earliest"]
            print(f"[{name}] probe normal vs {arm} at t={t}: earliest differing position "
                  f"{e and e['pos']} first module {e and e['first_diff']} "
                  f"where {e and e['where']}", flush=True)
            with open(os.path.join(args.out, "result.json"), "w") as f:
                json.dump(result, f)
    result["pass"] = ok and not any(e.get("arm") in REQUIRED_EQUAL for e in result["errors"])
    with open(os.path.join(args.out, "result.json"), "w") as f:
        json.dump(result, f)
    summary = []
    for name, rec in result["cases"].items():
        row = [name, str(len(rec["arms"].get("normal", {}).get("ids", [])))]
        for arm in arm_list[1:]:
            r = rec["arms"].get(arm)
            row.append(f"{arm}:" + ("ERR" if r is None else ("==" if r["equal_to_normal"]
                                                            else f"diff@{r['first_diff_vs_normal']}")))
        summary.append("  ".join(row))
    text = "\n".join(summary) + f"\n{'PASS' if result['pass'] else 'FAIL'}\n"
    with open(os.path.join(args.out, "summary.txt"), "w") as f:
        f.write(text)
    print(text, flush=True)


# ---------------------------------------------------------------- OOB diagnostic

def oob(args):
    import torch
    torch.cuda.memory._record_memory_history(enabled="all", context="alloc", stacks="python",
                                             max_entries=2_000_000)
    srv = load_module("exl3_server", SERVER_PY)
    from exllamav3.modules.attention_fn import bc_attn as bca_mod
    from exllamav3.modules.attention_fn import triton_paged as tp
    from exllamav3.util.tensor import g_tensor_cache

    slots = []
    cls = bca_mod.BCAttn
    orig_cfg = cls._configure
    # Record the exact bucket each slot receives (pointer + bucket bytes), so the extent check is
    # made against the buffer the slot really uses, for pristine and patched sizing alike.
    gb_calls = []
    orig_gb = g_tensor_cache.get_bucketed

    def gb(device, numel, dtype, x=""):
        t = orig_gb(device, numel, dtype, x)
        nb = 1 << max(numel - 1, 0).bit_length()
        gb_calls.append(dict(tag=x, numel=numel, ptr=t.data_ptr(), bytes=nb * t.element_size()))
        return t
    g_tensor_cache.get_bucketed = gb

    def cfg(self, bsz, q_len, causal, regime):
        first_call = len(gb_calls)
        r = orig_cfg(self, bsz, q_len, causal, regime)
        used = {c["tag"]: c for c in gb_calls[first_call:] if c["tag"] in ("bca_po", "bca_ml")}
        import triton
        hd_pad = triton.next_power_of_2(self.head_dim)
        qh, kvh = self.num_q_heads, self.num_kv_heads
        block_n = max(16, 8192 // hd_pad)
        block_m = triton.next_power_of_2(q_len)
        block_h = max(16 // block_m, 1)
        block_rows = block_m * block_h
        h_blocks = triton.cdiv(qh // kvh, block_h)
        programs = bsz * kvh * h_blocks
        splits_cap = max(1, min(2 * bca_mod._get_sm_count(self.device) // programs, 128))
        use_gqa, splits, _ = tp.gqa_geometry(bsz, kvh, h_blocks, splits_cap,
                                             bca_mod._get_sm_count(self.device), block_n)
        if use_gqa:
            extent = ((bsz * kvh - 1) * splits + splits - 1) * h_blocks + h_blocks
        else:
            extent = programs * splits_cap
        pn_o_pristine = programs * splits_cap * block_rows * hd_pad
        slots.append(dict(layer=getattr(self.module, "layer_idx", None), window=str(getattr(self, "window_size", None)),
                          bsz=bsz, q_len=q_len, regime=regime, head_dim=self.head_dim, qh=qh, kvh=kvh,
                          use_gqa=use_gqa, SPLITS=splits, NSUB=h_blocks, programs=programs,
                          splits_cap=splits_cap, block_rows=block_rows, hd_pad=hd_pad,
                          extent_blocks=extent, pristine_blocks=programs * splits_cap,
                          need_o=extent * block_rows * hd_pad, need_ml=extent * block_rows * 2,
                          pristine_o=pn_o_pristine,
                          backing_po=used.get("bca_po"), backing_ml=used.get("bca_ml")))
        return r
    cls._configure = cfg

    server = make_server(srv)
    gen = server.gen
    ids = server.tokenizer.hf_chat_template(
        [{"role": "user", "content": "Count from one to forty in words, separated by commas."}],
        add_generation_prompt=True, enable_thinking=False)
    if ids.ndim == 1:
        ids = ids.unsqueeze(0)
    arms = Arms(gen)
    r = generate(server, arms, "normal", ids, 160)
    torch.cuda.synchronize()

    backings = {}
    for key, (refc, t) in g_tensor_cache.cache.items():
        tag = key.rsplit("/", 1)[-1]
        if tag in ("bca_po", "bca_ml"):
            backings[key] = dict(tag=tag, ptr=t.data_ptr(), numel=t.numel(), bytes=t.numel() * t.element_size(),
                                 refc=refc)
    snap = torch.cuda.memory._snapshot()
    blocks = []
    for seg in snap["segments"]:
        addr = seg["address"]
        for b in seg["blocks"]:
            frames = [f"{f['filename']}:{f['line']}:{f['name']}" for f in (b.get("frames") or [])
                      if "exllamav3" in f["filename"] or "serve" in f["filename"] or "/work/" in f["filename"]]
            blocks.append(dict(addr=addr, size=b["size"], state=b["state"], seg_addr=seg["address"],
                               seg_size=seg["total_size"], frames=frames[:8]))
            addr += b["size"]

    def owner(ptr):
        for b in blocks:
            if b["addr"] <= ptr < b["addr"] + b["size"]:
                return b
        return None

    report = {"generated_tokens": len(r["ids"]), "slots": slots, "backings": list(backings.values()), "overflows": []}
    for s in slots:
        if s["regime"] != 0:
            continue
        for tag, need in (("bca_po", s["need_o"] * 4), ("bca_ml", s["need_ml"] * 4)):
            if tag == "bca_po":
                pn = s["pristine_o"]
            else:
                pn = s["pristine_blocks"] * s["block_rows"] * 2
            nb = 1 << max(pn - 1, 0).bit_length()
            dev = str(torch.device("cuda", 0))
            key = f"{dev}/{str((nb,))}/{str(torch.float)}/{tag}"
            observed = s.get("backing_po" if tag == "bca_po" else "backing_ml")
            bk = dict(tag=tag, ptr=observed["ptr"], bytes=observed["bytes"]) if observed else backings.get(key)
            if bk is None:
                # patched engines size differently: find the backing by exact extent instead
                cands = [b for b in backings.values() if b["tag"] == tag and b["bytes"] >= need]
                bk = min(cands, key=lambda b: b["bytes"]) if cands else None
            if bk is None:
                report["overflows"].append(dict(slot=s, tag=tag, note="backing not found"))
                continue
            if need <= bk["bytes"]:
                continue
            lo, hi = bk["ptr"] + bk["bytes"], bk["ptr"] + need
            hit = [dict(b, overlap=[max(lo, b["addr"]) - lo, min(hi, b["addr"] + b["size"]) - lo])
                   for b in blocks if b["addr"] < hi and b["addr"] + b["size"] > lo]
            own = owner(bk["ptr"])
            covered = sum(h["overlap"][1] - h["overlap"][0] for h in hit)
            report["overflows"].append(dict(
                layer=s["layer"], bsz=s["bsz"], q_len=s["q_len"], window=s["window"], tag=tag,
                backing_bytes=bk["bytes"], kernel_bytes=need, oob_bytes=need - bk["bytes"],
                backing_segment=own and [own["seg_addr"], own["seg_size"]],
                oob_bytes_in_known_blocks=covered, oob_bytes_unmapped_or_foreign=need - bk["bytes"] - covered,
                blocks=hit))
    os.makedirs(args.out, exist_ok=True)
    with open(os.path.join(args.out, "oob.json"), "w") as f:
        json.dump(report, f, indent=1)
    seen = set()
    for o in report["overflows"]:
        k = (o.get("bsz"), o.get("q_len"), o.get("tag"), o.get("window"))
        if k in seen:
            continue
        seen.add(k)
        print(f"OOB {o.get('tag')} bsz={o.get('bsz')} q_len={o.get('q_len')} window={o.get('window')}: "
              f"backing {o.get('backing_bytes')} B, kernels touch {o.get('kernel_bytes')} B "
              f"(+{o.get('oob_bytes')} B); {o.get('oob_bytes_unmapped_or_foreign')} B outside known blocks", flush=True)
        for b in o.get("blocks", []):
            print(f"   lands on {b['state']} block {b['size']} B at +{b['overlap'][0]}..+{b['overlap'][1]}: "
                  f"{b['frames'][:3]}", flush=True)
    print("OOB NONE" if not report["overflows"] else f"OOB {len(report['overflows'])} slot-buffer overflows", flush=True)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("run")
    a.add_argument("--out", required=True)
    a.add_argument("--arms", default="normal,cap,wrong0")
    a.add_argument("--cases", default="")
    a.add_argument("--bench", default="")
    a.add_argument("--tiny", default="3")
    a.add_argument("--no-probe", action="store_true")
    b = sub.add_parser("oob")
    b.add_argument("--out", required=True)
    args = ap.parse_args()
    {"run": run, "oob": oob}[args.cmd](args)


if __name__ == "__main__":
    main()
