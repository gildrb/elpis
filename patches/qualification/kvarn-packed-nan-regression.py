#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Regression qualification for KVarN attention correctness defect P0-C:
#   unused packed data contaminated valid raw attention inside
#   _packed_attention_split's packed-value matmul.
#
#   The split kernel loaded the packed scales/codes of EVERY valid physical
#   page and executed the packed-value tl.dot even when every packed
#   probability of the block was masked to zero (raw-only sink pages,
#   un-previewed incomplete tail pages). The packed pool is torch.empty, so
#   those records are arbitrary bytes and reinterpreted fp16 scales can be
#   NaN; 0 * NaN = NaN contaminated acc_rot INSIDE the matmul, before any
#   output-row mask. Probability masking does not sanitize an invalid value
#   operand. The kernel also computed BOTH representations on pages that
#   need only one.
#
#   Fix under test (decode-fixed.py): each representation pass runs only when
#   at least one (row, token) lane of the block selects it. use_raw mirrors
#   decode_head, so a lane selects packed only when a packed tile exists
#   (sealed page slot<0, or preview_ready with the query passing the page);
#   invalid operands can never reach a matmul, and single-representation
#   pages stop paying for the other matmul. Skipped passes are exact no-ops
#   (CPU proof: results/cpu-proof.json).
#
# Runs INSIDE the candidate image on one exclusive GPU (no model server).
# Three modules are exercised in one process:
#   deployed : the installed sglang decode.py (historical defect)
#   fixed    : /k/decode-fixed.py (the P0-C fix)
#   nogate   : decode-fixed.py with both gates forced to `if True:` -- the
#              fix with ONLY the gate removed; it must reproduce the defect,
#              proving the gate is the operative change (negative control).
# The NaN poison is deterministic (0xFF bytes -> fp16 NaN records), so both
# the defect and the fix are reproducible without relying on whatever
# torch.empty happened to return.
import hashlib
import importlib.util
import json
import sys
import time
from types import ModuleType

import torch

from sglang.kernels.ops.kvarn.store import begin_write_out, complete_tiles_out
from sglang.srt.mem_cache.kvarn.layout import KVarNLayout
from sglang.srt.mem_cache.kvarn.types import (
    KVarNCapacity,
    KVarNLayerView,
    KVarNWorkspace,
)

KV_HEADS = 4
HEAD_DIM = 256
QUERY_HEADS = 24
SCALE = HEAD_DIM**-0.5
ATOL = 0.0009765625
RTOL = 0.0078125
RMSE = 0.00048828125


def load_module(name: str, path: str) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ValueError(f"Cannot load module {name!r} from {path}")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def module_identity(mod):
    src = open(mod.__file__, "rb").read()
    return {"path": mod.__file__, "sha256": hashlib.sha256(src).hexdigest()}


def build(device, pages):
    """View with `pages` usable pages; physical page 0 reserved (packed zeros)."""
    layout = KVarNLayout(head_dim=HEAD_DIM, kv_heads=KV_HEADS, layer_ids=(0,))
    capacity = KVarNCapacity(
        token_capacity=pages * 128, tail_slots=8, max_write_tokens=128,
        max_query_tokens=32, max_visible_tokens=128, workspace_bytes=64 * 1024 * 1024,
    )
    workspace = KVarNWorkspace.create(layout, capacity, torch.bfloat16, device, QUERY_HEADS)
    view = KVarNLayerView(
        packed=torch.zeros((pages + 1, KV_HEADS, layout.tile_bytes), dtype=torch.uint8, device=device),
        raw_keys=torch.zeros((8, 128, KV_HEADS, HEAD_DIM), dtype=torch.bfloat16, device=device),
        raw_values=torch.zeros((8, 128, KV_HEADS, HEAD_DIM), dtype=torch.bfloat16, device=device),
        page_to_tail_slot=torch.full((pages + 1,), -1, dtype=torch.int32, device=device),
        valid_lengths=torch.zeros((pages + 1,), dtype=torch.int32, device=device),
        layout=layout,
        committed_mask=torch.zeros((pages + 1, 128), dtype=torch.bool, device=device),
        provisional_mask=torch.zeros((pages + 1, 128), dtype=torch.bool, device=device),
        sink_pages=torch.zeros((pages + 1,), dtype=torch.bool, device=device),
        tail_to_page=torch.full((8,), -1, dtype=torch.int32, device=device),
        preview_ready=torch.zeros((pages + 1,), dtype=torch.bool, device=device),
    )
    return view, workspace


def write_tokens(view, workspace, page, count, generator, device):
    k = torch.randn((count, KV_HEADS, HEAD_DIM), generator=generator, device=device,
                    dtype=torch.float32).to(torch.bfloat16)
    v = torch.randn((count, KV_HEADS, HEAD_DIM), generator=generator, device=device,
                    dtype=torch.float32).to(torch.bfloat16)
    locations = torch.arange(page * 128, page * 128 + count, device=device, dtype=torch.int64)
    begin_write_out(view, locations, k, v, False, workspace)
    return k, v


def build_poisoned_view(device, generator):
    """Six usable pages:
         1..3 sealed packed-only (slot -1, valid packed tiles)
         4    sink page, raw-only (poisoned packed tile)
         5    complete, previewed, still in tail (mixed boundary)
         6    incomplete 8-token tail, raw-only (poisoned packed tile)
    """
    view, workspace = build(device, 6)
    for page in (1, 2, 3):
        write_tokens(view, workspace, page, 128, generator, device)
        complete_tiles_out(view, workspace, seal=True)
    view.sink_pages[4] = True
    write_tokens(view, workspace, 4, 128, generator, device)
    complete_tiles_out(view, workspace, seal=True)
    write_tokens(view, workspace, 5, 128, generator, device)
    write_tokens(view, workspace, 6, 8, generator, device)
    # Deterministic NaN poison on the packed tiles that must never be read:
    # every fp16 scale/code record of pages 4 and 6 becomes 0xFFFF = NaN.
    view.packed[4, :, :] = 255
    view.packed[6, :, :] = 255
    state = {
        "sink_page": 4, "preview_page": 5, "incomplete_page": 6,
        "slots": view.page_to_tail_slot[1:7].tolist(),
        "preview": view.preview_ready[1:7].tolist(),
        "sink": view.sink_pages[1:7].tolist(),
        "valid_lengths": view.valid_lengths[1:7].tolist(),
    }
    return view, workspace, state


def query_geometry(device):
    """Eight rows, one request: mixed, boundary, packed-only, short, dead."""
    lower = torch.tensor([0, 0, 0, 0, 0, 0, 384, 0], device=device, dtype=torch.int32)
    upper = torch.tensor([648, 600, 640, 384, 8, 0, 648, 648], device=device, dtype=torch.int32)
    crosses_poison = [True, True, True, False, False, False, True, True]
    return lower, upper, crosses_poison


def run_entry(module, entry, q, view, table, request_ids, lower, upper, workspace):
    workspace.native_status.zero_()
    out = getattr(module, entry)(q, view, table, request_ids, lower, upper, SCALE, workspace)
    torch.cuda.synchronize()
    status = int(workspace.native_status.item())
    return out.clone(), status


def stats(out, ref):
    diff = (out.float() - ref.float()).abs()
    return {
        "max_abs": float(diff.max()),
        "rmse": float(diff.pow(2).mean().sqrt()),
        "within": bool((diff <= ATOL + RTOL * ref.float().abs()).all()),
        "finite": bool(torch.isfinite(out.float()).all()),
    }


def correctness_cases(fixed, deployed, nogate, device, generator):
    view, workspace, state = build_poisoned_view(device, generator)
    table = torch.zeros((1, 2057), device=device, dtype=torch.int32)
    table[0, :6] = torch.arange(1, 7, device=device, dtype=torch.int32)
    lower, upper, crosses_poison = query_geometry(device)
    q = torch.randn((8, QUERY_HEADS, HEAD_DIM), generator=generator, device=device,
                    dtype=torch.float32).to(torch.bfloat16)
    request_ids = torch.zeros((8,), device=device, dtype=torch.int32)
    # Reference: the UNCHANGED deployed PyTorch oracle (never reads a packed
    # tile a lane did not select; raises on unowned pages).
    ref = deployed.packed_attention(q, view, table, request_ids, lower, upper,
                                    SCALE, workspace).clone()
    ref_finite = bool(torch.isfinite(ref.float()).all())
    results = []

    for name, module in (("fixed", fixed), ("deployed", deployed), ("nogate", nogate)):
        for entry in ("packed_attention_out_nosync", "packed_attention_out"):
            out, status = run_entry(module, entry, q, view, table, request_ids,
                                    lower, upper, workspace)
            finite_rows = torch.isfinite(out.float()).all(dim=(1, 2))
            nan_rows = (~finite_rows).tolist()
            s = stats(out[:8], ref)
            entry_report = {
                "module": name, "entry": entry, "status": status,
                "ref_finite": ref_finite,
                "within": s["within"], "finite": s["finite"],
                "max_abs": s["max_abs"], "rmse": s["rmse"],
                "nan_rows": nan_rows,
                "dead_row_zero": bool((out[5].float() == 0).all()),
                "poison_crossing_rows": crosses_poison,
            }
            if name == "fixed":
                entry_report["passed"] = (
                    status == 0 and s["within"] and s["finite"] and entry_report["dead_row_zero"]
                )
            else:
                # Negative controls: gate-free kernel must return NaN on
                # exactly the rows whose range crosses a poisoned raw-only
                # page, and must fail the oracle comparison.
                # The defect is reproduced when the output is contaminated
                # (non-finite, oracle mismatch) and every row whose range
                # crosses a poisoned raw-only page is NaN. The deployed
                # kernel may NaN additional rows (shared accumulator lanes);
                # requiring exact row equality over-specifies the failure.
                crossing_nan = all(
                    bool(n) for n, c in zip(nan_rows, crosses_poison) if c
                )
                entry_report["defect_reproduced"] = (
                    status == 0 and not s["finite"] and not s["within"] and crossing_nan
                )
                entry_report["passed"] = bool(entry_report["defect_reproduced"])
            results.append(entry_report)
    return results, state


def time_launches(module, view, workspace, table, q, request_ids, lower, upper, iters=20):
    start = torch.cuda.Event(enable_timing=True)
    stop = torch.cuda.Event(enable_timing=True)
    for _ in range(5):
        module.packed_attention_out_nosync(q, view, table, request_ids, lower, upper,
                                           SCALE, workspace)
    torch.cuda.synchronize()
    start.record()
    for _ in range(iters):
        module.packed_attention_out_nosync(q, view, table, request_ids, lower, upper,
                                           SCALE, workspace)
    stop.record()
    torch.cuda.synchronize()
    return round(start.elapsed_time(stop) * 1000.0 / iters, 1)


def speed_cases(fixed, deployed, device, generator):
    """Per-launch microseconds at three depths, both modules, interleaved
    twice so session drift is visible. All-sealed geometry (microbench
    precedent): every page is packed-only for the fixed kernel except the
    raw tail page, so this measures the removed duplicate matmul."""
    results = {}
    for pages in (8, 64, 230):
        view, workspace = build(device, pages)
        for page in range(1, pages + 1):
            write_tokens(view, workspace, page, 128, generator, device)
            if page < pages:
                complete_tiles_out(view, workspace, seal=True)
        table = torch.zeros((1, 2057), device=device, dtype=torch.int32)
        table[0, :pages] = torch.arange(1, pages + 1, device=device, dtype=torch.int32)
        tokens = pages * 128
        q = torch.randn((8, QUERY_HEADS, HEAD_DIM), generator=generator, device=device,
                        dtype=torch.float32).to(torch.bfloat16)
        request_ids = torch.zeros((8,), device=device, dtype=torch.int32)
        lower = torch.zeros((8,), device=device, dtype=torch.int32)
        upper = (tokens - 8) + torch.arange(8, device=device, dtype=torch.int32)
        ref = deployed.packed_attention(q, view, table, request_ids, lower, upper,
                                        SCALE, workspace).clone()
        parity = {}
        for name, module in (("deployed", deployed), ("fixed", fixed)):
            out, status = run_entry(module, "packed_attention_out_nosync", q, view, table,
                                    request_ids, lower, upper, workspace)
            parity[name] = {"status": status, **stats(out, ref)}
        rounds = {}
        for round_id in (1, 2):
            rounds[f"deployed_r{round_id}"] = time_launches(deployed, view, workspace, table,
                                                            q, request_ids, lower, upper)
            rounds[f"fixed_r{round_id}"] = time_launches(fixed, view, workspace, table,
                                                         q, request_ids, lower, upper)
        results[str(pages)] = {"parity": parity, "us_per_launch": rounds}
    return results


def main():
    if not torch.cuda.is_available():
        print("cuda required", file=sys.stderr)
        return 2
    torch.cuda.init()
    device = "cuda"
    torch.manual_seed(20260917)
    generator = torch.Generator(device=device)
    generator.manual_seed(20260917)
    import sglang.kernels.ops.kvarn.decode as deployed_mod
    fixed_path = "/k/decode-fixed.py"
    fixed_mod = load_module("sglang.kernels.ops.kvarn.decode_fixed", fixed_path)
    nogate_src = open(fixed_path).read()
    for gate in ("if tl.sum(raw_sel.to(tl.int32)) > 0:",
                 "if tl.sum(packed_sel.to(tl.int32)) > 0:"):
        if nogate_src.count(gate) != 1:
            print(f"gate marker not unique: {gate}", file=sys.stderr)
            return 2
        nogate_src = nogate_src.replace(gate, "if True:")
    nogate_path = "/tmp/decode-nogate.py"
    with open(nogate_path, "w") as f:
        f.write(nogate_src)
    nogate_mod = load_module("sglang.kernels.ops.kvarn.decode_nogate", nogate_path)
    t0 = time.time()
    cases, view_state = correctness_cases(fixed_mod, deployed_mod, nogate_mod, device, generator)
    speed = speed_cases(fixed_mod, deployed_mod, device, generator)
    report = {
        "schema_version": 1,
        "gpu": torch.cuda.get_device_name(0),
        "fixture": "packed-nan-regression",
        "modules": {
            "deployed": module_identity(deployed_mod),
            "fixed": module_identity(fixed_mod),
            "nogate": module_identity(nogate_mod),
        },
        "view_state": view_state,
        "cases": cases,
        "speed": speed,
        "elapsed_s": round(time.time() - t0, 1),
    }
    fixed_ok = all(c["passed"] for c in cases if c["module"] == "fixed")
    controls_ok = all(c["passed"] for c in cases if c["module"] in ("deployed", "nogate"))
    depth_ok = all(
        v["parity"]["fixed"]["within"] and v["parity"]["fixed"]["status"] == 0
        for v in speed.values()
    )
    report["passed"] = fixed_ok and controls_ok and depth_ok
    out = sys.argv[1] if len(sys.argv) > 1 else "/k-results/packed-nan-regression.json"
    with open(out, "w") as f:
        json.dump(report, f, indent=1)
    print(json.dumps(report, indent=1))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
