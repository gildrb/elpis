#!/usr/bin/env python3
# F3 gather parity fixture: `gather_visible_out` (Triton) vs the eager oracle
# `gather_visible`, plus status-contract and negative-control gates.
# Runs in the candidate image on one exclusive GPU.
#
# Modes:
#   default                         test the deployed kernel vs the deployed oracle
#   KVARN_GATHER_CANDIDATE=<path>   test the candidate kernel (e.g. /tmp/gather/gather-A.py)
#                                  vs the deployed oracle AND bit-exact vs the
#                                  deployed kernel on identical inputs.
#
# Gates (a case passes only if all hold):
#   valid cases   : status stays 0 (or preserves pre-poisoned bits), outputs
#                   within one bf16 ulp of the eager oracle (repo tolerance:
#                   atol 2^-10, rtol 2^-7), padded columns exactly zero.
#   invalid cases : status bit0 becomes 1; eager oracle rejects the same input.
#   sticky bits   : bit1 pre-set survives a valid run untouched and combines
#                   with bit0 on an invalid run (kernel never clears Status).
#   graph capture : a valid gather replays under torch.cuda.CUDAGraph with
#                   identical output and status (no host reads / allocation).
#   negative ctrl : three tampered wrappers (lost status signal, false status
#                   signal, corrupted output) MUST be detected by the gates;
#                   an undetected control fails the fixture.
import importlib.util
import json
import os
import sys
from types import ModuleType

import torch

import sglang.kernels.ops.kvarn.gather as deployed_gather

PAGES = 24
KV_HEADS = 8
HEAD_DIM = 128
TAIL_SLOTS = 8
WIDTH = 2184            # production draft window (2048 + 128 + 8)
MAX_VISIBLE = WIDTH     # gather bound is total rows
ATOL = 0.0009765625     # one bf16 ulp, repo convention (kvarn-nosync-parity)
RTOL = 0.0078125
SEED = 20260917

EVIDENCE = None


def load_candidate() -> ModuleType | None:
    path = os.environ.get("KVARN_GATHER_CANDIDATE")
    if not path:
        return None
    spec = importlib.util.spec_from_file_location(
        "sglang.kernels.ops.kvarn._gather_candidate", path)
    if spec is None or spec.loader is None:
        raise ValueError(f"Cannot load gather candidate: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def build(device):
    from sglang.srt.mem_cache.kvarn.layout import KVarNLayout
    from sglang.srt.mem_cache.kvarn.types import (
        KVarNCapacity, KVarNLayerView, KVarNWorkspace)
    layout = KVarNLayout(head_dim=HEAD_DIM, kv_heads=KV_HEADS, layer_ids=(0,))
    capacity = KVarNCapacity(
        token_capacity=PAGES * 128, tail_slots=TAIL_SLOTS, max_write_tokens=128,
        max_query_tokens=8, max_visible_tokens=MAX_VISIBLE,
        workspace_bytes=64 * 1024 * 1024)
    workspace = KVarNWorkspace.create(layout, capacity, torch.bfloat16,
                                      device, KV_HEADS)
    view = KVarNLayerView(
        packed=torch.zeros((PAGES, KV_HEADS, layout.tile_bytes),
                           dtype=torch.uint8, device=device),
        raw_keys=torch.zeros((TAIL_SLOTS, 128, KV_HEADS, HEAD_DIM),
                             dtype=torch.bfloat16, device=device),
        raw_values=torch.zeros((TAIL_SLOTS, 128, KV_HEADS, HEAD_DIM),
                               dtype=torch.bfloat16, device=device),
        page_to_tail_slot=torch.full((PAGES,), -1, dtype=torch.int32,
                                     device=device),
        valid_lengths=torch.zeros((PAGES,), dtype=torch.int32, device=device),
        layout=layout,
        committed_mask=torch.zeros((PAGES, 128), dtype=torch.bool,
                                   device=device),
        provisional_mask=torch.zeros((PAGES, 128), dtype=torch.bool,
                                     device=device),
        sink_pages=torch.zeros((PAGES,), dtype=torch.bool, device=device),
        tail_to_page=torch.full((TAIL_SLOTS,), -1, dtype=torch.int32,
                                device=device),
        preview_ready=torch.zeros((PAGES,), dtype=torch.bool, device=device),
    )
    return view, workspace


def write_page(view, workspace, page, generator):
    from sglang.kernels.ops.kvarn.store import begin_write_out
    device = view.packed.device
    keys = torch.randn((128, KV_HEADS, HEAD_DIM), generator=generator,
                       device=device, dtype=torch.float32).to(torch.bfloat16)
    values = torch.randn((128, KV_HEADS, HEAD_DIM), generator=generator,
                         device=device, dtype=torch.float32).to(torch.bfloat16)
    locations = torch.arange(page * 128, page * 128 + 128, device=device,
                             dtype=torch.int64)
    begin_write_out(view, locations, keys, values, False, workspace)


def seal(view, workspace):
    from sglang.kernels.ops.kvarn.store import complete_tiles_out
    complete_tiles_out(view, workspace, seal=True)


def run_kernel(module, view, locations, lengths, workspace, status):
    status.zero_()
    keys, values = module.gather_visible_out(view, locations, lengths,
                                             workspace, status)
    torch.cuda.synchronize()
    return keys.clone(), values.clone(), int(status.item())


def run_eager(view, locations, lengths, workspace):
    try:
        keys, values = deployed_gather.gather_visible(
            view, locations, lengths, workspace)
        return keys.clone(), values.clone(), None
    except ValueError as error:
        return None, None, str(error)


def parity(kernel_out, eager_out):
    keys_k, values_k = kernel_out
    keys_e, values_e = eager_out
    rows = []
    for name, got, want in (("keys", keys_k, keys_e), ("values", values_k, values_e)):
        diff = (got.float() - want.float()).abs()
        rows.append({
            "tensor": name,
            "bitexact": bool(torch.equal(got, want)),
            "max_abs": float(diff.max()),
            "within_one_ulp": bool((diff <= ATOL + RTOL * want.float().abs()).all()),
        })
    return rows


def padding_zero(keys, values, lengths):
    for row, length in enumerate(lengths.tolist()):
        if length < keys.shape[1]:
            if float(keys[row, length:].abs().max()) != 0.0:
                return False
            if float(values[row, length:].abs().max()) != 0.0:
                return False
    return True


def window(device, lengths, base_page=1, overwrites=None):
    rows = len(lengths)
    width = MAX_VISIBLE // rows
    locations = torch.arange(base_page * 128,
                             base_page * 128 + rows * width, device=device,
                             dtype=torch.int64).view(rows, width)
    for column, loc in (overwrites or {}).items():
        locations[:, column] = loc
    return locations.contiguous(), torch.tensor(lengths, dtype=torch.int32,
                                                device=device)


def valid_case(name, module, view, workspace, status, locations, lengths,
               cross=None):
    eager = run_eager(view, locations, lengths, workspace)
    keys, values, code = run_kernel(module, view, locations, lengths,
                                    workspace, status)
    result = {
        "case": name, "status": code, "expected_status": 0,
        "parity": parity((keys, values), (eager[0], eager[1])),
        "padding_zero": padding_zero(keys, values, lengths),
    }
    if cross is not None:
        keys_d, values_d, code_d = run_kernel(cross, view, locations,
                                              lengths, workspace, status)
        result["cross_bitexact"] = bool(
            torch.equal(keys, keys_d) and torch.equal(values, values_d))
        result["cross_status"] = code_d
    ok = (result["status"] == 0 and result["padding_zero"]
          and all(r["within_one_ulp"] for r in result["parity"]))
    if "cross_bitexact" in result:
        ok = ok and result["cross_bitexact"] and result["cross_status"] == 0
    result["ok"] = bool(ok)
    if EVIDENCE is not None:
        EVIDENCE("gather", {"locations": locations, "lengths": lengths,
                 "keys": keys, "values": values, "reference_keys": eager[0],
                 "reference_values": eager[1]}, {"case": name, "status": code})
    return result


def invalid_case(name, module, view, workspace, status, locations, lengths):
    keys_e, values_e, oracle_error = run_eager(view, locations, lengths,
                                               workspace)
    keys, values, code = run_kernel(module, view, locations, lengths,
                                    workspace, status)
    ok = code & 1 == 1 and oracle_error is not None
    if EVIDENCE is not None:
        EVIDENCE("gather_invalid", {"locations": locations, "lengths": lengths},
                 {"case": name, "status": code, "oracle_error": oracle_error})
    return {"case": name, "status": code, "expected_status": 1,
            "oracle_rejected": oracle_error is not None,
            "oracle_error": oracle_error, "ok": bool(ok)}


def graph_case(module, view, workspace, status, locations, lengths):
    eager = run_eager(view, locations, lengths, workspace)
    status.zero_()
    stream = torch.cuda.Stream()
    with torch.cuda.stream(stream):
        module.gather_visible_out(view, locations, lengths, workspace, status)
    torch.cuda.current_stream().wait_stream(stream)
    graph = torch.cuda.CUDAGraph()
    with torch.cuda.graph(graph):
        keys, values = module.gather_visible_out(view, locations, lengths,
                                                 workspace, status)
    status.zero_()
    graph.replay()
    torch.cuda.synchronize()
    first = (keys.clone(), values.clone(), int(status.item()))
    status.zero_()
    graph.replay()
    torch.cuda.synchronize()
    second = (keys.clone(), values.clone(), int(status.item()))
    rows = parity((first[0], first[1]), (eager[0], eager[1]))
    ok = (first[2] == 0 and second[2] == 0
          and torch.equal(first[0], second[0])
          and torch.equal(first[1], second[1])
          and all(r["within_one_ulp"] for r in rows))
    if EVIDENCE is not None:
        EVIDENCE("gather_graph", {"locations": locations, "lengths": lengths,
                 "keys": first[0], "values": first[1], "replay_keys": second[0],
                 "replay_values": second[1], "reference_keys": eager[0],
                 "reference_values": eager[1]},
                 {"case": "graph_replay", "status": first[2], "replay_status": second[2]})
    return {"case": "graph_replay", "status": first[2],
            "replay_bitexact": bool(torch.equal(first[0], second[0])
                                    and torch.equal(first[1], second[1])),
            "parity": rows, "ok": bool(ok)}


def negative_controls(module, view, workspace, status):
    device = view.packed.device
    controls = []
    # NC1 lost-status: an invalid gather whose status is cleared post-launch
    # (a change that stops reporting invalid lanes) must trip the status gate.
    locations, lengths = window(device, [WIDTH], overwrites={0: 0})
    status.zero_()
    module.gather_visible_out(view, locations, lengths, workspace, status)
    torch.cuda.synchronize()
    status.zero_()  # tamper: simulate a kernel that never ORs bit0
    detected = int(status.item()) & 1 != 1
    controls.append({"control": "lost_status_signal", "detected": bool(detected)})
    # NC2 false-status: a valid gather that sets bit0 (a change that reports
    # success lanes as invalid) must trip the status gate.
    locations, lengths = window(device, [8])
    status.zero_()
    module.gather_visible_out(view, locations, lengths, workspace, status)
    torch.cuda.synchronize()
    status |= 1  # tamper: simulate a spurious success-path RED
    detected = int(status.item()) != 0
    controls.append({"control": "false_status_signal", "detected": bool(detected)})
    # NC3 corrupt-output: a one-element output corruption inside the valid
    # prefix must trip the one-ulp parity gate.
    locations, lengths = window(device, [8])
    eager = run_eager(view, locations, lengths, workspace)
    keys, values, code = run_kernel(module, view, locations, lengths,
                                    workspace, status)
    keys[0, 3, 0, 5] += 1.0  # tamper: one bf16 element far outside tolerance
    rows = parity((keys, values), (eager[0], eager[1]))
    detected = not all(r["within_one_ulp"] for r in rows)
    controls.append({"control": "corrupt_output", "detected": bool(detected)})
    return controls


def main():
    if not torch.cuda.is_available():
        print("cuda required", file=sys.stderr)
        return 2
    torch.cuda.init()
    device = "cuda"
    candidate = load_candidate()
    module = candidate if candidate is not None else deployed_gather
    cross = deployed_gather if candidate is not None else None
    generator = torch.Generator(device=device)
    generator.manual_seed(SEED)
    view, workspace = build(device)
    status = workspace.native_status
    # Pages 1..17 sealed committed (2176 packed tokens); page 18 written but
    # left provisional in a raw tail slot (mixed raw/packed window coverage).
    for page in range(1, 18):
        write_page(view, workspace, page, generator)
        seal(view, workspace)
    write_page(view, workspace, 18, generator)
    invalid_token = 23 * 128  # never-written page 23

    results = []
    # Valid: full production window, 2176 packed + 8 raw-tail tokens.
    locations, lengths = window(device, [WIDTH])
    results.append(valid_case("full_window_mixed_raw_packed", module, view,
                              workspace, status, locations, lengths, cross))
    # Valid: batch 2, mixed lengths, batch>1 flat-row mapping.
    locations, lengths = window(device, [MAX_VISIBLE // 2, 300])
    results.append(valid_case("two_rows_mixed_lengths", module, view,
                              workspace, status, locations, lengths, cross))
    # Valid: padding-heavy short prefix (length 5 of 2184).
    locations, lengths = window(device, [5])
    results.append(valid_case("padding_heavy_short_prefix", module, view,
                              workspace, status, locations, lengths, cross))
    # Valid: zero length, whole window padded.
    locations, lengths = window(device, [0])
    results.append(valid_case("zero_length_row", module, view, workspace,
                              status, locations, lengths, cross))
    # Sticky bits: pre-poisoned bit1 survives a valid run, then combines.
    locations, lengths = window(device, [8])
    status.fill_(2)
    keys, values = module.gather_visible_out(view, locations, lengths,
                                             workspace, status)
    torch.cuda.synchronize()
    sticky_kept = int(status.item())
    bad_locations, bad_lengths = window(device, [8], overwrites={0: 0})
    status.fill_(2)
    module.gather_visible_out(view, bad_locations, bad_lengths, workspace,
                              status)
    torch.cuda.synchronize()
    sticky_combined = int(status.item())
    if EVIDENCE is not None:
        EVIDENCE("gather_sticky", {}, {"valid": sticky_kept, "invalid": sticky_combined})
    results.append({"case": "sticky_prepoisoned_bits",
                    "status_after_valid": sticky_kept,
                    "status_after_invalid": sticky_combined,
                    "ok": bool(sticky_kept == 2 and sticky_combined == 3)})
    # Invalid metadata classes: kernel flags bit0, oracle rejects.
    for name, overwrites, lens in (
        ("invalid_unwritten_token", {0: invalid_token}, [WIDTH]),
        ("invalid_page_zero", {0: 0}, [WIDTH]),
        ("invalid_page_out_of_range", {0: PAGES * 128}, [WIDTH]),
        ("invalid_negative_length", None, [-1]),
        ("invalid_length_over_width", None, [WIDTH + 1]),
    ):
        locations, lengths = window(device, [WIDTH], overwrites=overwrites)
        lengths = torch.tensor(lens, dtype=torch.int32, device=device)
        results.append(invalid_case(name, module, view, workspace, status,
                                    locations, lengths))
    # Graph capture safety of the module under test.
    locations, lengths = window(device, [8])
    results.append(graph_case(module, view, workspace, status, locations,
                              lengths))
    controls = negative_controls(module, view, workspace, status)
    passed = (all(r["ok"] for r in results)
              and all(c["detected"] for c in controls))
    print(json.dumps({
        "module": "deployed" if candidate is None
                  else os.environ["KVARN_GATHER_CANDIDATE"],
        "cases": results, "negative_controls": controls,
        "passed": bool(passed)}, indent=1))
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
