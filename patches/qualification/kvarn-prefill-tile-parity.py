#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Parity fixture for the stage-15 tiled _packed_attention_split kernel.
#
# Runs INSIDE the candidate image on one exclusive GPU (no model server):
# builds a small synthetic KVarN layer view, writes pages through the real
# native store kernels, then compares the tiled triton kernel against the
# unchanged pure-PyTorch packed_attention oracle. Tolerances follow the
# packing-repair fixture precedent (atol 2**-10, rtol 2**-7, rmse 2**-11).
import json
import sys
import time

import torch
from sglang.kernels.ops.kvarn.decode import packed_attention, packed_attention_out
from sglang.kernels.ops.kvarn.store import begin_write_out, complete_tiles_out
from sglang.srt.mem_cache.kvarn.layout import KVarNLayout
from sglang.srt.mem_cache.kvarn.types import (
    KVarNCapacity,
    KVarNLayerView,
    KVarNWorkspace,
)

PAGES = 24
KV_HEADS = 4
HEAD_DIM = 256
QUERY_HEADS = 24
GROUP = QUERY_HEADS // KV_HEADS
SCALE = HEAD_DIM**-0.5
ATOL = 0.0009765625
RTOL = 0.0078125
RMSE = 0.00048828125

# Optional raw observation sink installed by bench.numerical; never changes gates.
EVIDENCE = None


def build(device: str) -> tuple[KVarNLayerView, KVarNWorkspace]:
    layout = KVarNLayout(head_dim=HEAD_DIM, kv_heads=KV_HEADS, layer_ids=(0,))
    capacity = KVarNCapacity(
        token_capacity=PAGES * 128,
        tail_slots=8,
        max_write_tokens=128,
        max_query_tokens=32,
        max_visible_tokens=128,
        workspace_bytes=64 * 1024 * 1024,
    )
    workspace = KVarNWorkspace.create(
        layout, capacity, torch.bfloat16, device, QUERY_HEADS
    )
    view = KVarNLayerView(
        packed=torch.zeros(
            (PAGES, KV_HEADS, layout.tile_bytes), dtype=torch.uint8, device=device
        ),
        raw_keys=torch.zeros(
            (8, 128, KV_HEADS, HEAD_DIM), dtype=torch.bfloat16, device=device
        ),
        raw_values=torch.zeros(
            (8, 128, KV_HEADS, HEAD_DIM), dtype=torch.bfloat16, device=device
        ),
        page_to_tail_slot=torch.full((PAGES,), -1, dtype=torch.int32, device=device),
        valid_lengths=torch.zeros((PAGES,), dtype=torch.int32, device=device),
        layout=layout,
        committed_mask=torch.zeros((PAGES, 128), dtype=torch.bool, device=device),
        provisional_mask=torch.zeros((PAGES, 128), dtype=torch.bool, device=device),
        sink_pages=torch.zeros((PAGES,), dtype=torch.bool, device=device),
        tail_to_page=torch.full((8,), -1, dtype=torch.int32, device=device),
        preview_ready=torch.zeros((PAGES,), dtype=torch.bool, device=device),
    )
    return view, workspace


def write_page(
    view: KVarNLayerView,
    workspace: KVarNWorkspace,
    page: int,
    generator: torch.Generator,
) -> None:
    keys = torch.randn(
        (128, KV_HEADS, HEAD_DIM),
        generator=generator,
        device=view.packed.device,
        dtype=torch.float32,
    ).to(torch.bfloat16)
    values = torch.randn(
        (128, KV_HEADS, HEAD_DIM),
        generator=generator,
        device=view.packed.device,
        dtype=torch.float32,
    ).to(torch.bfloat16)
    locations = torch.arange(
        page * 128, page * 128 + 128, device=view.packed.device, dtype=torch.int64
    )
    begin_write_out(view, locations, keys, values, False, workspace)


def seal(view: KVarNLayerView, workspace: KVarNWorkspace) -> None:
    complete_tiles_out(view, workspace, seal=True)


def run_case(
    view: KVarNLayerView,
    workspace: KVarNWorkspace,
    pages: int,
    raw_tail: bool,
    generator: torch.Generator,
    queries: int = 8,
    empty_rows: tuple[int, ...] = (),
) -> dict:
    device = view.packed.device
    q = torch.randn(
        (8, QUERY_HEADS, HEAD_DIM),
        generator=generator,
        device=device,
        dtype=torch.float32,
    ).to(torch.bfloat16)
    q = q[:queries].contiguous()
    table = torch.zeros((1, 2057), device=device, dtype=torch.int32)
    table[0, :pages] = torch.arange(1, pages + 1, device=device, dtype=torch.int32)
    request_ids = torch.zeros((queries,), device=device, dtype=torch.int64)
    lower = torch.zeros((queries,), device=device, dtype=torch.int64)
    upper = torch.full(
        (queries,),
        pages * 128 - (0 if raw_tail else 0),
        device=device,
        dtype=torch.int64,
    )
    upper[0] = pages * 128 - 61 if pages > 1 else 67
    if queries > 3 and pages > 1:
        upper[3] = 129
    for row in empty_rows:
        if row < queries:
            upper[row] = 0
    reference = packed_attention(
        q, view, table, request_ids, lower, upper, SCALE, workspace
    ).clone()
    workspace.native_status.zero_()
    output = packed_attention_out(
        q, view, table, request_ids, lower, upper, SCALE, workspace
    )
    torch.cuda.synchronize()
    status = int(workspace.native_status.item())
    diff = (output.float() - reference.float()).abs()
    denom = reference.float().abs().clamp_min(1e-6)
    case = {
        "pages": pages,
        "raw_tail": raw_tail,
        "queries": queries,
        "empty_rows": list(empty_rows),
        "status": status,
        "max_abs": float(diff.max()),
        "max_rel": float((diff / denom).max()),
        "rmse": float(diff.pow(2).mean().sqrt()),
        "within_tolerance": bool((diff <= ATOL + RTOL * reference.float().abs()).all()),
        "finite": bool(torch.isfinite(output.float()).all()),
    }
    if EVIDENCE is not None:
        EVIDENCE("prefill", {"q": q, "table": table, "requests": request_ids,
                 "lower": lower, "upper": upper, "output": output, "reference": reference},
                 {"pages": pages, "raw_tail": raw_tail, "queries": queries,
                  "empty_rows": list(empty_rows), "status": status})
    return case


def negative_case(
    view: KVarNLayerView,
    workspace: KVarNWorkspace,
    pages: int,
    bad_page: int | None,
    generator: torch.Generator,
) -> dict:
    device = view.packed.device
    q = torch.randn(
        (8, QUERY_HEADS, HEAD_DIM),
        generator=generator,
        device=device,
        dtype=torch.float32,
    ).to(torch.bfloat16)
    table = torch.zeros((1, 2057), device=device, dtype=torch.int32)
    table[0, :pages] = torch.arange(1, pages + 1, device=device, dtype=torch.int32)
    if bad_page is not None:
        table[0, pages - 1] = bad_page
    request_ids = torch.zeros((8,), device=device, dtype=torch.int64)
    lower = torch.zeros((8,), device=device, dtype=torch.int64)
    upper = torch.full((8,), pages * 128, device=device, dtype=torch.int64)
    workspace.native_status.zero_()
    packed_attention_out(q, view, table, request_ids, lower, upper, SCALE, workspace)
    torch.cuda.synchronize()
    if EVIDENCE is not None:
        EVIDENCE("prefill_status", {"table": table, "lower": lower, "upper": upper},
                 {"bad_page": bad_page, "status": int(workspace.native_status.item())})
    return {
        "pages": pages,
        "bad_page": bad_page,
        "status": int(workspace.native_status.item()),
    }


def run_serving_chunk_case(
    view: KVarNLayerView,
    workspace: KVarNWorkspace,
    generator: torch.Generator,
) -> dict:
    device = view.packed.device
    keys = torch.randn(
        (8, KV_HEADS, HEAD_DIM),
        generator=generator,
        device=device,
        dtype=torch.float32,
    ).to(torch.bfloat16)
    values = torch.randn(
        (8, KV_HEADS, HEAD_DIM),
        generator=generator,
        device=device,
        dtype=torch.float32,
    ).to(torch.bfloat16)
    locations = torch.arange(128, 136, device=device, dtype=torch.int64)
    workspace.native_status.zero_()
    begin_write_out(view, locations, keys, values, False, workspace)
    torch.cuda.synchronize()
    write_status = int(workspace.native_status.item())
    view.sink_pages[1] = True
    q = torch.randn(
        (8, QUERY_HEADS, HEAD_DIM),
        generator=generator,
        device=device,
        dtype=torch.float32,
    ).to(torch.bfloat16)
    table = torch.zeros((1, 2057), device=device, dtype=torch.int64)
    table[0, 0] = 1
    request_ids = torch.zeros((8,), device=device, dtype=torch.int64)
    lower = torch.zeros((8,), device=device, dtype=torch.int64)
    upper = torch.arange(1, 9, device=device, dtype=torch.int64)
    reference = packed_attention(
        q, view, table, request_ids, lower, upper, SCALE, workspace
    ).clone()
    workspace.native_status.zero_()
    output = packed_attention_out(
        q, view, table, request_ids, lower, upper, SCALE, workspace
    )
    torch.cuda.synchronize()
    status = int(workspace.native_status.item())
    diff = (output.float() - reference.float()).abs()
    denom = reference.float().abs().clamp_min(1e-6)
    if EVIDENCE is not None:
        EVIDENCE("prefill", {"q": q, "table": table, "requests": request_ids,
                 "lower": lower, "upper": upper, "output": output, "reference": reference,
                 "keys": keys, "values": values, "locations": locations},
                 {"kind": "serving_first_chunk", "status": status, "write_status": write_status})
    return {
        "pages": 1,
        "raw_tail": True,
        "queries": 8,
        "empty_rows": [],
        "kind": "serving_first_chunk",
        "write_status": write_status,
        "status": status,
        "max_abs": float(diff.max()),
        "max_rel": float((diff / denom).max()),
        "rmse": float(diff.pow(2).mean().sqrt()),
        "within_tolerance": bool((diff <= ATOL + RTOL * reference.float().abs()).all()),
        "finite": bool(torch.isfinite(output.float()).all()),
    }

def main() -> int:
    if not torch.cuda.is_available():
        print("cuda device required", file=sys.stderr)
        return 2
    torch.cuda.init()
    device = "cuda"
    torch.manual_seed(20260913)
    generator = torch.Generator(device=device)
    generator.manual_seed(20260913)
    started = time.time()
    view, workspace = build(device)
    cases: list[dict] = []
    serving_view, serving_ws = build(device)
    cases.append(run_serving_chunk_case(serving_view, serving_ws, generator))
    # Sealed (packed) page depths, raw tail on the final page when requested.
    plan = [(1, False), (2, True), (3, False), (5, True), (9, False), (17, True)]
    state = 0
    for pages, raw_tail in plan:
        while state < pages:
            write_page(view, workspace, state + 1, generator)
            state += 1
            if state < pages or not raw_tail:
                seal(view, workspace)
        cases.append(run_case(view, workspace, pages, raw_tail, generator))
    cases.append(run_case(view, workspace, 17, True, generator, queries=5))
    cases.append(run_case(view, workspace, 17, True, generator, empty_rows=(2, 6)))
    negatives = [
        negative_case(view, workspace, 17, 0, generator),
        negative_case(view, workspace, 17, PAGES + 5, generator),
        negative_case(view, workspace, 17, None, generator),
    ]
    # The last negative reused a fully valid table: it must keep status clean
    # only if every visible token was written; with 17 written pages it is.
    elapsed = time.time() - started
    positives_ok = all(
        case["status"] == 0
        and case.get("write_status", 0) == 0
        and case["finite"]
        and case["within_tolerance"]
        and case["rmse"] <= RMSE
        for case in cases
    )
    negatives_ok = (
        negatives[0]["status"] == 1
        and negatives[1]["status"] == 1
        and negatives[2]["status"] == 0
    )
    report = {
        "schema_version": 1,
        "fixture": "kvarn-prefill-tile-parity",
        "device": torch.cuda.get_device_name(0),
        "capability": list(torch.cuda.get_device_capability(0)),
        "cases": cases,
        "negatives": negatives,
        "tolerances": {"atol": ATOL, "rtol": RTOL, "rmse": RMSE},
        "elapsed_seconds": elapsed,
        "passed": positives_ok and negatives_ok,
    }
    print(json.dumps(report, indent=1))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
