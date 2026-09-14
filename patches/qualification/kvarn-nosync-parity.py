#!/usr/bin/env python3
# Offline parity for the sync-free verify launch (packed_attention_out_nosync)
# against the PyTorch oracle. Runs in the candidate image on one exclusive GPU.
import json
import sys
import time

import torch

from sglang.kernels.ops.kvarn.decode import (
    packed_attention,
    packed_attention_out,
    packed_attention_out_nosync,
)
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
SCALE = HEAD_DIM**-0.5
ATOL = 0.0009765625
RTOL = 0.0078125
RMSE = 0.00048828125


def build(device):
    layout = KVarNLayout(head_dim=HEAD_DIM, kv_heads=KV_HEADS, layer_ids=(0,))
    capacity = KVarNCapacity(
        token_capacity=PAGES * 128, tail_slots=8, max_write_tokens=128,
        max_query_tokens=32, max_visible_tokens=128, workspace_bytes=64 * 1024 * 1024,
    )
    workspace = KVarNWorkspace.create(layout, capacity, torch.bfloat16, device, QUERY_HEADS)
    view = KVarNLayerView(
        packed=torch.zeros((PAGES, KV_HEADS, layout.tile_bytes), dtype=torch.uint8, device=device),
        raw_keys=torch.zeros((8, 128, KV_HEADS, HEAD_DIM), dtype=torch.bfloat16, device=device),
        raw_values=torch.zeros((8, 128, KV_HEADS, HEAD_DIM), dtype=torch.bfloat16, device=device),
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


def write_page(view, workspace, page, generator):
    keys = torch.randn((128, KV_HEADS, HEAD_DIM), generator=generator, device=view.packed.device, dtype=torch.float32).to(torch.bfloat16)
    values = torch.randn((128, KV_HEADS, HEAD_DIM), generator=generator, device=view.packed.device, dtype=torch.float32).to(torch.bfloat16)
    locations = torch.arange(page * 128, page * 128 + 128, device=view.packed.device, dtype=torch.int64)
    begin_write_out(view, locations, keys, values, False, workspace)


def run_case(view, workspace, pages, raw_tail, generator, queries=8):
    device = view.packed.device
    q = torch.randn((queries, QUERY_HEADS, HEAD_DIM), generator=generator, device=device, dtype=torch.float32).to(torch.bfloat16)
    table = torch.zeros((1, 2057), device=device, dtype=torch.int32)
    table[0, :pages] = torch.arange(1, pages + 1, device=device, dtype=torch.int32)
    request_ids = torch.zeros((queries,), device=device, dtype=torch.int32)
    lower = torch.zeros((queries,), device=device, dtype=torch.int32)
    upper = (pages * 128 - 8) + torch.arange(queries, device=device, dtype=torch.int32)
    reference = packed_attention(q, view, table, request_ids, lower, upper, SCALE, workspace).clone()
    cases = []
    buffers = {}
    for name, fn in (
        ("counted", packed_attention_out),
        ("nosync", packed_attention_out_nosync),
    ):
        workspace.native_status.zero_()
        out = fn(q, view, table, request_ids, lower, upper, SCALE, workspace)
        torch.cuda.synchronize()
        status = int(workspace.native_status.item())
        diff = (out.float() - reference.float()).abs()
        buffers[name] = (
            workspace.native_partial_lse.float().clone(),
            workspace.native_partial_output.float().clone(),
        )
        cases.append({
            "launch": name, "status": status,
            "max_abs": float(diff.max()), "rmse": float(diff.pow(2).mean().sqrt()),
            "within": bool((diff <= ATOL + RTOL * reference.float().abs()).all()),
            "finite": bool(torch.isfinite(out.float()).all()),
        })
    lse_c, part_c = buffers["counted"]
    lse_n, part_n = buffers["nosync"]
    finite_c = torch.isfinite(lse_c) & torch.isfinite(lse_n)
    cases[-1]["lse_max_delta"] = float((lse_c[finite_c] - lse_n[finite_c]).abs().max()) if finite_c.any() else 0.0
    cases[-1]["lse_inf_mismatch"] = int((torch.isinf(lse_c) != torch.isinf(lse_n)).sum())
    both = torch.isfinite(part_c) & torch.isfinite(part_n)
    cases[-1]["partial_max_delta"] = float((part_c[both] - part_n[both]).abs().max()) if both.any() else 0.0
    return cases


def main():
    if not torch.cuda.is_available():
        print("cuda required", file=sys.stderr)
        return 2
    torch.cuda.init()
    device = "cuda"
    torch.manual_seed(20260915)
    generator = torch.Generator(device=device)
    generator.manual_seed(20260915)
    view, workspace = build(device)
    cases = []
    plan = [(1, False), (2, True), (5, True), (17, True)]
    state = 0
    for pages, raw_tail in plan:
        while state < pages:
            write_page(view, workspace, state + 1, generator)
            state += 1
            if state < pages or not raw_tail:
                complete_tiles_out(view, workspace, seal=True)
        cases.extend(run_case(view, workspace, pages, raw_tail, generator))
    ok = all(c["status"] == 0 and c["finite"] and c["within"] for c in cases)
    print(json.dumps({"cases": cases, "passed": ok}, indent=1))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
