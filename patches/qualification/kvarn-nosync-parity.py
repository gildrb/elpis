#!/usr/bin/env python3
# Offline parity for the sync-free verify launch (packed_attention_out_nosync)
# against the PyTorch oracle. Runs in the candidate image on one exclusive GPU.
import argparse
import json
import sys

import torch

from sglang.kernels.ops.kvarn.decode import (
    decode_head,
    packed_attention,
    packed_attention_out,
    packed_attention_out_nosync,
)
from sglang.kernels.ops.kvarn.store import begin_write_out, complete_tiles_out
from sglang.srt.mem_cache.kvarn.layout import KVarNLayout
from sglang.srt.mem_cache.kvarn_budget import qualification_page_count
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

EVIDENCE = None


def build(device, pages=PAGES):
    layout = KVarNLayout(head_dim=HEAD_DIM, kv_heads=KV_HEADS, layer_ids=(0,))
    capacity = KVarNCapacity(
        token_capacity=(pages - 1) * 128, tail_slots=8, max_write_tokens=128,
        max_query_tokens=32, max_visible_tokens=128, workspace_bytes=64 * 1024 * 1024,
    )
    workspace = KVarNWorkspace.create(layout, capacity, torch.bfloat16, device, QUERY_HEADS)
    view = KVarNLayerView(
        packed=torch.zeros((pages, KV_HEADS, layout.tile_bytes), dtype=torch.uint8, device=device),
        raw_keys=torch.zeros((8, 128, KV_HEADS, HEAD_DIM), dtype=torch.bfloat16, device=device),
        raw_values=torch.zeros((8, 128, KV_HEADS, HEAD_DIM), dtype=torch.bfloat16, device=device),
        page_to_tail_slot=torch.full((pages,), -1, dtype=torch.int32, device=device),
        valid_lengths=torch.zeros((pages,), dtype=torch.int32, device=device),
        layout=layout,
        committed_mask=torch.zeros((pages, 128), dtype=torch.bool, device=device),
        provisional_mask=torch.zeros((pages, 128), dtype=torch.bool, device=device),
        sink_pages=torch.zeros((pages,), dtype=torch.bool, device=device),
        tail_to_page=torch.full((8,), -1, dtype=torch.int32, device=device),
        preview_ready=torch.zeros((pages,), dtype=torch.bool, device=device),
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

def run_native_graph_cases(device, generator, context):
    """Full visible-history oracle, compressed by exact repeated-tile counts."""
    if context not in (245760, 262144):
        raise ValueError("Unsupported native context")
    capacity = context + 1024
    physical_pages = qualification_page_count(capacity, capture=True)
    view, workspace = build(device, physical_pages)
    logical_pages = context // 128
    half = logical_pages // 2
    last_page = physical_pages - 1
    # Two real packed prototypes and a raw tail. The far half is deliberately
    # nonzero and differs from the final window by order-one values. A zero
    # query also makes every visible token contribute equal softmax mass.
    keys = torch.randn((128, KV_HEADS, HEAD_DIM), generator=generator,
                       device=device, dtype=torch.float32).to(torch.bfloat16)
    channels = torch.arange(HEAD_DIM, device=device, dtype=torch.float32)
    pattern = (1 + channels.remainder(8) / 16).view(1, 1, HEAD_DIM)
    for page, amplitude in ((2, 1.0), (3, -0.25)):
        values = (pattern * amplitude).expand(128, KV_HEADS, HEAD_DIM).contiguous().to(torch.bfloat16)
        locations = torch.arange(page * 128, (page + 1) * 128, device=device, dtype=torch.int64)
        begin_write_out(view, locations, keys, values, False, workspace)
        complete_tiles_out(view, workspace, seal=True)
    packed_tiles = view.packed[2:4].clone()
    view.packed[2:2 + half].copy_(packed_tiles[:1].expand(half, -1, -1))
    view.packed[2 + half:2 + logical_pages].copy_(
        packed_tiles[1:].expand(logical_pages - half, -1, -1))
    view.committed_mask[2:2 + logical_pages].fill_(True)
    view.valid_lengths[2:2 + logical_pages].fill_(128)
    tail_values = (pattern * -0.25).expand(128, KV_HEADS, HEAD_DIM).contiguous().to(torch.bfloat16)
    tail_locations = torch.arange(last_page * 128, (last_page + 1) * 128,
                                  device=device, dtype=torch.int64)
    begin_write_out(view, tail_locations, keys, tail_values, False, workspace)
    table = torch.zeros((1, physical_pages - 1), device=device, dtype=torch.int32)
    table[0, :logical_pages] = torch.arange(2, logical_pages + 2, device=device, dtype=torch.int32)
    table[0, logical_pages - 1] = last_page
    page_kinds = torch.cat((torch.zeros(half, dtype=torch.int64),
                           torch.ones(logical_pages - half - 1, dtype=torch.int64),
                           torch.full((1,), 2, dtype=torch.int64)))
    # Use the existing dequantized-KV reference, never a native attention output.
    decoded_keys, decoded_values = [], []
    for page in (2, 2 + half, last_page):
        decoded = [decode_head(view, page, head) for head in range(KV_HEADS)]
        decoded_keys.append(torch.stack([item[0].float() for item in decoded], dim=1))
        decoded_values.append(torch.stack([item[1].float() for item in decoded], dim=1))
    oracle_keys, oracle_values = torch.stack(decoded_keys), torch.stack(decoded_values)
    q = torch.randn((8, QUERY_HEADS, HEAD_DIM), generator=generator, device=device,
                    dtype=torch.float32).to(torch.bfloat16)
    q[0].zero_()
    requests = torch.zeros(8, device=device, dtype=torch.int32)
    lower = torch.zeros(8, device=device, dtype=torch.int32)
    upper = context - 7 + torch.arange(8, device=device, dtype=torch.int32)
    write_status = int(workspace.native_status.item())

    def reference_for_bounds():
        # Counting every logical page is equivalent to expanding repeated KV,
        # but avoids retaining or allocating a multi-GiB dense context.
        counts = torch.zeros((8, 3, 128), dtype=torch.int64)
        for row, (lo, hi) in enumerate(zip(lower.cpu().tolist(), upper.cpu().tolist(), strict=True)):
            for logical in range(lo // 128, (hi + 127) // 128):
                start, end = max(lo - logical * 128, 0), min(hi - logical * 128, 128)
                counts[row, int(page_kinds[logical]), start:end] += 1
        weights_count = counts.to(device=device, dtype=torch.float32)
        reference = torch.empty_like(q)
        for head in range(QUERY_HEADS):
            kv_head = head // (QUERY_HEADS // KV_HEADS)
            k = oracle_keys[:, :, kv_head].reshape(-1, HEAD_DIM)
            v = oracle_values[:, :, kv_head].reshape(-1, HEAD_DIM)
            logits = q[:, head].float() @ k.T * SCALE
            logits += weights_count.reshape(8, -1).log()
            reference[:, head] = torch.softmax(logits, dim=-1) @ v
        return reference, counts

    side = torch.cuda.Stream()
    side.wait_stream(torch.cuda.current_stream())
    with torch.cuda.stream(side):
        packed_attention_out_nosync(q, view, table, requests, lower, upper, SCALE, workspace)
    torch.cuda.current_stream().wait_stream(side)
    torch.cuda.synchronize()
    graph = torch.cuda.CUDAGraph()
    with torch.cuda.graph(graph):
        output = packed_attention_out_nosync(q, view, table, requests, lower, upper, SCALE, workspace)
    cases = []
    references = []
    for window in (None, 2048):
        if window is None:
            lower.zero_()
        else:
            lower.copy_(upper - window)
        reference, counts = reference_for_bounds()
        references.append(reference.clone())
        workspace.native_status.zero_()
        eager = packed_attention_out(q, view, table, requests, lower, upper, SCALE, workspace).clone()
        eager_status = int(workspace.native_status.item())
        graph.replay()
        torch.cuda.synchronize()
        diff = (output.float() - reference.float()).abs()
        eager_diff = (eager.float() - reference.float()).abs()
        case = {
            "launch": "native_graph", "context": context, "window": window,
            "physical_pages": physical_pages, "last_page": last_page,
            "reference": "pytorch_dequantized_kv_full_multiplicity",
            "status": int(workspace.native_status.item()), "eager_status": eager_status,
            "write_status": write_status,
            "max_abs": float(diff.max()), "rmse": float(diff.square().mean().sqrt()),
            "within": bool((diff <= ATOL + RTOL * reference.float().abs()).all()
                           & (eager_diff <= ATOL + RTOL * reference.float().abs()).all()),
            "finite": bool(torch.isfinite(output).all() & torch.isfinite(eager).all()
                           & torch.isfinite(reference).all()),
        }
        case["passed"] = (write_status == case["status"] == case["eager_status"] == 0 and case["within"]
                          and case["finite"] and float(diff.square().mean().sqrt()) <= RMSE
                          and float(eager_diff.square().mean().sqrt()) <= RMSE)
        cases.append(case)
        if EVIDENCE is not None:
            EVIDENCE("native_context", {
                "q": q, "table": table, "requests": requests, "lower": lower, "upper": upper,
                "packed_tiles": packed_tiles, "raw_keys": keys, "raw_values": tail_values,
                "page_kinds": page_kinds, "counts": counts, "decoded_keys": oracle_keys,
                "decoded_values": oracle_values, "output": output, "eager": eager,
                "reference": reference,
            }, case)
    sensitive = bool((references[0][0].float() - references[1][0].float()).abs().min() > 0.25)
    if not sensitive:
        raise ValueError("Native fixture cannot detect missing far history")
    # The next physical page must fail in the captured native kernel and remain
    # sticky after the real last page is restored.
    table[0, logical_pages - 1] = physical_pages
    graph.replay()
    torch.cuda.synchronize()
    rejected_status = int(workspace.native_status.item())
    table[0, logical_pages - 1] = last_page
    graph.replay()
    torch.cuda.synchronize()
    sticky_status = int(workspace.native_status.item())
    boundary = {"case": "first_invalid_physical_page_and_sticky_status",
                "context": context, "physical_pages": physical_pages,
                "invalid_page": physical_pages, "rejected_status": rejected_status,
                "sticky_status": sticky_status,
                "passed": bool(rejected_status & 1 and sticky_status & 1)}
    if EVIDENCE is not None:
        EVIDENCE("native_context_status", {"table": table, "lower": lower, "upper": upper}, boundary)
    return cases, boundary



def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--context", type=int, choices=(245760, 262144), default=262144)
    args = parser.parse_args()
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
    native_cases, boundary = run_native_graph_cases(device, generator, args.context)
    cases.extend(native_cases)
    ok = all(c["status"] == 0 and c.get("eager_status", 0) == 0 and c["finite"] and c["within"] for c in cases)
    ok = ok and boundary["passed"] and all(case["passed"] for case in native_cases)
    print(json.dumps({"cases": cases, "boundary": boundary, "passed": ok}, indent=1))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
