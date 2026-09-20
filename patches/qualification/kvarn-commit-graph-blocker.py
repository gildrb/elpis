#!/usr/bin/env python3
# B2 ON-arm blocker reproduction: the stage22 `_KVarNCommitGraphRunner`
# (imported from the deployed dflash_worker_v2) driven end-to-end through a
# duck-typed worker against real qualified KVarN pools (target 16x D256 KV4,
# draft 5x D128 KV8, capture mode, allocator-style shared dummy page).
#
# Cases:
#   A  live-first-step emulation: verify-style staging -> runner capture ->
#      eager fallback commit -> replay. Expect PASS (status 0, rows committed).
#   B  THE BLOCKER: commit graph replay against rows NEVER staged provisional
#      -> expect sticky status bits=1 and NO rows committed (fail-closed).
#   C  warmup-only neutrality: ensure_capture on clean pools without any
#      staging -> expect status 0 (isolates whether warmup itself trips).
#   D  bit-4 independence: raw-slot exhaustion still fails closed with its
#      own bit after a B-style failure was cleared.
# Native admission/last-page cases additionally exercise the exact physical pool,
# allocator-owned dummy reservation and measured eager/graph committed KV parity.
import argparse
import json
import sys
from types import SimpleNamespace
from unittest.mock import patch

import torch

from sglang.srt.layers.attention.kvarn_backend import KVarNAttnBackend
from sglang.srt.mem_cache.kvarn.layout import KVarNLayout
from sglang.srt.mem_cache.kvarn.pool import KVarNTokenToKVPool
from sglang.srt.mem_cache.kvarn.types import KVarNCapacity
from sglang.srt.mem_cache.kvarn_allocator import KVarNPageAllocator
from sglang.srt.mem_cache.kvarn_budget import qualification_page_count
from sglang.srt.mem_cache.kv_cache_configurator import KVCacheConfigurator
from sglang.srt.mem_cache.memory_pool import HybridLinearKVPool
from sglang.srt.speculative.dflash_worker_v2 import DFlashWorkerV2, _KVarNCommitGraphRunner
from sglang.kernels.ops.kvarn.store import begin_write_out

DUMMY_PAGE = 1
HIDDEN = 512
REVIEWED = "e2f2c7311d93d240311fa3280c2c65fafaf93f8b4a3fcf9ac095d28b614291cd"

EVIDENCE = None


class _Full:
    def __init__(self, pool):
        self.full_kv_pool = pool


class _MockHybrid(HybridLinearKVPool):
    def __init__(self, pool):  # noqa: D107 - bypass the heavy parent init
        self.full_kv_pool = pool


class _Runner:
    def __init__(self, pool, device):
        self.token_to_kv_pool = pool
        self.device = device


class _Attn:
    def __init__(self, layer_id, kv_heads, head_dim, device):
        self.attn = self
        self.layer_id = layer_id
        self.num_kv_heads = kv_heads
        self.head_dim = head_dim
        self.proj = torch.nn.Linear(HIDDEN, 2 * kv_heads * head_dim, dtype=torch.bfloat16, device=device)

    def kv_proj_only(self, ctx):
        out = self.proj(ctx)
        k = out[..., : self.num_kv_heads * self.head_dim].contiguous()
        v = out[..., self.num_kv_heads * self.head_dim :].contiguous()
        return k, v

    def apply_k_norm(self, k):
        return k

    def apply_k_rope(self, positions, k):
        return k


class _Layer:
    def __init__(self, attn):
        self.self_attn = attn


class _DraftModel:
    def __init__(self, layers, device):
        self.layers = [_Layer(attn) for attn in layers]
        self.project = torch.nn.Linear(HIDDEN, HIDDEN, dtype=torch.bfloat16, device=device)

    def project_target_hidden(self, hidden):
        return self.project(hidden)

    def prepare_context_hidden_for_kv(self, layer, ctx_hidden):
        return ctx_hidden


class MockWorker:
    _kvarn_pools = DFlashWorkerV2._kvarn_pools
    _write_committed_draft_block = DFlashWorkerV2._write_committed_draft_block
    _append_target_hidden_to_draft_kv_by_loc = (
        DFlashWorkerV2._append_target_hidden_to_draft_kv_by_loc
    )

    def __init__(self, target_pool, draft_pool, device):
        self.block_size = 8
        self.device = device
        self.model_runner = _Runner(_MockHybrid(target_pool), device)
        self.draft_model_runner = _Runner(draft_pool, device)
        self.draft_model = _DraftModel(
            [_Attn(i, 8, 128, device) for i in range(5)], device
        )
        self._draft_verify_out_cache_loc_buf = torch.zeros((4, 8), dtype=torch.int64, device=device)
        self._draft_block_positions_buf = torch.zeros((4, 8), dtype=torch.int64, device=device)


def build_pools(device: str, capacity: int) -> tuple[KVarNTokenToKVPool, KVarNTokenToKVPool]:
    dummy = torch.tensor([DUMMY_PAGE], dtype=torch.int64, device=device)
    target = KVarNTokenToKVPool(
        KVarNLayout(head_dim=256, kv_heads=4, layer_ids=tuple(range(16))),
        KVarNCapacity(token_capacity=capacity, tail_slots=8, max_write_tokens=128,
                      max_query_tokens=32, max_visible_tokens=128,
                      workspace_bytes=64 * 1024 * 1024),
        torch.bfloat16, device, max_query_heads=24,
    )
    target.register_graph_dummy_pages(dummy)
    target.enable_qualification_mode(profile="target_sm86_bf16",
                                     reviewed_inventory_sha256=REVIEWED, capture=True)
    draft = KVarNTokenToKVPool(
        KVarNLayout(head_dim=128, kv_heads=8, layer_ids=tuple(range(5))),
        KVarNCapacity(token_capacity=capacity, tail_slots=8, max_write_tokens=128,
                      max_query_tokens=32, max_visible_tokens=2304,
                      workspace_bytes=64 * 1024 * 1024),
        torch.bfloat16, device, max_query_heads=32,
    )
    draft.register_graph_dummy_pages(dummy)
    draft.enable_qualification_mode(profile="draft_sm86_bf16",
                                    reviewed_inventory_sha256=REVIEWED, capture=True)
    return target, draft


def stage_block(pool, page, device, seed, offset=0):
    generator = torch.Generator(device=device)
    generator.manual_seed(seed)
    keys = torch.randn((8, 4, 256), generator=generator, device=device, dtype=torch.float32).to(torch.bfloat16)
    values = torch.randn((8, 4, 256), generator=generator, device=device, dtype=torch.float32).to(torch.bfloat16)
    locs = torch.arange(page * 128 + offset, page * 128 + offset + 8, device=device, dtype=torch.int64)
    for layer_id in pool.layout.layer_ids:
        begin_write_out(pool.layer_view(layer_id), locs, keys, values, True, pool.workspace)


def status_of(pool):
    torch.cuda.synchronize()
    return int(pool.workspace.native_status.item())


def committed_state(pool: KVarNTokenToKVPool, page: int) -> list[dict[str, torch.Tensor]]:
    """Observe only valid KV, never uninitialized raw/packed capacity."""
    states = []
    for layer_id in pool.layout.layer_ids:
        view = pool.layer_view(layer_id)
        slot = int(view.page_to_tail_slot[page].item())
        mask = view.committed_mask[page]
        if slot < 0 and bool(mask.any()):
            raise RuntimeError("Committed fixture page lost raw backing")
        empty_shape = (0, pool.layout.kv_heads, pool.layout.head_dim)
        states.append({
            "mask": mask.clone(),
            "provisional": view.provisional_mask[page].clone(),
            "length": view.valid_lengths[page].clone(),
            "keys": view.raw_keys[slot, mask].clone() if slot >= 0 else view.raw_keys.new_empty(empty_shape),
            "values": view.raw_values[slot, mask].clone() if slot >= 0 else view.raw_values.new_empty(empty_shape),
        })
    return states


def native_geometry_cases(device: str, capacity: int) -> list[dict[str, object]]:
    results: list[dict[str, object]] = []
    pages = qualification_page_count(capacity, capture=True)
    cfg = SimpleNamespace(kernel=SimpleNamespace(kvarn_qualification_mode="graph"))
    # Drive the real constructor entry, before any pool allocation: a smaller
    # admitted rung must still fail exact allocated-vs-requested equality.
    for allocated, requested in ((capacity - 128, capacity), (246784, 263168)):
        rejected = False
        with patch("sglang.srt.mem_cache.kv_cache_configurator.get_exec", return_value=cfg), patch(
            "sglang.srt.mem_cache.kv_cache_configurator.get_schedule",
            return_value=SimpleNamespace(max_total_tokens=requested),
        ):
            try:
                KVCacheConfigurator._build_kvarn_token_pool(
                    object(), max_total_num_tokens=allocated, req_to_token_pool=None,
                )
            except ValueError:
                rejected = True
        results.append({"case": "pool_shortfall", "allocated": allocated, "requested": requested,
                        "passed": rejected})

    target, draft = build_pools(device, capacity)
    allocator = KVarNPageAllocator(capacity, 128, torch.bfloat16, device, target, False)
    dummy = allocator.reserve_graph_dummy_page()
    dummy_page = int(dummy[0].item()) // 128
    release_rejected = False
    try:
        allocator.free(dummy)
    except ValueError:
        release_rejected = True
    remaining = allocator.alloc(capacity - 128)
    reserved_ok = (
        dummy_page == DUMMY_PAGE
        and allocator.reserved_size() == 128
        and remaining is not None
        and not bool((remaining // 128 == dummy_page).any())
        and int(remaining.max().item()) == pages * 128 - 1
        and allocator.alloc(128) is None
        and release_rejected
    )
    allocator.clear()
    reserved_ok = reserved_ok and allocator.available_size() == capacity - 128
    results.append({"case": "dummy_lifetime_and_last_page", "pages": pages,
                    "last_physical_token": pages * 128 - 1, "passed": bool(reserved_ok)})
    backend = SimpleNamespace(
        pool=target, _allocator=allocator,
        req_to_token=torch.empty((1, capacity - 1024), device=device, dtype=torch.int64),
        _page_table=torch.empty((1, (capacity - 1024) // 128), device=device, dtype=torch.int64),
    )
    KVarNAttnBackend.init_cuda_graph_state(backend, 1, 8)
    for width in ((capacity - 1024) // 128 - 1, pages):
        backend._page_table = torch.empty((1, width), device=device, dtype=torch.int64)
        rejected = False
        try:
            KVarNAttnBackend.init_cuda_graph_state(backend, 1, 8)
        except ValueError:
            rejected = True
        results.append({"case": "graph_table_geometry_rejection", "columns": width,
                        "passed": rejected})

    worker = MockWorker(target, draft, device)
    last_page = pages - 1
    worker._draft_verify_out_cache_loc_buf[0] = torch.arange(
        last_page * 128 + 120, last_page * 128 + 128, device=device, dtype=torch.int64)
    worker._draft_block_positions_buf[0] = torch.arange(
        capacity - 1024 - 8, capacity - 1024, device=device, dtype=torch.int64)
    hidden = torch.randn((8, HIDDEN), device=device, dtype=torch.bfloat16)
    runner = _KVarNCommitGraphRunner(worker)
    lens = torch.zeros((1,), device=device, dtype=torch.int32)
    prefix_page = last_page - 1
    stage_block(target, prefix_page, device, 709)
    prefix_locations = torch.arange(prefix_page * 128, prefix_page * 128 + 8,
                                    device=device, dtype=torch.int64).view(1, 8)
    prefix_lens = torch.ones((1,), device=device, dtype=torch.int32)
    for layer_id in target.layout.layer_ids:
        target.commit_prefix(layer_id, prefix_locations, prefix_lens)
    before_capture = committed_state(target, prefix_page)
    runner.ensure_capture(commit_lens=lens, hidden=hidden)
    target.check_native_status()
    draft.check_native_status()
    after_capture = committed_state(target, prefix_page)
    neutral = all(
        torch.equal(before[field], after[field])
        for before, after in zip(before_capture, after_capture, strict=True)
        for field in before
    )
    results.append({"case": "capture_preserves_committed_prefix", "passed": neutral})
    if EVIDENCE is not None:
        EVIDENCE("capture_prefix", {"before": before_capture, "after": after_capture,
                 "hidden": hidden}, {"page": prefix_page, "capacity": capacity,
                 "target_status": status_of(target), "draft_status": status_of(draft)})
    for offset, start_page in ((120, last_page), (124, last_page - 1)):
        observed_pages = list(range(start_page, (start_page * 128 + offset + 7) // 128 + 1))
        worker._draft_verify_out_cache_loc_buf[0] = torch.arange(
            start_page * 128 + offset, start_page * 128 + offset + 8,
            device=device, dtype=torch.int64)
        for accepted in range(9):
            observations = []
            statuses = []
            lens.fill_(accepted)
            for captured in (False, True):
                target.clear()
                draft.clear()
                stage_block(target, start_page, device, 710, offset=offset)
                if captured:
                    runner.replay(commit_lens=lens, hidden=hidden)
                else:
                    if runner.commit_lens_buf is None or runner.hidden_buf is None:
                        raise RuntimeError("Commit capture did not initialize static buffers")
                    runner.commit_lens_buf.copy_(lens)
                    runner.hidden_buf.copy_(hidden)
                    runner._run_region()
                target.check_native_status()
                draft.check_native_status()
                statuses.append({"target": status_of(target), "draft": status_of(draft)})
                observations.append([
                    state for page in observed_pages
                    for pool in (target, draft) for state in committed_state(pool, page)
                ])
            maximum = 0.0
            matches = True
            for index, (eager, graph) in enumerate(zip(*observations, strict=True)):
                page = observed_pages[index // 21]
                expected_mask = torch.zeros(128, device=device, dtype=torch.bool)
                first = start_page * 128 + offset
                for location in range(first, first + accepted):
                    if location // 128 == page:
                        expected_mask[location % 128] = True
                matches &= torch.equal(graph["mask"], expected_mask)
                matches &= torch.equal(eager["mask"], expected_mask)
                for field in ("mask", "provisional", "length"):
                    matches &= torch.equal(eager[field], graph[field])
                for field in ("keys", "values"):
                    left, right = eager[field].float(), graph[field].float()
                    matches &= bool(torch.isfinite(left).all() & torch.isfinite(right).all())
                    matches &= bool(torch.allclose(left, right, atol=0.0009765625, rtol=0.0078125))
                    if left.numel():
                        maximum = max(maximum, float((left - right).abs().max()))
            results.append({"case": "last_page_commit_graph_eager_parity", "accepted": accepted,
                            "page": start_page, "offset": offset, "pages": observed_pages,
                            "max_abs": maximum, "passed": bool(matches)})
            if EVIDENCE is not None:
                EVIDENCE("commit", {"eager": observations[0], "graph": observations[1],
                         "hidden": hidden, "locations": worker._draft_verify_out_cache_loc_buf[:1],
                         "positions": worker._draft_block_positions_buf[:1]},
                         {"accepted": accepted, "page": start_page, "offset": offset,
                          "pages": observed_pages, "capacity": capacity, "statuses": statuses,
                          "target_status": status_of(target), "draft_status": status_of(draft)})
    return results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--context", type=int, choices=(245760, 262144), default=262144)
    args = parser.parse_args()
    capacity = args.context + 1024
    block_page = capacity // 128 - 2
    if not torch.cuda.is_available():
        print("cuda required", file=sys.stderr)
        return 2
    device = "cuda"
    torch.manual_seed(20260919)
    results = native_geometry_cases(device, capacity)

    # ---- Case A: live-first-step emulation (staged, capture, eager, replay)
    target, draft = build_pools(device, capacity)
    worker = MockWorker(target, draft, device)
    worker._draft_verify_out_cache_loc_buf[0] = torch.arange(
        block_page * 128, block_page * 128 + 8, device=device, dtype=torch.int64)
    worker._draft_block_positions_buf[0] = torch.arange(8, device=device, dtype=torch.int64)
    stage_block(target, block_page, device, 11)
    runner = _KVarNCommitGraphRunner(worker)
    hidden = torch.randn((8, HIDDEN), device=device, dtype=torch.bfloat16)
    lens = torch.tensor([3], device=device, dtype=torch.int32)
    try:
        runner.ensure_capture(commit_lens=lens, hidden=hidden)
        capture_err = None
    except Exception as error:  # noqa: BLE001
        capture_err = repr(error)
    case_a = {"case": "A_staged_capture_eager_replay", "capture_error": capture_err}
    if capture_err is None:
        # First-step eager fallback commit on the staged block...
        for layer_id in target.layout.layer_ids:
            target.commit_prefix(layer_id, worker._draft_verify_out_cache_loc_buf[:1], lens)
        # ...then the SECOND step replays on a freshly staged page (the live
        # per-step cadence; replaying over the already-committed block would
        # double-commit and correctly trip the immutable guard).
        replay_page = block_page + 2
        stage_block(target, replay_page, device, 13)
        worker._draft_verify_out_cache_loc_buf[0] = torch.arange(
            replay_page * 128, replay_page * 128 + 8, device=device, dtype=torch.int64)
        runner.replay(commit_lens=lens, hidden=hidden)
        torch.cuda.synchronize()
        view = target.layer_view(0)
        case_a["committed_rows_first"] = int(view.committed_mask[block_page].sum().item())
        case_a["committed_rows_replay"] = int(view.committed_mask[replay_page].sum().item())
        case_a["status"] = status_of(target)
        case_a["draft_status"] = status_of(draft)
        case_a["passed"] = (case_a["status"] == 0 and case_a["draft_status"] == 0
                            and case_a["committed_rows_first"] == 3
                            and case_a["committed_rows_replay"] == 3)
    else:
        case_a["passed"] = False
    results.append(case_a)
    del target, draft, worker, runner
    torch.cuda.empty_cache()

    # ---- Case B: THE BLOCKER - replay against never-staged rows
    target, draft = build_pools(device, capacity)
    worker = MockWorker(target, draft, device)
    worker._draft_verify_out_cache_loc_buf[0] = torch.arange(
        block_page * 128, block_page * 128 + 8, device=device, dtype=torch.int64)
    worker._draft_block_positions_buf[0] = torch.arange(8, device=device, dtype=torch.int64)
    runner = _KVarNCommitGraphRunner(worker)
    hidden = torch.randn((8, HIDDEN), device=device, dtype=torch.bfloat16)
    lens = torch.tensor([5], device=device, dtype=torch.int32)
    case_b = {"case": "B_unstaged_replay_blocker"}
    try:
        runner.ensure_capture(commit_lens=lens, hidden=hidden)
        runner.replay(commit_lens=lens, hidden=hidden)
        torch.cuda.synchronize()
        case_b["status_target"] = status_of(target)
        case_b["status_draft"] = status_of(draft)
        view = target.layer_view(0)
        case_b["committed_rows"] = int(view.committed_mask[block_page].sum().item())
        raised = None
        try:
            target.check_native_status()
        except RuntimeError as error:
            raised = str(error)
        case_b["gate_raised"] = raised
        case_b["fail_closed"] = (case_b["committed_rows"] == 0 and case_b["status_target"] != 0)
        case_b["passed"] = bool(case_b["fail_closed"] and case_b["gate_raised"])
    except Exception as error:  # noqa: BLE001
        case_b["error"] = repr(error)
        case_b["passed"] = False
    results.append(case_b)

    # ---- Case D (same pools as B): capacity bit independence after clearing
    target.workspace.native_status.zero_()
    draft.workspace.native_status.zero_()
    view = target.layer_view(0)
    for slot in range(8):
        view.tail_to_page[slot] = slot + 1
    torch.cuda.synchronize()
    stage_block(target, block_page + 1, device, 12)
    case_d = {"case": "D_bit4_independent_after_blocker"}
    try:
        target.check_native_status()
        case_d["gate_raised"] = None
        case_d["passed"] = False
    except RuntimeError as error:
        case_d["gate_raised"] = str(error)
        case_d["bit4"] = (status_of(target) & 4) != 0
        case_d["passed"] = bool(case_d["bit4"] and "raw-slot pressure" in case_d["gate_raised"])
    results.append(case_d)
    del target, draft, worker, runner
    torch.cuda.empty_cache()

    # ---- Case E: FIXED ORDER - capture BEFORE staging, then stage, commit,
    # and replay exactly like the live step cadence after the reorder.
    target, draft = build_pools(device, capacity)
    worker = MockWorker(target, draft, device)
    worker._draft_verify_out_cache_loc_buf[0] = torch.arange(
        block_page * 128, block_page * 128 + 8, device=device, dtype=torch.int64)
    worker._draft_block_positions_buf[0] = torch.arange(8, device=device, dtype=torch.int64)
    hidden = torch.randn((8, HIDDEN), device=device, dtype=torch.bfloat16)
    lens = torch.tensor([4], device=device, dtype=torch.int32)
    case_e = {"case": "E_capture_before_staging_fixed_order"}
    try:
        # 1) capture on clean pools (decode-branch start, pre-staging)
        runner = _KVarNCommitGraphRunner(worker)
        runner.ensure_capture(commit_lens=lens, hidden=hidden)
        # 2) the step's verify-side staging
        stage_block(target, block_page, device, 21)
        # 3) first-step eager fallback commit on the staged block
        for layer_id in target.layout.layer_ids:
            target.commit_prefix(layer_id, worker._draft_verify_out_cache_loc_buf[:1], lens)
        # 4) second step: stage a fresh block, replay
        replay_page = block_page + 2
        stage_block(target, replay_page, device, 22)
        worker._draft_verify_out_cache_loc_buf[0] = torch.arange(
            replay_page * 128, replay_page * 128 + 8, device=device, dtype=torch.int64)
        runner.replay(commit_lens=lens, hidden=hidden)
        torch.cuda.synchronize()
        view = target.layer_view(0)
        case_e["committed_first"] = int(view.committed_mask[block_page].sum().item())
        case_e["committed_replay"] = int(view.committed_mask[replay_page].sum().item())
        case_e["status"] = status_of(target)
        case_e["draft_status"] = status_of(draft)
        case_e["passed"] = (case_e["status"] == 0 and case_e["draft_status"] == 0
                            and case_e["committed_first"] == 4
                            and case_e["committed_replay"] == 4)
    except Exception as error:  # noqa: BLE001
        case_e["error"] = repr(error)
        case_e["passed"] = False
    results.append(case_e)
    del target, draft, worker
    torch.cuda.empty_cache()

    # ---- Case F: REAL TAIL emulation - capture early, verify-stage, replay,
    # then the worker's UNCONDITIONAL eager append (stage22 tail). The replay
    # already contains the draft append; re-running begin_write on rows the
    # replay committed must trip the immutable guard: the live 'after replay'
    # status bits=1.
    def run_real_tail(skip_append_when_replayed):
        target, draft = build_pools(device, capacity)
        worker = MockWorker(target, draft, device)
        worker._draft_verify_out_cache_loc_buf[0] = torch.arange(
            block_page * 128, block_page * 128 + 8, device=device, dtype=torch.int64)
        worker._draft_block_positions_buf[0] = torch.arange(8, device=device, dtype=torch.int64)
        lens = torch.tensor([5], device=device, dtype=torch.int32)
        # decode-branch start: capture on clean pools
        runner = _KVarNCommitGraphRunner(worker)
        runner.ensure_capture(commit_lens=lens, hidden=torch.randn((8, HIDDEN), device=device, dtype=torch.bfloat16))
        # verify-side staging (the verify graph's begin_write)
        stage_block(target, block_page, device, 31)
        replayed = runner.matches(commit_lens=lens, hidden=torch.randn((8, HIDDEN), device=device, dtype=torch.bfloat16))
        if replayed:
            runner.replay(commit_lens=lens, hidden=torch.randn((8, HIDDEN), device=device, dtype=torch.bfloat16))
        if not (replayed and skip_append_when_replayed):
            # the worker tail's unconditional append call
            worker._append_target_hidden_to_draft_kv_by_loc(
                target_hidden=torch.randn((8, HIDDEN), device=device, dtype=torch.bfloat16),
                cache_loc=worker._draft_verify_out_cache_loc_buf[0].reshape(-1),
                cache_loc_2d=worker._draft_verify_out_cache_loc_buf[:1],
                positions=worker._draft_block_positions_buf[0].reshape(-1),
                commit_lens=lens,
                may_have_pos0=False,
            )
        torch.cuda.synchronize()
        return target, draft, replayed

    case_f = {"case": "F_real_tail_unconditional_append"}
    target, draft, replayed_f = run_real_tail(skip_append_when_replayed=False)
    case_f["replayed"] = replayed_f
    case_f["status_target"] = status_of(target)
    case_f["status_draft"] = status_of(draft)
    raised_f = None
    try:
        target.check_native_status()
    except RuntimeError as error:
        raised_f = str(error)
    raised_fd = None
    try:
        draft.check_native_status()
    except RuntimeError as error:
        raised_fd = str(error)
    case_f["gate_raised_target"] = raised_f
    case_f["gate_raised_draft"] = raised_fd
    case_f["passed"] = bool(
        replayed_f
        and (case_f["status_target"] != 0 or case_f["status_draft"] != 0)
        and (raised_f or raised_fd)
    )
    results.append(case_f)
    del target, draft
    torch.cuda.empty_cache()

    # ---- Case G: the FIX - replayed steps skip the eager append
    case_g = {"case": "G_real_tail_gated_append_fix"}
    target, draft, replayed_g = run_real_tail(skip_append_when_replayed=True)
    case_g["replayed"] = replayed_g
    case_g["status_target"] = status_of(target)
    case_g["status_draft"] = status_of(draft)
    view = target.layer_view(0)
    case_g["target_committed_rows"] = int(view.committed_mask[block_page].sum().item())
    draft_view = draft.layer_view(0)
    case_g["draft_committed_rows"] = int(draft_view.committed_mask[block_page].sum().item())
    case_g["passed"] = bool(
        replayed_g
        and case_g["status_target"] == 0
        and case_g["status_draft"] == 0
        and case_g["target_committed_rows"] == 5
        and case_g["draft_committed_rows"] == 5
    )
    results.append(case_g)
    del target, draft
    torch.cuda.empty_cache()

    # ---- Case C: warmup-only neutrality (no staging anywhere)
    target, draft = build_pools(device, capacity)
    worker = MockWorker(target, draft, device)
    worker._draft_verify_out_cache_loc_buf[0] = torch.arange(
        block_page * 128, block_page * 128 + 8, device=device, dtype=torch.int64)
    worker._draft_block_positions_buf[0] = torch.arange(8, device=device, dtype=torch.int64)
    runner = _KVarNCommitGraphRunner(worker)
    hidden = torch.randn((8, HIDDEN), device=device, dtype=torch.bfloat16)
    lens = torch.tensor([0], device=device, dtype=torch.int32)
    case_c = {"case": "C_warmup_only_neutral"}
    try:
        runner.ensure_capture(commit_lens=lens, hidden=hidden)
        torch.cuda.synchronize()
        case_c["status_target"] = status_of(target)
        case_c["status_draft"] = status_of(draft)
        case_c["empty_masks"] = all(
            not bool(view.committed_mask.any() | view.provisional_mask.any())
            and not bool(view.valid_lengths.any() | view.preview_ready.any())
            for pool in (target, draft) for view in pool._views.values()
        )
        case_c["passed"] = (case_c["status_target"] == 0 and case_c["status_draft"] == 0
                            and case_c["empty_masks"])
    except Exception as error:  # noqa: BLE001
        case_c["error"] = repr(error)
        case_c["passed"] = False
    results.append(case_c)

    # Case A is the live-order repro and MUST fail exactly like the shipped
    # bug (warmup discard wipes staging); a PASS from A would mean the repro
    # no longer exercises the defect. Case F uses detector semantics instead:
    # its passed=true means the tail defect was reproduced (status bit set,
    # gate raised). B/C/D/E/G must pass outright.
    must_fail = {"A_staged_capture_eager_replay"}
    ok = all(
        (case["passed"] is False and case.get("capture_error") is None
         and (case.get("status", 0) != 0 or case.get("draft_status", 0) != 0))
        if case["case"] in must_fail else case["passed"]
        for case in results
    )
    print(json.dumps({"context": args.context, "pool_tokens": capacity, "cases": results,
                      "expected": "A live-order repro FAIL, B fail-closed, C neutral, D bit4, E fixed-order PASS, F real-tail unconditional append FAILS (live repro), G gated-append FIX PASSES",
                      "passed": ok}, indent=1))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
