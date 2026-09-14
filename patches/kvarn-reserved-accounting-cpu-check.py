import hashlib, inspect, json, sys
from pathlib import Path
import torch

from sglang.srt.mem_cache.allocator.paged import PagedTokenToKVPoolAllocator
from sglang.srt.mem_cache.kvarn_allocator import KVarNPageAllocator
from sglang.srt.managers.scheduler_components.invariant_checker import (
    SchedulerInvariantChecker,
)

cases = []
def case(name, ok):
    cases.append({"name": name, "ok": bool(ok)})
    if not ok:
        print("FAIL:", name, file=sys.stderr)

class _StubKVCache:
    pass

# 1. Stock paged allocator: default reserved accounting is zero.
paged = PagedTokenToKVPoolAllocator(1024, 128, torch.float32, "cpu", _StubKVCache(), False)
case("stock paged allocator reserves nothing", paged.reserved_size() == 0)
case("stock paged allocator fully available", paged.available_size() == 1024)

# 2. Real KVarN allocator on CPU tensors: reservation arithmetic.
kvarn = KVarNPageAllocator(1024, 128, torch.float32, "cpu", _StubKVCache(), False)
case("kvarn unreserved reports zero", kvarn.reserved_size() == 0)
locs = kvarn.reserve_graph_dummy_page()
case("reservation removes exactly one page", kvarn.available_size() == 1024 - 128)
case("reservation reports 128 tokens", kvarn.reserved_size() == 128)
case("reserved locations span one page", int(locs[0]) // 128 == int(locs[-1]) // 128)
again = kvarn.reserve_graph_dummy_page()
case("reservation is idempotent", again is locs and kvarn.reserved_size() == 128)

# 3. Lifetime enforcement is unchanged: freeing the dummy page still raises.
freed_guard = False
try:
    kvarn._release_page_ids(torch.tensor([int(locs[0]) // 128], dtype=torch.int64))
except ValueError:
    freed_guard = True
case("freeing reserved page still raises", freed_guard)

# 4. clear() keeps the reservation carved out and accounted.
kvarn.clear()
case("clear keeps one page reserved", kvarn.available_size() == 1024 - 128)
case("clear keeps reservation reported", kvarn.reserved_size() == 128)

# 5. Real checker: stage13 arithmetic reproduced without reserved (negative control).
leak_neg, msg_neg = SchedulerInvariantChecker._check_pool_invariant(
    "full", 263040, 0, 0, 0, 263168,
)
case("pre-fix arithmetic still leaks 128", leak_neg and "263040" in msg_neg)

# 6. Real checker: same numbers with reserved accounted.
leak_fix, msg_fix = SchedulerInvariantChecker._check_pool_invariant(
    "full", 263040, 0, 0, 0, 263168, 0, 128,
)
case("reserved accounting closes the leak", not leak_fix)
case("message reports reserved", "reserved=128" in msg_fix)

# 7. Busy-path arithmetic: sessions plus reservation stay exact.
leak_busy, _msg_busy = SchedulerInvariantChecker._check_pool_invariant(
    "full", 262912, 0, 0, 128, 263168, 0, 128,
)
case("busy conservation with reserved exact", not leak_busy)

# 8. End-to-end _check_full_pool on the hybrid-ssm branch with real allocator.
class _TreeCache:
    def supports_mamba(self):
        return True
    def full_protected_size(self):
        return 0
class _Observer:
    def session_held_tokens(self):
        return 0
    def session_held_full_tokens(self):
        return 0
class _PoolStats:
    full_available_size = kvarn.available_size()
    full_evictable_size = 0
class _ReqPool:
    size = 1024
    def schedulable_token_capacity(self, physical_capacity):
        return physical_capacity
checker = SchedulerInvariantChecker(
    is_hybrid_swa=False,
    is_hybrid_ssm=True,
    disaggregation_mode=None,
    page_size=128,
    full_tokens_per_layer=None,
    swa_tokens_per_layer=None,
    max_total_num_tokens=1024,
    tree_cache=_TreeCache(),
    token_to_kv_pool_allocator=kvarn,
    req_to_token_pool=_ReqPool(),
    pool_stats_observer=_Observer(),
    get_last_batch=lambda: None,
    get_running_batch=lambda: None,
)
full_leak, full_msg = checker._check_full_pool(_PoolStats())
case("hybrid-ssm idle check passes with reservation", not full_leak)
case("full check reports reserved=128", "reserved=128" in full_msg)

# 9. Non-regression: stock allocator through the same path.
checker_stock = SchedulerInvariantChecker(
    is_hybrid_swa=False,
    is_hybrid_ssm=True,
    disaggregation_mode=None,
    page_size=128,
    full_tokens_per_layer=None,
    swa_tokens_per_layer=None,
    max_total_num_tokens=1024,
    tree_cache=_TreeCache(),
    token_to_kv_pool_allocator=paged,
    req_to_token_pool=_ReqPool(),
    pool_stats_observer=_Observer(),
    get_last_batch=lambda: None,
    get_running_batch=lambda: None,
)
class _PoolStatsStock:
    full_available_size = paged.available_size()
    full_evictable_size = 0
stock_leak, stock_msg = checker_stock._check_full_pool(_PoolStatsStock())
case("stock allocator idle check unchanged", not stock_leak)
case("stock message reports reserved=0", "reserved=0" in stock_msg)

# 10. Source-level guards on all three patched files.
inv_src = inspect.getsource(SchedulerInvariantChecker._check_pool_invariant)
case("invariant formula includes reserved",
     "uncached + reserved" in inv_src and "reserved: int = 0" in inv_src)
full_src = inspect.getsource(SchedulerInvariantChecker._check_full_pool)
case("full check sources reserved from allocator",
     "allocator.reserved_size()" in full_src)
case("base default reserved is zero",
     PagedTokenToKVPoolAllocator(256, 128, torch.float32, "cpu", _StubKVCache(), False).reserved_size() == 0)
kv_src = inspect.getsource(KVarNPageAllocator.reserved_size)
case("kvarn override reads dummy locations", "_graph_dummy_locations" in kv_src)

passed = sum(1 for c in cases if c["ok"]) == len(cases)
out = {
    "status": "passed-cpu-only" if passed else "failed",
    "cases": len(cases),
    "case_detail": cases,
}
Path("/work/out/cpu-check.json").write_text(json.dumps(out, indent=1))
print(json.dumps({"passed": passed, "cases": len(cases)}))
sys.exit(0 if passed else 1)
