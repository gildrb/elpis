# Obligations for the b/a GEMV of ext 5106 (gdn_conv_rule_norm_kernel<..., KS = 1, 2, ...>, the k split),
# over the Nat model gdn_ba_ksplit.bend against gdn_ba_ksplit_spec.bend. fp32 values are symbolic (Ex):
# equal values mean the same operations on the same operands in the same order, i.e. bit-identical
# results for any input data. Domains: every k2 (= k / 2, half2 elements per row), every head h and
# head count H, every batch-row count S; the thread grid is the kernel's 512 threads x GR_KS_ITERS = 5.
# Out of scope: overflow of the C ints (bounded in gdn_ba_ksplit.bend), memory ordering beyond the
# block barrier modelled in prog, the fp32 rounding itself.
#
# Relation to gdn_fast_laws.bend: task_exactly_once / task_decode(_range) describe 5101's per-warp GEMV
# (one (row, b|a) task per warp); that loop still runs as KS 0, the fallback below (fallback_ks0) and the
# EXL3_GDN_BA_KSPLIT=0 kill switch, so those laws keep holding for it unchanged. For the served b/a path
# (KS 2, S <= 8, k <= 5120) the laws of this module supersede them: every task is computed by all 512
# threads, element by element.
import Base
import ./gdn_ba_ksplit.bend as Impl
import ./gdn_ba_ksplit_spec.bend as Spec

# (1) Element ownership, into: thread t < 512 at iteration i < 5 handles half2 element t + 512 i of
# every row (both b/a weight rows and every x row), which lies in [0, 2560), and that element's
# reference owner is (t, i): no two (thread, iteration) pairs share an element.
law own_into:
  for +t: Nat
  for +i: Nat
  for tr: {Nat.is_lt(t, 512n) == True{} : Bool}
  for ir: {Nat.is_lt(i, 5n) == True{} : Bool}
  {Impl.ks_j(t, i) == Nat.add(t, Nat.mul(i, 512n)) : Nat} &
  {Nat.is_lt(Impl.ks_j(t, i), 2560n) == True{} : Bool} &
  {Spec.owner_t(Impl.ks_j(t, i)) == t : Nat} &
  {Spec.owner_i(Impl.ks_j(t, i)) == i : Nat}

# (1) ... onto: every half2 element j < 2560 (= 5120 halves, both components) is handled by its
# reference owner, a thread < 512 at an iteration < 5. With own_into: exactly one (warp t / 32, lane
# t % 32, i) per element. The kernel's `if (j < k2)` guard then drops exactly the elements j >= k2.
law own_onto:
  for +j: Nat
  for jr: {Nat.is_lt(j, 2560n) == True{} : Bool}
  {Nat.is_lt(Spec.owner_t(j), 512n) == True{} : Bool} &
  {Nat.is_lt(Spec.owner_i(j), 5n) == True{} : Bool} &
  {Impl.ks_j(Spec.owner_t(j), Spec.owner_i(j)) == j : Nat}

# (2) The per-thread chain: thread t's partial of task (row s, b|a) after the FMA loop, for any
# batch-row count S > s, is the reference chain: its elements t, t + 512, ... below k2 in ascending
# order, two fmaf each (.x then .y), starting from 0.0f. Independent of S and of every other row.
law chain_row:
  for +t: Nat
  for +S: Nat
  for +s: Nat
  for +ab: Nat
  for +k2: Nat
  for +h: Nat
  for +H: Nat
  for sr: {Nat.is_lt(s, S) == True{} : Bool}
  for s8: {Nat.is_lt(s, 8n) == True{} : Bool}
  {Impl.acc(t, S, s, ab, k2, h, H) == Spec.chain(t, s, ab, k2, h, H) : Impl.Ex}

# (2) The warp reduction: the kernel's __shfl_down_sync loop (offsets 16..1, lanes past 31 reading
# their own value) leaves in lane 0 the reference lane tree of the warp's 32 chains.
law warp_tree:
  for +w: Nat
  for +s: Nat
  for +ab: Nat
  for +k2: Nat
  for +h: Nat
  for +H: Nat
  {Impl.tree(Spec.clanes(32n, 0n, w, s, ab, k2, h, H)) == Spec.wtree(5n, 0n, w, s, ab, k2, h, H) : Impl.Ex}

# ... and that tree adds every lane 0..31 exactly once.
law tree_lanes_once:
  {Spec.perm32(Spec.tree_lanes(5n, 0n)) == True{} : Bool}

# (2, 3) The slot lane 0 of warp w writes for (row s, b|a) is the reference slot, the slot thread s
# reads for warp w, and decodes back to (w, b|a, s): each partial lands in its own slot and is read by
# the thread of its row.
law slot_decode:
  for +w: Nat
  for +s: Nat
  for +ab: Nat
  for s8: {Nat.is_lt(s, 8n) == True{} : Bool}
  for a2: {Nat.is_lt(ab, 2n) == True{} : Bool}
  {Impl.wslot(w, s, ab) == Spec.slot(w, s, ab) : Nat} &
  {Impl.rslot(w, s, ab) == Spec.slot(w, s, ab) : Nat} &
  {Impl.dec_w(Spec.slot(w, s, ab)) == w : Nat} &
  {Impl.dec_ab(Spec.slot(w, s, ab)) == ab : Nat} &
  {Impl.dec_s(Spec.slot(w, s, ab)) == s : Nat}

# (2, 3) The value thread s < S stores to ba_out and turns into beta / g: the reference sum of task
# (s, b|a), i.e. warps 0..15 in order from 0.0f, each the lane tree of its 32 chains, then the bias
# of the row's weight when present. It reads only partials written by this launch (no Stale), for
# every S > s: row invariant (one row's b/a does not depend on S or on the other rows).
law task_value:
  for +S: Nat
  for +s: Nat
  for +ab: Nat
  for +k2: Nat
  for +h: Nat
  for +H: Nat
  for +hb: Bool
  for sr: {Nat.is_lt(s, S) == True{} : Bool}
  for s8: {Nat.is_lt(s, 8n) == True{} : Bool}
  for a2: {Nat.is_lt(ab, 2n) == True{} : Bool}
  {Impl.task(S, s, ab, k2, h, H, hb) == Spec.value(s, ab, k2, h, H, hb) : Impl.Ex}

# (3) Barrier position: in the k-split kernel (KS 1, 2), for owner and non-owner blocks, the partial
# writes (lane 0, ks_part = m.dot2) are separated from the thread-s reads by a __syncthreads(), which
# comes after every warp's writes; the reads are separated from the token loop's m.dot2 writes by a
# __syncthreads(); each happens once.
law barrier_ksplit:
  for +ks: Nat
  for +own: Bool
  for k1: {Nat.is_lt(0n, ks) == True{} : Bool}
  for k3: {Nat.is_lt(ks, 3n) == True{} : Bool}
  {Spec.fenced(Impl.PartW{}, Impl.PartR{}, Impl.prog(ks, own)) == True{} : Bool} &
  {Spec.fenced(Impl.PartR{}, Impl.Dot2W{}, Impl.prog(ks, own)) == True{} : Bool} &
  {Spec.count(Impl.PartW{}, Impl.prog(ks, own)) == 1n : Nat} &
  {Spec.count(Impl.PartR{}, Impl.prog(ks, own)) == 1n : Nat}

# (3) KS 0 (5101): the per-warp GEMV's m.ba writes precede its reads across a __syncthreads().
law barrier_ks0:
  for +own: Bool
  {Spec.fenced(Impl.Gemv{}, Impl.PartR{}, Impl.prog(0n, own)) == True{} : Bool}

# (4) Fallback: more than 8 rows or more than 2560 half2 per row run the per-warp GEMV (KS 0);
# otherwise the selected variant runs.
law fallback_ks0:
  for +ks: Nat
  for +S: Nat
  for +k: Nat
  for big: {Bool.or(Nat.is_lt(8n, S), Nat.is_lt(2560n, Nat.div(k, 2n))) == True{} : Bool}
  {Impl.variant(ks, S, k) == 0n : Nat}

law covered_ks:
  for +ks: Nat
  for +S: Nat
  for +k: Nat
  for s8: {Nat.is_le(S, 8n) == True{} : Bool}
  for k2: {Nat.is_le(Nat.div(k, 2n), 2560n) == True{} : Bool}
  {Impl.variant(ks, S, k) == ks : Nat}
