# Semantic obligations for the work partition and deterministic split-K reduction of the
# EXL3 m16 swap-AB GEMM (patches/exl3-ext/2001-gemm-m16-swapab.patch). Quantified over every
# shape: mats matrices, k >= 128 (KT = k / 16 k-tiles; covers every multiple of 128), any n
# (NG = n / 128 groups per matrix) and any grid G >= 1; I = Impl.total(mats, n, k).
# Nat model of the C int expressions: overflow, the memory model (__threadfence / atomicAdd
# visibility), cp.async and fp32 values are outside this contract (see the module headers).
import Base
import ./gemm_m16_partition.bend as Impl
import ./gemm_m16_partition_spec.bend as Spec

# (1) Partition. Every iteration x < I has exactly one owning block (spec: division-free).
law owners_exactly_one:
  for +mats: Nat
  for +n: Nat
  for +k: Nat
  for +G: Nat
  for +x: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for inside: {Nat.is_lt(x, Impl.total(mats, n, k)) == True{} : Bool}
  {Spec.owners(G, x, Impl.total(mats, n, k), G) == 1n : Nat}

# (1) The kernel's block ranges [s_b, e_b) (K:96-97) are exactly the owned sets.
law range_is_owned:
  for +mats: Nat
  for +n: Nat
  for +k: Nat
  for +G: Nat
  for +b: Nat
  for +x: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  {Bool.and(Nat.is_le(Impl.start(b, Impl.total(mats, n, k), G), x),
      Nat.is_lt(x, Impl.start(1n+b, Impl.total(mats, n, k), G))) ==
    Spec.owns(b, x, Impl.total(mats, n, k), G) : Bool}

# (1) The kernel's owner() (K:65-68, H:83-86) names that block, and it is in the grid.
law owner_owns:
  for +mats: Nat
  for +n: Nat
  for +k: Nat
  for +G: Nat
  for +x: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for inside: {Nat.is_lt(x, Impl.total(mats, n, k)) == True{} : Bool}
  {Spec.owns(Impl.owner(x, Impl.total(mats, n, k), G), x, Impl.total(mats, n, k), G) ==
    True{} : Bool} &
  {Nat.is_lt(Impl.owner(x, Impl.total(mats, n, k), G), G) == True{} : Bool}

# (2) Block b < G runs the group-boundary code of group g (K:200-203) iff it owns an
# iteration of g. No H:184 precondition needed: an empty block runs no group.
law runs_iff_touches:
  for +mats: Nat
  for +n: Nat
  for +k: Nat
  for +G: Nat
  for +g: Nat
  for +b: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  for group: {Nat.is_lt(g, Impl.groups(mats, n)) == True{} : Bool}
  for block: {Nat.is_lt(b, G) == True{} : Bool}
  {Impl.runs(Impl.start(b, Impl.total(mats, n, k), G),
      Impl.start(1n+b, Impl.total(mats, n, k), G), Impl.kt(k), g) ==
    Spec.touches(b, g, Impl.kt(k), Impl.total(mats, n, k), G) : Bool}

# (2) Under the host guard total >= G (H:184) the blocks touching g are exactly the
# contiguous range [b_lo(g), b_hi(g)] (K:321-322), which is non-empty and inside the grid.
law contributors_contiguous:
  for +mats: Nat
  for +n: Nat
  for +k: Nat
  for +G: Nat
  for +g: Nat
  for +b: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total(mats, n, k)) == True{} : Bool}
  for group: {Nat.is_lt(g, Impl.groups(mats, n)) == True{} : Bool}
  {Spec.touches(b, g, Impl.kt(k), Impl.total(mats, n, k), G) ==
    Bool.and(Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G), b),
      Nat.is_le(b, Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G))) : Bool} &
  {Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G),
    Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G)) == True{} : Bool} &
  {Nat.is_lt(Impl.b_hi(g, Impl.kt(k), Impl.total(mats, n, k), G), G) == True{} : Bool}

# (2) A contributor's slot b - b_lo (K:328) is below nc (K:323), nc fits the host's
# max_contrib (H:186-191), and its workspace address fits groups * max_contrib slots (H:192).
law slot_in_range:
  for +mats: Nat
  for +n: Nat
  for +k: Nat
  for +G: Nat
  for +g: Nat
  for +b: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total(mats, n, k)) == True{} : Bool}
  for group: {Nat.is_lt(g, Impl.groups(mats, n)) == True{} : Bool}
  for contributor: {Spec.touches(b, g, Impl.kt(k), Impl.total(mats, n, k), G) == True{}
    : Bool}
  {Nat.is_lt(Nat.sub(b, Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G)),
    Impl.nc(g, Impl.kt(k), Impl.total(mats, n, k), G)) == True{} : Bool} &
  {Nat.is_le(Impl.nc(g, Impl.kt(k), Impl.total(mats, n, k), G),
    Impl.max_contrib(Impl.groups(mats, n), Impl.kt(k), Impl.total(mats, n, k), G)) ==
    True{} : Bool} &
  {Nat.is_lt(Impl.address(g, Impl.max_contrib(Impl.groups(mats, n), Impl.kt(k),
      Impl.total(mats, n, k), G), b, Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G)),
    Nat.mul(Impl.groups(mats, n), Impl.max_contrib(Impl.groups(mats, n), Impl.kt(k),
      Impl.total(mats, n, k), G))) == True{} : Bool}

# (2) Workspace addresses are injective over (group, contributor): no two partials share
# a slot, within or across groups.
law slot_injective:
  for +mats: Nat
  for +n: Nat
  for +k: Nat
  for +G: Nat
  for +g: Nat
  for +b: Nat
  for +h: Nat
  for +c: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total(mats, n, k)) == True{} : Bool}
  for group_g: {Nat.is_lt(g, Impl.groups(mats, n)) == True{} : Bool}
  for group_h: {Nat.is_lt(h, Impl.groups(mats, n)) == True{} : Bool}
  for touch_b: {Spec.touches(b, g, Impl.kt(k), Impl.total(mats, n, k), G) == True{} : Bool}
  for touch_c: {Spec.touches(c, h, Impl.kt(k), Impl.total(mats, n, k), G) == True{} : Bool}
  for same: {Impl.address(g, Impl.max_contrib(Impl.groups(mats, n), Impl.kt(k),
      Impl.total(mats, n, k), G), b, Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G)) ==
    Impl.address(h, Impl.max_contrib(Impl.groups(mats, n), Impl.kt(k),
      Impl.total(mats, n, k), G), c, Impl.b_lo(h, Impl.kt(k), Impl.total(mats, n, k), G))
    : Nat}
  {g == h : Nat} & {b == c : Nat}

# (3) Warp split (K:84-85, K:103, K:131, K:199-207): for any block range [s, e) and 64-column
# half h, a tile x is run by exactly one of the 8 warps of that half when s <= x < e, and by
# none otherwise.
law warp_split:
  for +s: Nat
  for +e: Nat
  for +x: Nat
  for +h: Nat
  for ordered: {Nat.is_le(s, e) == True{} : Bool}
  for half: {Nat.is_lt(h, 2n) == True{} : Bool}
  {Impl.handlers(8n, x, h, s, e) ==
    Spec.bit(Bool.and(Nat.is_le(s, x), Nat.is_lt(x, e))) : Nat}

# (3) The prefetch issue count nj (K:103, K:127-129, K:209) equals the compute loop's
# count (it = s_b + kp + 4j while it < e_b, K:199-207): the cp.async ring never desyncs.
law issue_matches_compute:
  for +s: Nat
  for +e: Nat
  for +kp: Nat
  for +j: Nat
  for ordered: {Nat.is_le(s, e) == True{} : Bool}
  {Nat.is_lt(j, Impl.nj(s, e, kp)) == Nat.is_lt(Impl.iter(s, kp, j), e) : Bool}

# (3) Group attribution (K:200-207): an iteration s_b <= it < e_b decoded as g = it / KT is
# in a group the loop runs, inside g's segment [g * KT, seg_hi(g)); the last segment
# ends at e_b.
law segment_attribution:
  for +k: Nat
  for +s: Nat
  for +e: Nat
  for +it: Nat
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  for low: {Nat.is_le(s, it) == True{} : Bool}
  for high: {Nat.is_lt(it, e) == True{} : Bool}
  {Impl.runs(s, e, Impl.kt(k), Nat.div(it, Impl.kt(k))) == True{} : Bool} &
  {Nat.is_le(Nat.mul(Nat.div(it, Impl.kt(k)), Impl.kt(k)), it) == True{} : Bool} &
  {Nat.is_lt(it, Impl.seg_hi(e, Nat.div(it, Impl.kt(k)), Impl.kt(k))) == True{} : Bool} &
  {Impl.seg_hi(e, Nat.div(Nat.sub(e, 1n), Impl.kt(k)), Impl.kt(k)) == e : Nat}

# (3) The incremental issue cursor (K:213-214) stays equal to the decoded iteration
# (K:176-177) after every step of 4.
law cursor_step:
  for +k: Nat
  for +it: Nat
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  {Impl.advance(Impl.decode(it, Impl.kt(k)), Impl.kt(k)) ==
    Impl.decode(Nat.add(it, 4n), Impl.kt(k)) : Impl.Cursor}

# (3) The two 64-column halves use disjoint in-block reduction slots (K:261-262).
law red_slots_disjoint:
  for +a: Nat
  for +h: Nat
  for +c: Nat
  for +i: Nat
  for a2: {Nat.is_lt(a, 2n) == True{} : Bool}
  for h2: {Nat.is_lt(h, 2n) == True{} : Bool}
  for c2: {Nat.is_lt(c, 2n) == True{} : Bool}
  for i2: {Nat.is_lt(i, 2n) == True{} : Bool}
  for same: {Impl.red_slot(a, h) == Impl.red_slot(c, i) : Nat}
  {a == c : Nat} & {h == i : Nat}

# (4) In-block split-K: the shared-memory steps K:284-292 compute (p0 + p2) + (p1 + p3).
law block_tree:
  for p0: Spec.Sum
  for p1: Spec.Sum
  for p2: Spec.Sum
  for p3: Spec.Sum
  {Impl.tree(p0, p1, p2, p3) == Spec.tree(p0, p1, p2, p3) : Spec.Sum}

# (4) Cross-block split-K: whatever order the touching blocks arrive in (repeats allowed),
# once they have all stored their partials (K:328-331) into a workspace with room for nc
# slots, the finisher's sum (K:344-354) is the ascending-block left fold of the partials of
# the blocks touching g: it depends only on (G, shape, g).
law reduction_order:
  for +mats: Nat
  for +n: Nat
  for +k: Nat
  for +G: Nat
  for +g: Nat
  for +order: List<&2, Nat>
  for +ws: List<&2, Spec.Sum>
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total(mats, n, k)) == True{} : Bool}
  for group: {Nat.is_lt(g, Impl.groups(mats, n)) == True{} : Bool}
  for room: {Nat.is_le(Impl.nc(g, Impl.kt(k), Impl.total(mats, n, k), G),
    List.length(&2, Spec.Sum, ws)) == True{} : Bool}
  for touching: {Spec.all_touch(order, g, Impl.kt(k), Impl.total(mats, n, k), G) ==
    True{} : Bool}
  for complete: {Spec.all_arrived(G, order, g, Impl.kt(k), Impl.total(mats, n, k), G) ==
    True{} : Bool}
  {Some{Impl.finish(Impl.arrive(order, ws, Impl.b_lo(g, Impl.kt(k),
      Impl.total(mats, n, k), G)), Impl.nc(g, Impl.kt(k), Impl.total(mats, n, k), G))} ==
    Spec.reduce(g, Impl.kt(k), Impl.total(mats, n, k), G) : Maybe<&2, Spec.Sum>}
