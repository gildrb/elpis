# Semantic obligations for the ext 2105 / 8205 slot-weighted split-K partition
# (bend/gemm_m16_wpart.bend; K:/H: line refs there). Every law is generic in total, G, nsm, w0, w1 (and
# KT, groups, g, b, x) unless it names the served instance; the preconditions are stated per law.
# `wpos` below means 1 <= w0, 1 <= w1 and 1 <= G (so W(G) >= 1). Nat model of the C int64 expressions:
# overflow, the kernel's memory model and fp32 values are outside this contract.
import Base
import ./gemm_m16_wpart.bend as Impl
import ./gemm_m16_wpart_spec.bend as Spec
import ./gemm_m16_partition.bend as V2
import ./gemm_m16_partition_spec.bend as V2Spec

# (0) The min/max closed form of W (K:54-57) is the recursive weight prefix of the spec.
law wpre_is_wsum:
  for +b: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  {Impl.wpre(b, nsm, w0, w1) == Spec.wsum(b, nsm, w0, w1) : Nat}

# (1) The partition starts at 0 and ends at total.
law start_zero:
  for +total: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  {Impl.start(0n, total, G, nsm, w0, w1) == 0n : Nat}

law start_full:
  for +total: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  {Impl.start(G, total, G, nsm, w0, w1) == total : Nat}

# (2) start is monotone.
law start_mono:
  for +total: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +b: Nat
  for +c: Nat
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for ordered: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(Impl.start(b, total, G, nsm, w0, w1), Impl.start(c, total, G, nsm, w0, w1)) ==
    True{} : Bool}

# (3) The closed-form owner (K:66-72) is the largest block whose share starts at or below x: for
# every b, b <= owner(x) iff start(b) <= x (generic; no non-empty-slice assumption).
law owner_galois:
  for +total: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +b: Nat
  for +x: Nat
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for work: {Nat.is_lt(0n, total) == True{} : Bool}
  {Nat.is_le(b, Impl.owner(x, total, G, nsm, w0, w1)) ==
    Nat.is_le(Impl.start(b, total, G, nsm, w0, w1), x) : Bool}

# (3) For x < total, owner(x) is in the grid and x lies in its range [start(owner), start(owner + 1)).
law owner_correct:
  for +total: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +x: Nat
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for inside: {Nat.is_lt(x, total) == True{} : Bool}
  {Nat.is_le(Impl.start(Impl.owner(x, total, G, nsm, w0, w1), total, G, nsm, w0, w1), x) ==
    True{} : Bool} &
  {Nat.is_lt(x, Impl.start(1n+Impl.owner(x, total, G, nsm, w0, w1), total, G, nsm, w0, w1)) ==
    True{} : Bool} &
  {Nat.is_lt(Impl.owner(x, total, G, nsm, w0, w1), G) == True{} : Bool}

# (3) The closed form equals the spec's downward search for the largest b < G with
# total * wsum(b) < (x + 1) * wsum(G).
law owner_is_search:
  for +total: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +x: Nat
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for inside: {Nat.is_lt(x, total) == True{} : Bool}
  {Impl.owner(x, total, G, nsm, w0, w1) == Spec.search(G, x, total, G, nsm, w0, w1) : Nat}

# (3) The kernel's block ranges [s_b, e_b) (K:132-133) are exactly the spec's owned sets.
law range_is_owned:
  for +total: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +b: Nat
  for +x: Nat
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  {Bool.and(Nat.is_le(Impl.start(b, total, G, nsm, w0, w1), x),
      Nat.is_lt(x, Impl.start(1n+b, total, G, nsm, w0, w1))) ==
    Spec.owns(b, x, total, G, nsm, w0, w1) : Bool}

# (4) Every iteration x < total has exactly one owning block b < G.
law owners_exactly_one:
  for +total: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +x: Nat
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for inside: {Nat.is_lt(x, total) == True{} : Bool}
  {Spec.owners(G, x, total, G, nsm, w0, w1) == 1n : Nat}

# (4) ... and owner(x) is that block: any b with start(b) <= x < start(b + 1) is owner(x).
law owner_unique:
  for +total: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +b: Nat
  for +x: Nat
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for work: {Nat.is_lt(0n, total) == True{} : Bool}
  for lo: {Nat.is_le(Impl.start(b, total, G, nsm, w0, w1), x) == True{} : Bool}
  for hi: {Nat.is_lt(x, Impl.start(1n+b, total, G, nsm, w0, w1)) == True{} : Bool}
  {Impl.owner(x, total, G, nsm, w0, w1) == b : Nat}

# (5) Equal weights (w, w), w >= 1, are 2001's v2 partition: start and owner coincide with
# gemm_m16_partition's, so every v2 law carries over at (1, 1) (the kill switch).
law equal_weights_is_v2:
  for +total: Nat
  for +G: Nat
  for +nsm: Nat
  for +w: Nat
  for +b: Nat
  for +x: Nat
  for wpos: {Nat.is_lt(0n, w) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for work: {Nat.is_lt(0n, total) == True{} : Bool}
  {Impl.start(b, total, G, nsm, w, w) == V2.start(b, total, G) : Nat} &
  {Impl.owner(x, total, G, nsm, w, w) == V2.owner(x, total, G) : Nat}

# (6) The host guard (H:103-109) implies the positivity preconditions ...
law valid_domain:
  for +total: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for valid: {Impl.weights_valid(total, G, nsm, w0, w1) == True{} : Bool}
  {Nat.is_lt(0n, w0) == True{} : Bool} & {Nat.is_lt(0n, w1) == True{} : Bool} &
  {Nat.is_lt(0n, G) == True{} : Bool} & {Nat.is_lt(0n, total) == True{} : Bool}

# (6) ... and non-empty slices for every block of the grid.
law valid_nonempty:
  for +total: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +b: Nat
  for valid: {Impl.weights_valid(total, G, nsm, w0, w1) == True{} : Bool}
  for block: {Nat.is_lt(b, G) == True{} : Bool}
  {Nat.is_lt(Impl.start(b, total, G, nsm, w0, w1), Impl.start(1n+b, total, G, nsm, w0, w1)) ==
    True{} : Bool}

# (7) Group g < groups (iterations g * KT .. (g + 1) * KT - 1 of total = groups * KT): its first and
# last contributors are ordered and in the grid, nc = last - first + 1 >= 1 and nc <= max_contrib
# (H:112-122). No non-empty-slice assumption.
law contrib_bounds:
  for +groups: Nat
  for +KT: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +g: Nat
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for group: {Nat.is_lt(g, groups) == True{} : Bool}
  {Nat.is_le(Impl.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1),
    Impl.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool} &
  {Nat.is_lt(Impl.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), G) == True{} : Bool} &
  {Nat.is_le(1n, Impl.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool} &
  {Nat.is_le(Impl.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1),
    Impl.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool}

# (7) A contributor b of group g (it owns an iteration of g) flushes into slot b - first_contrib(g)
# (K:279-280): first_contrib(g) <= b, the slot is below nc(g) <= max_contrib, and the workspace
# address g * max_contrib + slot is below groups * max_contrib (H:144).
law slot_in_range:
  for +groups: Nat
  for +KT: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +g: Nat
  for +b: Nat
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for group: {Nat.is_lt(g, groups) == True{} : Bool}
  for contributor: {Spec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}
  {Nat.is_le(Impl.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b) == True{} : Bool} &
  {Nat.is_lt(Nat.sub(b, Impl.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
    Impl.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) == True{} : Bool} &
  {Nat.is_lt(Nat.sub(b, Impl.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
    Impl.max_contrib(groups, KT, G, nsm, w0, w1)) == True{} : Bool} &
  {Nat.is_lt(Impl.address(g, Impl.max_contrib(groups, KT, G, nsm, w0, w1), b,
      Impl.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)),
    Nat.mul(groups, Impl.max_contrib(groups, KT, G, nsm, w0, w1))) == True{} : Bool}

# (7) Workspace addresses are injective over (group, contributor): no two partials share a slot.
law slot_injective:
  for +groups: Nat
  for +KT: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +g: Nat
  for +b: Nat
  for +h: Nat
  for +c: Nat
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for group_g: {Nat.is_lt(g, groups) == True{} : Bool}
  for group_h: {Nat.is_lt(h, groups) == True{} : Bool}
  for touch_b: {Spec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}
  for touch_c: {Spec.touches(c, h, KT, Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}
  for same: {Impl.address(g, Impl.max_contrib(groups, KT, G, nsm, w0, w1), b,
      Impl.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) ==
    Impl.address(h, Impl.max_contrib(groups, KT, G, nsm, w0, w1), c,
      Impl.first_contrib(h, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) : Nat}
  {g == h : Nat} & {b == c : Nat}

# (7) Under the host guard the blocks b < G touching g are exactly [first_contrib(g), last_contrib(g)]
# (so the finisher's slots 0 .. nc - 1 (K:375-381) are all written) ...
law contributors_contiguous:
  for +groups: Nat
  for +KT: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +g: Nat
  for +b: Nat
  for valid: {Impl.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for group: {Nat.is_lt(g, groups) == True{} : Bool}
  for block: {Nat.is_lt(b, G) == True{} : Bool}
  {Spec.touches(b, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) ==
    Bool.and(Nat.is_le(Impl.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), b),
      Nat.is_le(b, Impl.last_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1))) : Bool}

# (7) ... and their number is nc(g).
law touch_count_is_nc:
  for +groups: Nat
  for +KT: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +g: Nat
  for valid: {Impl.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool}
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for group: {Nat.is_lt(g, groups) == True{} : Bool}
  {Spec.touch_count(G, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) ==
    Impl.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1) : Nat}

# (8) Slice length: if L * W(G) <= total * w0 and L * W(G) <= total * w1, every block owns at least L
# iterations (so L >= 1 gives non-empty slices) ...
law slice_len:
  for +total: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +L: Nat
  for +b: Nat
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for l0: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w0)) == True{} : Bool}
  for l1: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w1)) == True{} : Bool}
  {Nat.is_le(Nat.add(Impl.start(b, total, G, nsm, w0, w1), L),
    Impl.start(1n+b, total, G, nsm, w0, w1)) == True{} : Bool}

# (8) ... and then a group of KT iterations has at most D + 2 contributors when KT - 2 < (D + 1) L.
law nc_bound:
  for +total: Nat
  for +KT: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +L: Nat
  for +D: Nat
  for +g: Nat
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for work: {Nat.is_lt(0n, total) == True{} : Bool}
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for l0: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w0)) == True{} : Bool}
  for l1: {Nat.is_le(Nat.mul(L, Impl.wpre(G, nsm, w0, w1)), Nat.mul(total, w1)) == True{} : Bool}
  for span: {Nat.is_lt(Nat.sub(KT, 2n), Nat.mul(1n+D, L)) == True{} : Bool}
  {Nat.is_le(Impl.nc(g, KT, total, G, nsm, w0, w1), 2n+D) == True{} : Bool}

# (9) Served instance (82 SMs, G = 164, KT = 5120 / 16 = 320, H:195-196 weights (100, 91), slot workspace
# EXL3_M16G_SLOT_BYTES = 8 * 1024 * 1024): the host guard holds (every slice non-empty), max_contrib is 7 for
# the GDN bundle (32 groups) and 8 for the attention bundle (28 groups), and both launches fit (H:141-145).
# The served constants enter through equations on variables (as in tail_m16_sched's mc0_served): the
# checker's Nat is unary and normalizes closed terms, so the laws keep every large product symbolic.
law served_gdn:
  for +groups: Nat
  for +KT: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +k: Nat
  for +cap: Nat
  for s_groups: {groups == Impl.groups_gdn() : Nat}
  for s_kt: {KT == Impl.kt_served() : Nat}
  for s_grid: {G == Impl.grid_served() : Nat}
  for s_nsm: {nsm == Impl.nsm_served() : Nat}
  for s_w0: {w0 == Impl.w0_served() : Nat}
  for s_w1: {w1 == Impl.w1_served() : Nat}
  for s_k: {k == 1024n : Nat}
  for s_cap: {cap == Impl.slot_bytes_of(k) : Nat}
  {Impl.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool} &
  {Impl.max_contrib(groups, KT, G, nsm, w0, w1) == 7n : Nat} &
  {Impl.launch_fits_cap(groups, KT, G, nsm, w0, w1, cap) == True{} : Bool}

law served_attn:
  for +groups: Nat
  for +KT: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +k: Nat
  for +cap: Nat
  for s_groups: {groups == Impl.groups_attn() : Nat}
  for s_kt: {KT == Impl.kt_served() : Nat}
  for s_grid: {G == Impl.grid_served() : Nat}
  for s_nsm: {nsm == Impl.nsm_served() : Nat}
  for s_w0: {w0 == Impl.w0_served() : Nat}
  for s_w1: {w1 == Impl.w1_served() : Nat}
  for s_k: {k == 1024n : Nat}
  for s_cap: {cap == Impl.slot_bytes_of(k) : Nat}
  {Impl.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1) == True{} : Bool} &
  {Impl.max_contrib(groups, KT, G, nsm, w0, w1) == 8n : Nat} &
  {Impl.launch_fits_cap(groups, KT, G, nsm, w0, w1, cap) == True{} : Bool}
