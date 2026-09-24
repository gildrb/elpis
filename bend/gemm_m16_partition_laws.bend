# Semantic obligations for the work partition and deterministic split-K reduction of the
# EXL3 m16 swap-AB GEMM, patch 2001 v2 (patches/exl3-ext/2001-gemm-m16-swapab.patch, sha256
# 0da35574..., committed at 03e72ca; K:/H: line refs as in gemm_m16_partition.bend). Shape laws
# quantify over every shape: mats matrices, k >= 128 (KT = k / 16 k-tiles; covers every multiple
# of 128), any n (NG = n / 512 groups per matrix) and any grid G >= 1; I = Impl.total(mats, n, k).
# Block-loop laws quantify over any block range [s, e) and any KT >= 1.
# Nat model of the C int expressions: overflow, the memory model (__stcg/__ldcg visibility across
# grid.sync), cp.async timing and fp32 values are outside this contract (see the module headers).
# Retired with v1 (structure absent from v2): warp_split, issue_matches_compute, cursor_step
# (step 4), segment_attribution, runs_iff_touches, red_slots_disjoint, block_tree.
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

# (1) The kernel's block ranges [s_b, e_b) (K:124-125) are exactly the owned sets.
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

# (1) The kernel's owner() (K:72-75, H:80-83) names that block, and it is in the grid.
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

# (2) Under the host guard total >= G (H:183) the blocks touching g are exactly the
# contiguous range [b_lo(g), b_hi(g)] (K:258, K:364), which is non-empty and inside the grid.
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

# (2) A contributor's slot b - b_lo (K:258-259) is below nc (K:364), nc fits the host's
# max_contrib (H:184-189), and its workspace address fits groups * max_contrib slots (K:259, H:190).
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

# (3) Main loop (K:275-346): for any block range [s, e) and KT >= 1 the loop consumes the
# iterations s .. e - 1 once each, in ascending order, each into group it / KT, and flushes each
# group right after its last iteration in the range. (Equality also shows the model's fuel
# never stops the loop early.)
law mainloop_trace:
  for +s: Nat
  for +e: Nat
  for +KT: Nat
  for ordered: {Nat.is_le(s, e) == True{} : Bool}
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  {Impl.mainloop(s, e, KT) == Spec.trace(Nat.sub(e, s), s, e, KT) : List<&2, Spec.Ev>}

# (3) Block b flushes (K:344) group g exactly once if it owns an iteration of g, else never.
law flush_once_iff_touches:
  for +mats: Nat
  for +n: Nat
  for +k: Nat
  for +G: Nat
  for +g: Nat
  for +b: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  {Spec.flushes(Impl.mainloop(Impl.start(b, Impl.total(mats, n, k), G),
      Impl.start(1n+b, Impl.total(mats, n, k), G), Impl.kt(k)), g) ==
    Spec.bit(Spec.touches(b, g, Impl.kt(k), Impl.total(mats, n, k), G)) : Nat}

# (3) The incremental weight-issue cursor (K:140-155) after j issues is the decoded iteration
# s + j (K:141-142, the same decode as the activation copy K:169-171).
law issue_cursor:
  for +s: Nat
  for +j: Nat
  for +KT: Nat
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  {Impl.issued(j, s, KT) == Impl.decode(Nat.add(s, j), KT) : Impl.Cursor}

# (4) Warp w's partial element (n-tile t, c >> 1 = h, lane >> 2 = q) (K:259, K:268) lies in the
# 512-column group, in w's own 64-column slice, and in the weight n-tile w * 4 + t that warp w
# streams (K:138).
law warp_columns:
  for +w: Nat
  for +t: Nat
  for +h: Nat
  for +q: Nat
  for w8: {Nat.is_lt(w, 8n) == True{} : Bool}
  for t4: {Nat.is_lt(t, 4n) == True{} : Bool}
  for h2: {Nat.is_lt(h, 2n) == True{} : Bool}
  for q8: {Nat.is_lt(q, 8n) == True{} : Bool}
  {Nat.is_lt(Impl.col(w, t, h, q), 512n) == True{} : Bool} &
  {Nat.div(Impl.col(w, t, h, q), 64n) == w : Nat} &
  {Nat.div(Impl.col(w, t, h, q), 16n) == Impl.wtile(w, t) : Nat}

# (4) No two (warp, n-tile, c >> 1, lane >> 2) write the same column.
law warp_columns_injective:
  for +w: Nat
  for +t: Nat
  for +h: Nat
  for +q: Nat
  for +w2: Nat
  for +t2: Nat
  for +h2: Nat
  for +q2: Nat
  for tw: {Nat.is_lt(t, 4n) == True{} : Bool}
  for hw: {Nat.is_lt(h, 2n) == True{} : Bool}
  for qw: {Nat.is_lt(q, 8n) == True{} : Bool}
  for tw2: {Nat.is_lt(t2, 4n) == True{} : Bool}
  for hw2: {Nat.is_lt(h2, 2n) == True{} : Bool}
  for qw2: {Nat.is_lt(q2, 8n) == True{} : Bool}
  for same: {Impl.col(w, t, h, q) == Impl.col(w2, t2, h2, q2) : Nat}
  {w == w2 : Nat} & {t == t2 : Nat} & {h == h2 : Nat} & {q == q2 : Nat}

# (4) Every column c < 512 of a group is written by the in-range tuple (c / 64, c % 64 / 16,
# c % 16 / 8, c % 8).
law warp_columns_cover:
  for +c: Nat
  for inside: {Nat.is_lt(c, 512n) == True{} : Bool}
  {Nat.is_lt(Nat.div(c, 64n), 8n) == True{} : Bool} &
  {Impl.col(Nat.div(c, 64n), Nat.div(Nat.mod(c, 64n), 16n), Nat.div(Nat.mod(c, 16n), 8n),
    Nat.mod(c, 8n)) == c : Nat}

# (4) Token rows of a lane's accumulator (K:267): row(mt, lane & 3, c & 1) is injective, every
# row r is row(r / 8, r % 8 / 2, r % 2), and token tile mt covers rows 8 mt .. 8 mt + 7.
law lane_rows:
  for +mt: Nat
  for +a: Nat
  for +c1: Nat
  for +mt2: Nat
  for +a2: Nat
  for +c2: Nat
  for aw: {Nat.is_lt(a, 4n) == True{} : Bool}
  for cw: {Nat.is_lt(c1, 2n) == True{} : Bool}
  for aw2: {Nat.is_lt(a2, 4n) == True{} : Bool}
  for cw2: {Nat.is_lt(c2, 2n) == True{} : Bool}
  for same: {Impl.row(mt, a, c1) == Impl.row(mt2, a2, c2) : Nat}
  {mt == mt2 : Nat} & {a == a2 : Nat} & {c1 == c2 : Nat}

law lane_rows_cover:
  for +r: Nat
  {Impl.row(Nat.div(r, 8n), Nat.div(Nat.mod(r, 8n), 2n), Nat.mod(r, 2n)) == r : Nat} &
  {Nat.div(r, 8n) == Nat.div(Impl.row(Nat.div(r, 8n), Nat.div(Nat.mod(r, 8n), 2n),
    Nat.mod(r, 2n)), 8n) : Nat}

# (5) Finisher (K:358): every job x < jobs is visited by exactly one (block, warp) of the grid,
# and no job past the end is visited.
law finish_jobs_once:
  for +x: Nat
  for +G: Nat
  for +J: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  {Impl.job_hits(G, x, G, J) == Spec.bit(Nat.is_lt(x, J)) : Nat}

# (5) Job decode (K:360-363) is a bijection from [0, groups * m * 4) (K:357) onto (group <
# groups, row < m, chunk < 4): every job decodes in range and back to itself ...
law finish_job_decode:
  for +groups: Nat
  for +m: Nat
  for +x: Nat
  for inside: {Nat.is_lt(x, Impl.jobs(groups, m)) == True{} : Bool}
  {Spec.job_ok(Impl.job(x, m), groups, m) == True{} : Bool} &
  {Spec.encode(Impl.job(x, m), m) == x : Nat}

# (5) ... and every (group, row, chunk) in range is the decode of its own job number.
law finish_job_encode:
  for +groups: Nat
  for +m: Nat
  for +j: Spec.Job
  for ok: {Spec.job_ok(j, groups, m) == True{} : Bool}
  {Impl.job(Spec.encode(j, m), m) == j : Spec.Job} &
  {Nat.is_lt(Spec.encode(j, m), Impl.jobs(groups, m)) == True{} : Bool}

# (5) Cross-block split-K: whatever order the touching blocks' flushes land in before the
# grid.sync (K:350) (repeats allowed), once they have all stored their partials (K:256-270)
# into a workspace with room for nc slots, the finisher's sum (K:364-371) is the
# ascending-block left fold of the partials of the blocks touching g: it depends only on
# (G, shape, g).
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
