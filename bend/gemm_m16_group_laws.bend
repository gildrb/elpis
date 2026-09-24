# Semantic obligations for the column map, work partition, split-K slots, distributed finish and
# prologue of the grouped EXL3 m16 GEMM, ext patch 2102 (2102-proj-m16-grouped-v2.patch, sha256
# 50f75e69...; K:/H: line refs as in gemm_m16_group.bend). A bundle ns is the list of matrix widths
# in launch order; laws quantify over every bundle of at most 4 matrices (EXL3_M16G_MAX_MATS; the
# host rejects more, H:190), every k (KT = k / 16; k >= 128 where a law needs KT >= 1, which covers
# every multiple of 128), every token count m and every grid G >= 1. Width laws add widths_ok
# (every n_i a positive multiple of 512, H:102-103). Partition laws take the host's launch guard
# launch_fits (H:109-113, TORCH_CHECKed at H:240) with any slot byte budget sb (the patch passes
# EXL3_M16G_SLOT_BYTES) instead of assuming a workspace size.
# The Nat model of the C int expressions: overflow, the memory model (__stcg/__ldcg visibility
# across grid.sync), cp.async timing and fp32 values are outside this contract. The block
# partition, main loop, owner helper and finish are 2001 v2's (bend/gemm_m16_partition_laws.bend
# proves them over any total); these laws restate them over the bundle's total and add the
# multi-matrix structure.
import Base
import ./gemm_m16_group.bend as Impl
import ./gemm_m16_group_spec.bend as Spec
import ./gemm_m16_partition.bend as V2
import ./gemm_m16_partition_spec.bend as V2Spec

# (a) The host's gbase array (H:203-227, read at K:53-70, K:96) is the prefix sum of the groups per
# matrix, and gbase[4] is the bundle's group count.
law gbase_prefix:
  for +ns: List<&2, Nat>
  for +i: Nat
  {Impl.gbase(ns, i) == Spec.before(ns, i) : Nat}

law groups_total:
  for +ns: List<&2, Nat>
  for bundle: {Nat.is_le(Impl.num_mats(ns), 4n) == True{} : Bool}
  {Impl.groups(ns) == Spec.ngroups(ns) : Nat}

# (a) Column map forward: every launch group g < groups lies in the matrix exl3_m16g_mat (K:63-70)
# names, at local index g - gbase[mat] (K:115, K:348), which is one of that matrix's groups and
# numbers back to g.
law group_map_forward:
  for +ns: List<&2, Nat>
  for +g: Nat
  for bundle: {Nat.is_le(Impl.num_mats(ns), 4n) == True{} : Bool}
  for inside: {Nat.is_lt(g, Impl.groups(ns)) == True{} : Bool}
  {Nat.is_lt(Impl.mat(ns, g), Impl.num_mats(ns)) == True{} : Bool} &
  {Nat.is_lt(Impl.local(ns, g), Spec.ng_at(ns, Impl.mat(ns, g))) == True{} : Bool} &
  {Spec.gidx(ns, Impl.mat(ns, g), Impl.local(ns, g)) == g : Nat}

# (a) Column map onto: every group l of every matrix i is a launch group, mapped back to (i, l).
law group_map_onto:
  for +ns: List<&2, Nat>
  for +i: Nat
  for +l: Nat
  for bundle: {Nat.is_le(Impl.num_mats(ns), 4n) == True{} : Bool}
  for mat_i: {Nat.is_lt(i, Impl.num_mats(ns)) == True{} : Bool}
  for group_l: {Nat.is_lt(l, Spec.ng_at(ns, i)) == True{} : Bool}
  {Nat.is_lt(Spec.gidx(ns, i, l), Impl.groups(ns)) == True{} : Bool} &
  {Impl.mat(ns, Spec.gidx(ns, i, l)) == i : Nat} &
  {Impl.local(ns, Spec.gidx(ns, i, l)) == l : Nat}

# (a) The per-matrix width recomputed from gbase (n_mat K:347; row_bytes K:114) is the matrix's width.
law group_map_width:
  for +ns: List<&2, Nat>
  for +g: Nat
  for bundle: {Nat.is_le(Impl.num_mats(ns), 4n) == True{} : Bool}
  for widths: {Spec.widths_ok(ns) == True{} : Bool}
  for inside: {Nat.is_lt(g, Impl.groups(ns)) == True{} : Bool}
  {Impl.nmat(ns, g) == Spec.width(ns, Impl.mat(ns, g)) : Nat}

# (a) Ownership: every (matrix i, local group l, k-tile t) is iteration (gidx * KT + t) of the
# launch, owned by exactly one block (spec: division-free), decoded by the kernel (K:118-119,
# K:151-152) back to group gidx, k-tile t, and mapped to matrix i, local group l.
law tile_owned_once:
  for +ns: List<&2, Nat>
  for +k: Nat
  for +G: Nat
  for +i: Nat
  for +l: Nat
  for +t: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for bundle: {Nat.is_le(Impl.num_mats(ns), 4n) == True{} : Bool}
  for mat_i: {Nat.is_lt(i, Impl.num_mats(ns)) == True{} : Bool}
  for group_l: {Nat.is_lt(l, Spec.ng_at(ns, i)) == True{} : Bool}
  for tile_t: {Nat.is_lt(t, Impl.kt(k)) == True{} : Bool}
  {Nat.is_lt(Nat.add(Nat.mul(Spec.gidx(ns, i, l), Impl.kt(k)), t), Impl.total(ns, k)) ==
    True{} : Bool} &
  {V2Spec.owners(G, Nat.add(Nat.mul(Spec.gidx(ns, i, l), Impl.kt(k)), t), Impl.total(ns, k), G)
    == 1n : Nat} &
  {V2.decode(Nat.add(Nat.mul(Spec.gidx(ns, i, l), Impl.kt(k)), t), Impl.kt(k)) ==
    V2.Cursor{Spec.gidx(ns, i, l), t} : V2.Cursor} &
  {Impl.mat(ns, Spec.gidx(ns, i, l)) == i : Nat} &
  {Impl.local(ns, Spec.gidx(ns, i, l)) == l : Nat}

# (a) Every iteration x < total decodes (K:151-152) to a launch group and k-tile in range that
# encode back to x: there are no other iterations.
law tile_decode:
  for +ns: List<&2, Nat>
  for +k: Nat
  for +x: Nat
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  for inside: {Nat.is_lt(x, Impl.total(ns, k)) == True{} : Bool}
  {Nat.is_lt(Nat.div(x, Impl.kt(k)), Impl.groups(ns)) == True{} : Bool} &
  {Nat.is_lt(Nat.sub(x, Nat.mul(Nat.div(x, Impl.kt(k)), Impl.kt(k))), Impl.kt(k)) == True{} : Bool} &
  {Nat.add(Nat.mul(Nat.div(x, Impl.kt(k)), Impl.kt(k)),
    Nat.sub(x, Nat.mul(Nat.div(x, Impl.kt(k)), Impl.kt(k)))) == x : Nat}

# (a) Block b's range [s_b, e_b) (K:100-101) is exactly its owned set, and exl3_m16_owner names the
# owning block, inside the grid.
law blocks_own_ranges:
  for +ns: List<&2, Nat>
  for +k: Nat
  for +G: Nat
  for +b: Nat
  for +x: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for inside: {Nat.is_lt(x, Impl.total(ns, k)) == True{} : Bool}
  {Bool.and(Nat.is_le(Impl.start(b, Impl.total(ns, k), G), x),
      Nat.is_lt(x, Impl.start(1n+b, Impl.total(ns, k), G))) ==
    V2Spec.owns(b, x, Impl.total(ns, k), G) : Bool} &
  {V2Spec.owns(Impl.owner(x, Impl.total(ns, k), G), x, Impl.total(ns, k), G) == True{} : Bool} &
  {Nat.is_lt(Impl.owner(x, Impl.total(ns, k), G), G) == True{} : Bool}

# (a) Weight issue cursor across matrices (K:107-135): before the j-th issue of a block (j < n_iter)
# the incrementally maintained cursor and pointer (+= row_bytes within a group; w_src re-derived
# on a group wrap, possibly into the next matrix with its own width) equal the direct address of
# iteration s_b + j: its decoded (group, k-tile), B[mat(group)] and that tile row's offset.
law issue_site:
  for +s: Nat
  for +n: Nat
  for +KT: Nat
  for +j: Nat
  for +ns: List<&2, Nat>
  for +warp: Nat
  for +lane: Nat
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for issuing: {Nat.is_lt(j, n) == True{} : Bool}
  {Impl.issued(j, s, n, KT, ns, warp, lane) == Impl.wsite(ns, Nat.add(s, j), KT, warp, lane) : Impl.Iss}

# (a) Weight site bounds: for a launch group g, k-tile kt < KT, warp < 8 and lane < 32 the 16 bytes
# a lane streams (K:115 + K:121, the address issue_site names) lie inside B[mat]: KT rows of
# row_bytes (K:114), and row_bytes is that matrix's (n / 16) * 128 (the (k/16, n/16, 64) half
# trellis of H:210-211 at K = 4).
law weight_site_in_matrix:
  for +ns: List<&2, Nat>
  for +k: Nat
  for +g: Nat
  for +kt: Nat
  for +warp: Nat
  for +lane: Nat
  for bundle: {Nat.is_le(Impl.num_mats(ns), 4n) == True{} : Bool}
  for widths: {Spec.widths_ok(ns) == True{} : Bool}
  for inside: {Nat.is_lt(g, Impl.groups(ns)) == True{} : Bool}
  for tile: {Nat.is_lt(kt, Impl.kt(k)) == True{} : Bool}
  for warp8: {Nat.is_lt(warp, 8n) == True{} : Bool}
  for lane32: {Nat.is_lt(lane, 32n) == True{} : Bool}
  {Nat.is_le(Nat.add(Nat.add(Impl.wsrc(ns, g, warp, lane), Nat.mul(kt, Impl.row_bytes(ns, g))), 16n),
    Nat.mul(Impl.kt(k), Impl.row_bytes(ns, g))) == True{} : Bool} &
  {Impl.row_bytes(ns, g) == Nat.mul(Nat.div(Spec.width(ns, Impl.mat(ns, g)), 16n), 128n) : Nat}

# (a) The main loop (K:256-318) consumes the block's iterations once each in ascending order, each
# into group it / KT, and flushes (K:317) each group right after its last iteration in the range;
# block b flushes launch group g exactly once iff it owns an iteration of g.
law mainloop_trace:
  for +s: Nat
  for +e: Nat
  for +KT: Nat
  for ordered: {Nat.is_le(s, e) == True{} : Bool}
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  {Impl.mainloop(s, e, KT) == V2Spec.trace(Nat.sub(e, s), s, e, KT) : List<&2, V2Spec.Ev>}

law flush_once_iff_touches:
  for +ns: List<&2, Nat>
  for +k: Nat
  for +G: Nat
  for +g: Nat
  for +b: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  {V2Spec.flushes(Impl.mainloop(Impl.start(b, Impl.total(ns, k), G),
      Impl.start(1n+b, Impl.total(ns, k), G), Impl.kt(k)), g) ==
    V2Spec.bit(V2Spec.touches(b, g, Impl.kt(k), Impl.total(ns, k), G)) : Nat}

# (b) Under the host's launch guard the blocks contributing to launch group g (of any matrix) are
# the contiguous range [owner(g * KT), owner((g + 1) * KT - 1)] (K:239, K:334), inside the grid.
law contributors_contiguous:
  for +ns: List<&2, Nat>
  for +k: Nat
  for +G: Nat
  for +sb: Nat
  for +g: Nat
  for +b: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  for launch: {Impl.launch_fits(Impl.groups(ns), Impl.kt(k), G, sb) == True{} : Bool}
  for group: {Nat.is_lt(g, Impl.groups(ns)) == True{} : Bool}
  {V2Spec.touches(b, g, Impl.kt(k), Impl.total(ns, k), G) ==
    Bool.and(Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(ns, k), G), b),
      Nat.is_le(b, Impl.b_hi(g, Impl.kt(k), Impl.total(ns, k), G))) : Bool} &
  {Nat.is_le(Impl.b_lo(g, Impl.kt(k), Impl.total(ns, k), G),
    Impl.b_hi(g, Impl.kt(k), Impl.total(ns, k), G)) == True{} : Bool} &
  {Nat.is_lt(Impl.b_hi(g, Impl.kt(k), Impl.total(ns, k), G), G) == True{} : Bool}

# (c) A contributor's slot b - b_lo (K:239) is below nc (K:334), nc fits the host's max_contrib
# (H:80-90, H:248), and its slot g * max_contrib + (b - b_lo) (K:240) is below groups * max_contrib.
law slot_in_range:
  for +ns: List<&2, Nat>
  for +k: Nat
  for +G: Nat
  for +sb: Nat
  for +g: Nat
  for +b: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  for launch: {Impl.launch_fits(Impl.groups(ns), Impl.kt(k), G, sb) == True{} : Bool}
  for group: {Nat.is_lt(g, Impl.groups(ns)) == True{} : Bool}
  for contributor: {V2Spec.touches(b, g, Impl.kt(k), Impl.total(ns, k), G) == True{} : Bool}
  {Nat.is_lt(Nat.sub(b, Impl.b_lo(g, Impl.kt(k), Impl.total(ns, k), G)),
    Impl.nc(g, Impl.kt(k), Impl.total(ns, k), G)) == True{} : Bool} &
  {Nat.is_le(Impl.nc(g, Impl.kt(k), Impl.total(ns, k), G),
    Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G)) == True{} : Bool} &
  {Nat.is_lt(Impl.address(g, Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G), b,
      Impl.b_lo(g, Impl.kt(k), Impl.total(ns, k), G)),
    Nat.mul(Impl.groups(ns), Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G))) == True{} : Bool}

# (c) Slots are injective across all matrices of the bundle: two contributors (block b of local
# group l of matrix i, block c of local group l2 of matrix i2) that share a slot are the same
# block of the same group of the same matrix.
law slot_injective:
  for +ns: List<&2, Nat>
  for +k: Nat
  for +G: Nat
  for +sb: Nat
  for +i: Nat
  for +l: Nat
  for +b: Nat
  for +i2: Nat
  for +l2: Nat
  for +c: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  for bundle: {Nat.is_le(Impl.num_mats(ns), 4n) == True{} : Bool}
  for launch: {Impl.launch_fits(Impl.groups(ns), Impl.kt(k), G, sb) == True{} : Bool}
  for mat_i: {Nat.is_lt(i, Impl.num_mats(ns)) == True{} : Bool}
  for group_l: {Nat.is_lt(l, Spec.ng_at(ns, i)) == True{} : Bool}
  for mat_i2: {Nat.is_lt(i2, Impl.num_mats(ns)) == True{} : Bool}
  for group_l2: {Nat.is_lt(l2, Spec.ng_at(ns, i2)) == True{} : Bool}
  for touch_b: {V2Spec.touches(b, Spec.gidx(ns, i, l), Impl.kt(k), Impl.total(ns, k), G) ==
    True{} : Bool}
  for touch_c: {V2Spec.touches(c, Spec.gidx(ns, i2, l2), Impl.kt(k), Impl.total(ns, k), G) ==
    True{} : Bool}
  for same: {Impl.address(Spec.gidx(ns, i, l), Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G),
      b, Impl.b_lo(Spec.gidx(ns, i, l), Impl.kt(k), Impl.total(ns, k), G)) ==
    Impl.address(Spec.gidx(ns, i2, l2), Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G),
      c, Impl.b_lo(Spec.gidx(ns, i2, l2), Impl.kt(k), Impl.total(ns, k), G)) : Nat}
  {i == i2 : Nat} & {l == l2 : Nat} & {b == c : Nat}

# (c) Workspace fit: under launch_fits every float a contributor flushes (K:240, K:249; token row
# < 16 = the size_m cap, group column < 512) lies in the sb-byte slot region (EXL3_M16G_SLOT_BYTES, H:19),
# below the input-transform scratch at H:242; and the finishing lane's read of slot c < nc (K:335,
# K:339) is exactly the float contributor b_lo + c flushed for that row and column.
law workspace_fit:
  for +ns: List<&2, Nat>
  for +k: Nat
  for +G: Nat
  for +sb: Nat
  for +g: Nat
  for +b: Nat
  for +row: Nat
  for +col: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  for launch: {Impl.launch_fits(Impl.groups(ns), Impl.kt(k), G, sb) == True{} : Bool}
  for group: {Nat.is_lt(g, Impl.groups(ns)) == True{} : Bool}
  for contributor: {V2Spec.touches(b, g, Impl.kt(k), Impl.total(ns, k), G) == True{} : Bool}
  for row16: {Nat.is_lt(row, 16n) == True{} : Bool}
  for col512: {Nat.is_lt(col, 512n) == True{} : Bool}
  {Nat.is_le(Nat.mul(1n+Impl.flush_float(Impl.address(g,
      Impl.max_contrib(Impl.groups(ns), Impl.kt(k), G), b,
      Impl.b_lo(g, Impl.kt(k), Impl.total(ns, k), G)), row, col), 4n), sb) ==
    True{} : Bool}

law finish_reads_slots:
  for +g: Nat
  for +mc: Nat
  for +lo: Nat
  for +c: Nat
  for +r: Nat
  for +ch: Nat
  for +lane: Nat
  for +e: Nat
  {Impl.finish_float(g, mc, c, r, ch, lane, e) ==
    Impl.flush_float(Impl.address(g, mc, Nat.add(lo, c), lo), r,
      Nat.add(Nat.mul(ch, 128n), Nat.add(Nat.mul(lane, 4n), e))) : Nat}

# (d) Finisher (K:328): every job x < jobs is visited by exactly one (block, warp) of the grid, and
# no job past the end is visited.
law finish_jobs_once:
  for +ns: List<&2, Nat>
  for +m: Nat
  for +x: Nat
  for +G: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  {Impl.job_hits(G, x, G, Impl.jobs(Impl.groups(ns), m)) ==
    V2Spec.bit(Nat.is_lt(x, Impl.jobs(Impl.groups(ns), m))) : Nat}

# (d) Every job's output task (K:330-333, K:345-348) is 128 columns of one row of one matrix of the
# bundle, starting at a multiple of 128, inside that matrix's C (row stride n_mat, K:355).
law finish_place:
  for +ns: List<&2, Nat>
  for +m: Nat
  for +x: Nat
  for bundle: {Nat.is_le(Impl.num_mats(ns), 4n) == True{} : Bool}
  for widths: {Spec.widths_ok(ns) == True{} : Bool}
  for inside: {Nat.is_lt(x, Impl.jobs(Impl.groups(ns), m)) == True{} : Bool}
  {Nat.is_lt(Spec.place_mat(Impl.place(ns, x, m)), Impl.num_mats(ns)) == True{} : Bool} &
  {Nat.is_lt(Spec.place_r(Impl.place(ns, x, m)), m) == True{} : Bool} &
  {Nat.mod(Spec.place_col0(Impl.place(ns, x, m)), 128n) == 0n : Nat} &
  {Nat.is_le(Nat.add(Spec.place_col0(Impl.place(ns, x, m)), 128n),
    Spec.width(ns, Spec.place_mat(Impl.place(ns, x, m)))) == True{} : Bool}

# (d) Every task (matrix i, token row r < m, 128-column chunk q of the matrix) is a job's task.
law finish_place_onto:
  for +ns: List<&2, Nat>
  for +m: Nat
  for +i: Nat
  for +r: Nat
  for +q: Nat
  for bundle: {Nat.is_le(Impl.num_mats(ns), 4n) == True{} : Bool}
  for mat_i: {Nat.is_lt(i, Impl.num_mats(ns)) == True{} : Bool}
  for row_r: {Nat.is_lt(r, m) == True{} : Bool}
  for chunk_q: {Nat.is_lt(q, Nat.mul(Spec.ng_at(ns, i), 4n)) == True{} : Bool}
  {Nat.is_lt(V2Spec.encode(V2Spec.Job{Spec.gidx(ns, i, Nat.div(q, 4n)), r, Nat.mod(q, 4n)}, m),
    Impl.jobs(Impl.groups(ns), m)) == True{} : Bool} &
  {Impl.place(ns, V2Spec.encode(V2Spec.Job{Spec.gidx(ns, i, Nat.div(q, 4n)), r, Nat.mod(q, 4n)},
    m), m) == Spec.Place{i, r, Nat.mul(q, 128n)} : Spec.Place}

# (d) No two jobs share a task: with finish_jobs_once, every (matrix, row, 128-column task) is
# finished by exactly one warp of the grid.
law finish_place_injective:
  for +ns: List<&2, Nat>
  for +m: Nat
  for +x: Nat
  for +y: Nat
  for bundle: {Nat.is_le(Impl.num_mats(ns), 4n) == True{} : Bool}
  for inside_x: {Nat.is_lt(x, Impl.jobs(Impl.groups(ns), m)) == True{} : Bool}
  for inside_y: {Nat.is_lt(y, Impl.jobs(Impl.groups(ns), m)) == True{} : Bool}
  for same: {Impl.place(ns, x, m) == Impl.place(ns, y, m) : Spec.Place}
  {x == y : Nat}

# (d) Split-K reduction of launch group g: whatever order the contributors' flushes land in before
# the grid.sync (K:321), the finisher's sum (K:334-341) is the ascending-block left fold of the
# partials of the blocks touching g: it depends only on (G, bundle, k, g).
law reduction_order:
  for +ns: List<&2, Nat>
  for +k: Nat
  for +G: Nat
  for +sb: Nat
  for +g: Nat
  for +order: List<&2, Nat>
  for +ws: List<&2, V2Spec.Sum>
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, k) == True{} : Bool}
  for launch: {Impl.launch_fits(Impl.groups(ns), Impl.kt(k), G, sb) == True{} : Bool}
  for group: {Nat.is_lt(g, Impl.groups(ns)) == True{} : Bool}
  for room: {Nat.is_le(Impl.nc(g, Impl.kt(k), Impl.total(ns, k), G),
    List.length(&2, V2Spec.Sum, ws)) == True{} : Bool}
  for touching: {V2Spec.all_touch(order, g, Impl.kt(k), Impl.total(ns, k), G) == True{} : Bool}
  for complete: {V2Spec.all_arrived(G, order, g, Impl.kt(k), Impl.total(ns, k), G) == True{}
    : Bool}
  {Some{Impl.finish(Impl.arrive(order, ws, Impl.b_lo(g, Impl.kt(k), Impl.total(ns, k), G)),
      Impl.nc(g, Impl.kt(k), Impl.total(ns, k), G))} ==
    V2Spec.reduce(g, Impl.kt(k), Impl.total(ns, k), G) : Maybe<&2, V2Spec.Sum>}

# (d) Conservative extension: a one-matrix bundle [n] is 2001 v2's single-matrix launch (mats = 1):
# the same total and max_contrib and the same finisher sum (hence the same split-K reduction order)
# for every group, arrival order and workspace; and every group g < groups lies in matrix 0 at
# its own index (so weight/output addressing is 2001's single-matrix addressing).
law single_matrix_is_v2:
  for +n: Nat
  for +k: Nat
  for +G: Nat
  for +g: Nat
  for +order: List<&2, Nat>
  for +ws: List<&2, V2Spec.Sum>
  {Impl.total(n <> Nil{}, k) == V2.total(1n, n, k) : Nat} &
  {Impl.max_contrib(Impl.groups(n <> Nil{}), Impl.kt(k), G) ==
    V2.max_contrib(V2.groups(1n, n), V2.kt(k), V2.total(1n, n, k), G) : Nat} &
  {Impl.finish(Impl.arrive(order, ws, Impl.b_lo(g, Impl.kt(k), Impl.total(n <> Nil{}, k), G)),
      Impl.nc(g, Impl.kt(k), Impl.total(n <> Nil{}, k), G)) ==
    V2.finish(V2.arrive(order, ws, V2.b_lo(g, V2.kt(k), V2.total(1n, n, k), G)),
      V2.nc(g, V2.kt(k), V2.total(1n, n, k), G)) : V2Spec.Sum}

law single_matrix_map:
  for +n: Nat
  for +g: Nat
  for group: {Nat.is_lt(g, Impl.groups(n <> Nil{})) == True{} : Bool}
  {Impl.mat(n <> Nil{}, g) == 0n : Nat} &
  {Impl.local(n <> Nil{}, g) == g : Nat}

# (e) Prologue (K:176): every warp job w < total_warps is visited by exactly one (block, warp) of
# the grid, and none past the end.
law prologue_jobs_once:
  for +nm: Nat
  for +m: Nat
  for +k: Nat
  for +w: Nat
  for +G: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  {Impl.pro_hits(G, w, G, Impl.total_warps(nm, m, k)) ==
    V2Spec.bit(Nat.is_lt(w, Impl.total_warps(nm, m, k))) : Nat}

# (e) Every cell (matrix i, token row r, 128-column block c) of the input-transform scratch is the
# job cell_index(i, r, c) < total_warps, whose warp writes it (K:183, H:243) from the same 128
# inputs (K:182) with the matching input scales (K:184) of matrix i (K:178).
law prologue_cover:
  for +nm: Nat
  for +m: Nat
  for +k: Nat
  for +i: Nat
  for +r: Nat
  for +c: Nat
  for aligned: {Nat.is_eq(Nat.mod(k, 128n), 0n) == True{} : Bool}
  for mat_i: {Nat.is_lt(i, nm) == True{} : Bool}
  for row_r: {Nat.is_lt(r, m) == True{} : Bool}
  for block_c: {Nat.is_lt(c, Nat.div(k, 128n)) == True{} : Bool}
  {Nat.is_lt(Spec.cell_index(m, k, i, r, c), Impl.total_warps(nm, m, k)) == True{} : Bool} &
  {Impl.pro_mat(Spec.cell_index(m, k, i, r, c), Impl.per_mat(m, k)) == i : Nat} &
  {Impl.pro_xh(m, k, Spec.cell_index(m, k, i, r, c)) == Spec.xh_cell(m, k, i, r, c) : Nat} &
  {Impl.pro_a(m, k, Spec.cell_index(m, k, i, r, c)) == Spec.a_cell(k, r, c) : Nat} &
  {Impl.pro_suh(m, k, Spec.cell_index(m, k, i, r, c)) == Nat.mul(c, 128n) : Nat}

# (e) Job w writes elements [128 w, 128 w + 128) of the scratch: distinct jobs never overlap, and
# every write stays inside num_mats * size_m * size_k halves (<= EXL3_M16G_XH_BYTES by shape_ok).
law prologue_writes:
  for +nm: Nat
  for +m: Nat
  for +k: Nat
  for +w: Nat
  for aligned: {Nat.is_eq(Nat.mod(k, 128n), 0n) == True{} : Bool}
  for inside: {Nat.is_lt(w, Impl.total_warps(nm, m, k)) == True{} : Bool}
  {Impl.pro_xh(m, k, w) == Nat.mul(w, 128n) : Nat} &
  {Nat.is_le(Nat.add(Impl.pro_xh(m, k, w), 128n), Nat.mul(Nat.mul(nm, m), k)) == True{} : Bool}
