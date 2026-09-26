# Laws of the wide-tile prefill GEMM of ext patch 3011 (exllamav3_ext/hgemm_f16acc_wide.cuh and the route in
# hgemm_f16acc.cu) over the Nat / U32 model hgemm_wide.bend and the independent reference hgemm_wide_spec.bend.
# Shipped configuration: 128 x 128 x 32 tiles, 2 x 2 warps of 64 x 64, GROUP_M = G (the kernel passes 8).
# Scope: index maps, loop orders and the route. Outside it: C int overflow (host: M, N, K < 2^31), the
# ldmatrix / mma fragment register layouts (checked against the patch's own expressions by the finite
# differential test hgemm_wide_diff.py), fp16 / fp32 rounding itself (the same operations in the same order
# are the same bits; measured bit-exact on the GPU at every served shape), and the hardware.
import Base
import ./hgemm_wide.bend as Impl
import ./hgemm_wide_spec.bend as Spec

# ==== (1) every output tile and element is written exactly once, partial edge tiles included ====

# The grouped raster maps every block id of the grid to a tile of the grid ...
law raster_in_range:
  for +b: Nat
  for +G: Nat
  for +gn: Nat
  for +gm: Nat
  for gpos: {Nat.is_lt(0n, G) == True{} : Bool}
  for npos: {Nat.is_lt(0n, gn) == True{} : Bool}
  for inside: {Nat.is_lt(b, Nat.mul(gm, gn)) == True{} : Bool}
  {Nat.is_lt(Impl.tile_m(b, G, gn, gm), gm) == True{} : Bool} &
  {Nat.is_lt(Impl.tile_n(b, G, gn, gm), gn) == True{} : Bool}

# ... no two blocks compute the same tile ...
law raster_inj:
  for +b1: Nat
  for +b2: Nat
  for +G: Nat
  for +gn: Nat
  for +gm: Nat
  for gpos: {Nat.is_lt(0n, G) == True{} : Bool}
  for npos: {Nat.is_lt(0n, gn) == True{} : Bool}
  for in1: {Nat.is_lt(b1, Nat.mul(gm, gn)) == True{} : Bool}
  for in2: {Nat.is_lt(b2, Nat.mul(gm, gn)) == True{} : Bool}
  for same_m: {Impl.tile_m(b1, G, gn, gm) == Impl.tile_m(b2, G, gn, gm) : Nat}
  for same_n: {Impl.tile_n(b1, G, gn, gm) == Impl.tile_n(b2, G, gn, gm) : Nat}
  {b1 == b2 : Nat}

# ... and every tile is computed, by the block Spec.bid_of names.
law raster_cover:
  for +tm: Nat
  for +tn: Nat
  for +G: Nat
  for +gn: Nat
  for +gm: Nat
  for gpos: {Nat.is_lt(0n, G) == True{} : Bool}
  for tmin: {Nat.is_lt(tm, gm) == True{} : Bool}
  for tnin: {Nat.is_lt(tn, gn) == True{} : Bool}
  {Nat.is_lt(Spec.bid_of(tm, tn, G, gn, gm), Nat.mul(gm, gn)) == True{} : Bool} &
  {Impl.tile_m(Spec.bid_of(tm, tn, G, gn, gm), G, gn, gm) == tm : Nat} &
  {Impl.tile_n(Spec.bid_of(tm, tn, G, gn, gm), G, gn, gm) == tn : Nat}

# Inside a tile: two stores (thread < 128, i < 4, j < 8, h < 2, e < 2) of the same element are the same store ...
law tile_store_inj:
  for +t1: Nat
  for +i1: Nat
  for +j1: Nat
  for +h1: Nat
  for +e1: Nat
  for +t2: Nat
  for +i2: Nat
  for +j2: Nat
  for +h2: Nat
  for +e2: Nat
  for tt1: {Nat.is_lt(t1, 128n) == True{} : Bool}
  for ii1: {Nat.is_lt(i1, 4n) == True{} : Bool}
  for jj1: {Nat.is_lt(j1, 8n) == True{} : Bool}
  for hh1: {Nat.is_lt(h1, 2n) == True{} : Bool}
  for ee1: {Nat.is_lt(e1, 2n) == True{} : Bool}
  for tt2: {Nat.is_lt(t2, 128n) == True{} : Bool}
  for ii2: {Nat.is_lt(i2, 4n) == True{} : Bool}
  for jj2: {Nat.is_lt(j2, 8n) == True{} : Bool}
  for hh2: {Nat.is_lt(h2, 2n) == True{} : Bool}
  for ee2: {Nat.is_lt(e2, 2n) == True{} : Bool}
  for same_r: {Impl.row_of(0n, t1, i1, h1) == Impl.row_of(0n, t2, i2, h2) : Nat}
  for same_c: {Impl.col_of(0n, t1, j1, e1) == Impl.col_of(0n, t2, j2, e2) : Nat}
  {t1 == t2 : Nat} & {i1 == i2 : Nat} & {j1 == j2 : Nat} & {h1 == h2 : Nat} & {e1 == e2 : Nat}

# ... every store lands inside the tile ...
law tile_store_in:
  for +t: Nat
  for +i: Nat
  for +j: Nat
  for +h: Nat
  for +e: Nat
  for tt: {Nat.is_lt(t, 128n) == True{} : Bool}
  for ii: {Nat.is_lt(i, 4n) == True{} : Bool}
  for jj: {Nat.is_lt(j, 8n) == True{} : Bool}
  for hh: {Nat.is_lt(h, 2n) == True{} : Bool}
  for ee: {Nat.is_lt(e, 2n) == True{} : Bool}
  {Nat.is_lt(Impl.row_of(0n, t, i, h), 128n) == True{} : Bool} &
  {Nat.is_lt(Impl.col_of(0n, t, j, e), 128n) == True{} : Bool}

# ... and every element (r, c) of the tile is stored, by its m16n8 accumulator owner.
law tile_store_cover:
  for +r: Nat
  for +c: Nat
  for rr: {Nat.is_lt(r, 128n) == True{} : Bool}
  for cc: {Nat.is_lt(c, 128n) == True{} : Bool}
  {Nat.is_lt(Spec.own_tid(r, c), 128n) == True{} : Bool} &
  {Nat.is_lt(Spec.own_i(r), 4n) == True{} : Bool} &
  {Nat.is_lt(Spec.own_j(c), 8n) == True{} : Bool} &
  {Nat.is_lt(Spec.own_h(r), 2n) == True{} : Bool} &
  {Nat.is_lt(Spec.own_e(c), 2n) == True{} : Bool} &
  {Impl.row_of(0n, Spec.own_tid(r, c), Spec.own_i(r), Spec.own_h(r)) == r : Nat} &
  {Impl.col_of(0n, Spec.own_tid(r, c), Spec.own_j(c), Spec.own_e(c)) == c : Nat}

# A block's stores are its tile's: the tile origin (bm, bn) is added to the in-tile coordinates.
law store_offset:
  for +bm: Nat
  for +bn: Nat
  for +t: Nat
  for +i: Nat
  for +j: Nat
  for +h: Nat
  for +e: Nat
  {Impl.row_of(bm, t, i, h) == Nat.add(bm, Impl.row_of(0n, t, i, h)) : Nat} &
  {Impl.col_of(bn, t, j, e) == Nat.add(bn, Impl.col_of(0n, t, j, e)) : Nat}

# The launch grid covers every row: M <= grid_m(M) * 128 (partial edge tiles; the rows >= M of the last
# M-stripe are exactly the stores the `row >= M` guard drops, Impl.stored).
law grid_rows:
  for +M: Nat
  {Nat.is_le(M, Nat.mul(Impl.grid_m(M), 128n)) == True{} : Bool}

# Composed over a launch (grid gn x grid_m(M), the H: launch): two stores of any blocks of the grid (a
# block, thread < 128, i < 4, j < 8, h < 2, e < 2) that write the same output element are the same store ...
law global_inj:
  for +by1: Nat
  for +bx1: Nat
  for +t1: Nat
  for +i1: Nat
  for +j1: Nat
  for +h1: Nat
  for +e1: Nat
  for +by2: Nat
  for +bx2: Nat
  for +t2: Nat
  for +i2: Nat
  for +j2: Nat
  for +h2: Nat
  for +e2: Nat
  for +G: Nat
  for +gn: Nat
  for +gm: Nat
  for gpos: {Nat.is_lt(0n, G) == True{} : Bool}
  for yy1: {Nat.is_lt(by1, gm) == True{} : Bool}
  for xx1: {Nat.is_lt(bx1, gn) == True{} : Bool}
  for tt1: {Nat.is_lt(t1, 128n) == True{} : Bool}
  for ii1: {Nat.is_lt(i1, 4n) == True{} : Bool}
  for jj1: {Nat.is_lt(j1, 8n) == True{} : Bool}
  for hh1: {Nat.is_lt(h1, 2n) == True{} : Bool}
  for ee1: {Nat.is_lt(e1, 2n) == True{} : Bool}
  for yy2: {Nat.is_lt(by2, gm) == True{} : Bool}
  for xx2: {Nat.is_lt(bx2, gn) == True{} : Bool}
  for tt2: {Nat.is_lt(t2, 128n) == True{} : Bool}
  for ii2: {Nat.is_lt(i2, 4n) == True{} : Bool}
  for jj2: {Nat.is_lt(j2, 8n) == True{} : Bool}
  for hh2: {Nat.is_lt(h2, 2n) == True{} : Bool}
  for ee2: {Nat.is_lt(e2, 2n) == True{} : Bool}
  for same_r: {Impl.grow(by1, bx1, t1, i1, h1, G, gn, gm) == Impl.grow(by2, bx2, t2, i2, h2, G, gn, gm) : Nat}
  for same_c: {Impl.gcol(by1, bx1, t1, j1, e1, G, gn, gm) == Impl.gcol(by2, bx2, t2, j2, e2, G, gn, gm) : Nat}
  {by1 == by2 : Nat} & {bx1 == bx2 : Nat} & {t1 == t2 : Nat} & {i1 == i2 : Nat} & {j1 == j2 : Nat} &
  {h1 == h2 : Nat} & {e1 == e2 : Nat}

# ... and every element (R, C) with R < M, C < 128 gn, partial last M-stripe included, is stored (the store
# passes the `row >= M` guard) by the block Spec.own_block names and its tile owner.
law global_cover:
  for +R: Nat
  for +C: Nat
  for +M: Nat
  for +G: Nat
  for +gn: Nat
  for gpos: {Nat.is_lt(0n, G) == True{} : Bool}
  for rr: {Nat.is_lt(R, M) == True{} : Bool}
  for cc: {Nat.is_lt(C, Nat.mul(gn, 128n)) == True{} : Bool}
  {Nat.is_lt(Spec.own_by(R, C, G, gn, Impl.grid_m(M)), Impl.grid_m(M)) == True{} : Bool} &
  {Nat.is_lt(Spec.own_bx(R, C, G, gn, Impl.grid_m(M)), gn) == True{} : Bool} &
  {Impl.grow(Spec.own_by(R, C, G, gn, Impl.grid_m(M)), Spec.own_bx(R, C, G, gn, Impl.grid_m(M)),
    Spec.own_tid(Nat.mod(R, 128n), Nat.mod(C, 128n)), Spec.own_i(Nat.mod(R, 128n)), Spec.own_h(Nat.mod(R, 128n)),
    G, gn, Impl.grid_m(M)) == R : Nat} &
  {Impl.gcol(Spec.own_by(R, C, G, gn, Impl.grid_m(M)), Spec.own_bx(R, C, G, gn, Impl.grid_m(M)),
    Spec.own_tid(Nat.mod(R, 128n), Nat.mod(C, 128n)), Spec.own_j(Nat.mod(C, 128n)), Spec.own_e(Nat.mod(C, 128n)),
    G, gn, Impl.grid_m(M)) == C : Nat} &
  {Impl.stored(Spec.own_by(R, C, G, gn, Impl.grid_m(M)), Spec.own_bx(R, C, G, gn, Impl.grid_m(M)),
    Spec.own_tid(Nat.mod(R, 128n), Nat.mod(C, 128n)), Spec.own_i(Nat.mod(R, 128n)), Spec.own_h(Nat.mod(R, 128n)),
    G, gn, Impl.grid_m(M), M) == True{} : Bool}

# ==== (2) per-element accumulation order: the served kernel's, so the same bits ====

# For every K = 64 L (the host requires K % 64 == 0 for both kernels), every output element of the wide
# kernel adds the same fp16 partials in the same order as the served f16acc kernel: one per 32-wide K slice,
# ascending, each two m16n8k16 MMAs (k offsets 32 s, 32 s + 16) issued into a +0 fp16 accumulator.
law k_order:
  for +L: Nat
  {Impl.wide_acc(Nat.mul(L, 64n)) == Spec.slices(Nat.mul(L, 2n), 0n) : List<&2, List<&2, Nat>>} &
  {Impl.served_acc(Nat.mul(L, 64n)) == Spec.slices(Nat.mul(L, 2n), 0n) : List<&2, List<&2, Nat>>}

# ==== (3) cp.async stage writes cover each stage exactly once ====

# A stage (BM x BK halves = 512 chunks of 8): the 4 iterations of the 128 threads write distinct chunks ...
law a_stage_inj:
  for +t1: Nat
  for +i1: Nat
  for +t2: Nat
  for +i2: Nat
  for tt1: {Nat.is_lt(t1, 128n) == True{} : Bool}
  for ii1: {Nat.is_lt(i1, 4n) == True{} : Bool}
  for tt2: {Nat.is_lt(t2, 128n) == True{} : Bool}
  for ii2: {Nat.is_lt(i2, 4n) == True{} : Bool}
  for same: {Impl.a_dest(t1, i1) == Impl.a_dest(t2, i2) : Nat}
  {t1 == t2 : Nat} & {i1 == i2 : Nat}

# ... every write is a whole chunk inside the stage ...
law a_stage_in:
  for +t: Nat
  for +i: Nat
  for tt: {Nat.is_lt(t, 128n) == True{} : Bool}
  for ii: {Nat.is_lt(i, 4n) == True{} : Bool}
  {Nat.is_lt(Nat.div(Impl.a_dest(t, i), 8n), 512n) == True{} : Bool} &
  {Nat.mod(Impl.a_dest(t, i), 8n) == 0n : Nat}

# ... and every chunk s < 512 is written, by thread c % 128 in iteration c / 128, c = Spec.a_own_c(s).
law a_stage_cover:
  for +s: Nat
  for ss: {Nat.is_lt(s, 512n) == True{} : Bool}
  {Nat.is_lt(Nat.mod(Spec.a_own_c(s), 128n), 128n) == True{} : Bool} &
  {Nat.is_lt(Nat.div(Spec.a_own_c(s), 128n), 4n) == True{} : Bool} &
  {Impl.a_dest(Nat.mod(Spec.a_own_c(s), 128n), Nat.div(Spec.a_own_c(s), 128n)) == Nat.mul(s, 8n) : Nat}

# B stage (BK x BN halves = 512 chunks of 8): the same three facts.
law b_stage_inj:
  for +t1: Nat
  for +i1: Nat
  for +t2: Nat
  for +i2: Nat
  for tt1: {Nat.is_lt(t1, 128n) == True{} : Bool}
  for ii1: {Nat.is_lt(i1, 4n) == True{} : Bool}
  for tt2: {Nat.is_lt(t2, 128n) == True{} : Bool}
  for ii2: {Nat.is_lt(i2, 4n) == True{} : Bool}
  for same: {Impl.b_dest(t1, i1) == Impl.b_dest(t2, i2) : Nat}
  {t1 == t2 : Nat} & {i1 == i2 : Nat}

law b_stage_in:
  for +t: Nat
  for +i: Nat
  for tt: {Nat.is_lt(t, 128n) == True{} : Bool}
  for ii: {Nat.is_lt(i, 4n) == True{} : Bool}
  {Nat.is_lt(Nat.div(Impl.b_dest(t, i), 8n), 512n) == True{} : Bool} &
  {Nat.mod(Impl.b_dest(t, i), 8n) == 0n : Nat}

law b_stage_cover:
  for +s: Nat
  for ss: {Nat.is_lt(s, 512n) == True{} : Bool}
  {Nat.is_lt(Nat.mod(Spec.b_own_c(s), 128n), 128n) == True{} : Bool} &
  {Nat.is_lt(Nat.div(Spec.b_own_c(s), 128n), 4n) == True{} : Bool} &
  {Impl.b_dest(Nat.mod(Spec.b_own_c(s), 128n), Nat.div(Spec.b_own_c(s), 128n)) == Nat.mul(s, 8n) : Nat}

# ==== (4) route: total over the served shapes, the served kernel for anything else ====

# The patch's table is exactly the served projection shapes of the model.
law route_table:
  {Impl.wide_shapes() == Spec.served_shapes() : List<&2, Spec.HwShape>}

# Every routed shape meets the wide kernel's requirements (N % 128 == 0, K % 32 == 0).
law route_fits:
  {Spec.all_fit(Impl.wide_shapes()) == True{} : Bool}

# For every switch value, device, batch, M and shape the route is the intended one: an error for a
# malformed switch, the wide kernel exactly on (on, sm86, unbatched, M >= 1024, served shape), else the
# served kernel.
law route_total:
  for env: Spec.HwEnv
  for +major: U32
  for +minor: U32
  for +batch: U32
  for +M: U32
  for +K: U32
  for +N: U32
  for +f: Bool
  {Impl.route(env, major, minor, batch, M, K, N, f) ==
    Spec.route(env, Bool.and(U32.is_eq(major, 8), U32.is_eq(minor, 6)), U32.is_eq(batch, 1), U32.is_ge(M, 1024),
      Spec.member(Spec.served_shapes(), Spec.HwShape{K, N, f})) : Spec.HwRoute}
