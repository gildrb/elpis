# Error-bound laws of the served decode GEMMs (bend/err_gemm.bend paths, bend/err_bound.bend
# vocabulary): for every served (op, m), m = 1 .. 8 verify rows, and every leaf (input term) of an
# output element, elpis's rounding path is dominated at exchange rate x = 128 by the path of a real
# worst leaf of the same output element in stock ExLlamaV3 355c6ee's non-speculative M = 1 decode
# (Eb.dom; with err_bound_laws.bend dom_sigma: elpis's worst-case error bound for that element is
# no larger than stock's). Where elpis runs stock's own arithmetic the paths are equal (dom_refl).
#
# Named hypotheses (each a property of the served runtime, not of the arithmetic):
#   H_route   the served kernels: m1map-map.json kernel_map 'verify' (exl3_gemm_m16g_kernel for the
#             projections, exl3_tail_m16_kernel for o_proj / out_proj + MLP, gdn_conv_rule_norm_kernel
#             for b/a, stock exl3_gemm_kernel for lm_head), routes of bend/precision_elpis.bend
#             (m = 1 projections: the site's sliced exl3_mgemm, 2102 M16G_OLD).
#   H_stock   stock M = 1 dispatch with the default environment (EXL3_INT8_GEMV unset = 2, int8
#             launches succeed: precision_stock.bend served_env) and the persisted autotune records
#             of precision_stock.bend (attention bundle shape 4 grid 4, GDN bundle shape 4 grid 10,
#             lm_head shape 4 grid 82: bend/lmhead.bend served_tab); stock b/a through
#             BC_GatedDeltaNetSplit's gdn_ba_gemv (fp16 b/a weights, modules/gated_delta_net.py:658).
#   H_carrier the m16g route writes the same C carriers as stock's bundles (attention fp16 q / kv
#             buffers, GDN fp32 qkv / z; libtorch/attention.cpp:553-563, gated_delta_net.cpp:278).
#   H_fmad    nvcc contracts the int8 epilogue's `acc += q_s * (float) p` and `k_inv * acc + corr`
#             into fma (default --fmad=true): the stock count used is the smaller, contracted one.
#   Leaf coordinates. Laws (9) proj_m16g_served and (10) tail_served take tr and pa from the models:
#             tr = the tile's run position in the served m16g / tail DIET trace, 1 <= tr <= FO = 2 by
#             bend/err_gemm_runs_laws.bend tr_pos / tr_bound_m16g / tr_bound_tail (from fold_runs_m16g /
#             fold_runs_tail, ported there and kernel-checked); pa = the finisher adds of the leaf's slot,
#             1 + pa <= grid by gemm_m16_wpart_laws.bend contrib_bounds (proof imported). Remaining
#             coordinate bound, named H_seg: fa (folds of the later runs of the leaf's segment) <= KT,
#             because a segment lies in one group of KT k-tiles (G16:401 seg_end, checked by
#             err_gemm_diff.py); own <= 1 by definition. The tail phases use the same weighted
#             partition (8205, m16_wsched.bend) at the phase's (groups, KT).
#   H_pieces  the stock column-piece model: a block's fp16 run in a column is its slice cut to the
#             column (the stock loop's runs are exactly these pieces: err_gemm_runs_laws.bend
#             stock_runs_are_column_pieces, kernel-checked there) and a column's pieces meet in
#             descending block order (GI:834-841 lock_i, checked by err_gemm_diff.py). The slice
#             partition itself is proven here (law partition_exact).
#   H_ba      the elpis b/a leaf structure (10-fmaf chains, 5-level shuffle tree, 16 warp partials from
#             0.0f, ks variant served: S <= 8, k / 2 = 2560) as modelled by bend/gdn_ba_ksplit.bend task.
# Not counted (common to both sides at the op boundary, or outside it): the producer of the fp16
# input x, the consumer of the output; bf16 steps do not occur on these paths.
import Base
import ./err_bound.bend as Eb
import ./err_gemm.bend as E
import ./lmhead.bend as LH
import ./gemm_m16_wpart.bend as Wp
import ./tail_m16_sched.bend as TS
import ./mlp_m16_sched.bend as Mlp
import ./err_gemm_runs.bend as R
import ./precision_elpis.bend as PE
import ./m16_diet.bend as Diet
import ./m16_diet_spec.bend as DSpec

# (1) Projections at m = 2 .. 8 (exl3_gemm_m16g_kernel, fp16 runs of <= FO = 2 k16 tiles, fp32
# split-K): every leaf of an output element in bundle column tile nt is dominated by the stock
# witness of that element (attention: 160 fp16 MMAs + fp16 partials; GDN: 128 fp16 MMAs).
law proj_m16g_dom:
  for +op: E.Op
  for +m: Nat
  for +nt: Nat
  for +tr: Nat
  for +own: Nat
  for +fa: Nat
  for +pa: Nat
  for pj: {E.is_proj(op) == True{} : Bool}
  for rows: {Bool.and(Nat.is_le(2n, m), Nat.is_le(m, 8n)) == True{} : Bool}
  for col: {Nat.is_le(1n+nt, E.proj_tn(op)) == True{} : Bool}
  for leaf: {E.m16_leaf(op, tr, own, fa, pa) == True{} : Bool}
  {Eb.dom(128n, E.m16_path(op, tr, own, fa, pa), E.proj_wit(op, nt)) == True{} : Bool}

# (2) Projections at m = 1: elpis runs stock's sliced exl3_mgemm, every leaf (b, j) of an element in
# column tile nt has stock's path.
law proj_m1_dom:
  for +op: E.Op
  for +nt: Nat
  for +b: Nat
  for +j: Nat
  for pj: {E.is_proj(op) == True{} : Bool}
  for lf: {E.proj_leaf(op, nt, b, j) == True{} : Bool}
  {Eb.dom(128n, E.proj_m1(op, nt, b, j), E.proj_stock(op, nt, b, j)) == True{} : Bool}

# (3) o_proj, out_proj, gate, up, down at m = 1 .. 8 (exl3_tail_m16_kernel phases 0 / 1 / 2): every
# leaf is dominated by the stock int8 GEMV witness (one q8 step), for every k-split count ks.
law tail_dom:
  for +op: E.Op
  for +m: Nat
  for +ks: Nat
  for +tr: Nat
  for +own: Nat
  for +fa: Nat
  for +pa: Nat
  for tl: {E.is_tail(op) == True{} : Bool}
  for rows: {Bool.and(Nat.is_le(1n, m), Nat.is_le(m, 8n)) == True{} : Bool}
  for leaf: {E.m16_leaf(op, tr, own, fa, pa) == True{} : Bool}
  {Eb.dom(128n, E.m16_path(op, tr, own, fa, pa), E.tail_wit(op, ks)) == True{} : Bool}

# (4) GDN b/a at m = 1 .. 8 (5106 k-split partial FMAs, fp32 throughout): every leaf (chain position
# p, warp w) is dominated by the stock gdn_ba_gemv witness (a 160-fmaf lane chain).
law ba_dom:
  for +m: Nat
  for +p: Nat
  for +w: Nat
  for +hb: Bool
  for rows: {Bool.and(Nat.is_le(1n, m), Nat.is_le(m, 8n)) == True{} : Bool}
  for hp: {Nat.is_lt(p, 10n) == True{} : Bool}
  for hw: {Nat.is_lt(w, 16n) == True{} : Bool}
  {Eb.dom(128n, E.ba_path(p, w, hb), E.ba_wit(hb)) == True{} : Bool}

# (5) lm_head (the stock exl3_gemm_kernel on both sides): for every matrix k x n, column tile nt,
# leaf (i, j, g) and row r < m <= 8, row r's path in the m-row verify call equals row 0's in the
# 1-row stock call (bend/lmhead_laws.bend served_order), hence is dominated by it.
law head_dom:
  for +k: Nat
  for +n: Nat
  for +nt: Nat
  for +m: Nat
  for +r: Nat
  for +i: Nat
  for +j: Nat
  for +g: Nat
  for +c32: Bool
  for +hr: {Nat.is_lt(r, m) == True{} : Bool}
  for +hm: {Nat.is_le(m, 8n) == True{} : Bool}
  {E.head_path(k, n, nt, m, r, i, j, g, c32) == E.head_path(k, n, nt, 1n, 0n, i, j, g, c32) : Eb.Path} &
  {Eb.dom(128n, E.head_path(k, n, nt, m, r, i, j, g, c32), E.head_path(k, n, nt, 1n, 0n, i, j, g, c32)) == True{} : Bool}

# (6) The stock witnesses are real leaves: the first k-tile of block wit_b's piece of every column
# tile of a slice (attention: blocks 1, 3 of 4; GDN: blocks 1, 3, 6, 8 of 10), and their paths are
# the stated ones (attention: 160 t16, 7 r16, 17 r32; GDN: 128 t16, 3 r16, 19 r32).
law witness_leaves:
  for +op: E.Op
  for +nt: Nat
  for pj: {E.is_proj(op) == True{} : Bool}
  for col: {Nat.is_le(1n+nt, E.proj_tn(op)) == True{} : Bool}
  {E.proj_leaf(op, nt, E.wit_b(op, nt), 0n) == True{} : Bool} &
  {E.proj_wit(op, nt) == E.psel(E.is_attn(op), Eb.Path{17n, 0n, 7n, 160n, 0n, 0n, 0n, 0n},
    Eb.Path{19n, 0n, 3n, 128n, 0n, 0n, 0n, 0n}) : Eb.Path}

# (7) The literal shapes of bend/err_gemm.bend are the schedule models' values: m16g KT and grid
# (gemm_m16_wpart.bend), tail KT0 / KT1 and grid (tail_m16_sched.bend, mlp_m16_sched.bend), KT2 via
# inter = 1088 * 16 and law kt2_of_mul, the stock bundles' slice tiles and k-tiles (lmhead.bend tiles /
# tiles_k at shape 4) and the stock b/a lane chain length 2 * (5120 / 2 / 32).
law shape_literals:
  {Wp.kt_served() == 320n : Nat} &
  {TS.kt0(TS.kin()) == 384n : Nat} &
  {Mlp.kt1(Mlp.hidden()) == 320n : Nat} &
  {Nat.mul(1088n, 16n) == Mlp.inter() : Nat} &
  {Wp.grid_served() == 164n : Nat} &
  {Mlp.grid() == 164n : Nat} &
  {LH.tiles(5120n, 1024n, 4n) == 640n : Nat} &
  {LH.tiles(5120n, 2048n, 4n) == 1280n : Nat} &
  {LH.tiles_k(5120n, 4n) == 320n : Nat} &
  {Nat.mul(2n, Nat.div(Nat.div(5120n, 2n), 32n)) == E.ba_chain() : Nat}

# The down phase's k-tiles: KT2(x * 16) = x (mlp_m16_sched.bend kt2 = k / 16), so KT2(inter) = 1088.
law kt2_of_mul:
  for +x: Nat
  {Mlp.kt2(Nat.mul(x, 16n)) == x : Nat}

# (8) The stock bundles' slice partition (GI:98-100, lmhead.bend slice_beg: T b / G) is exact: block b
# owns k-tiles [c b, c (b + 1)) with c = T / G = 640 / 4 = 160 (attention) and 1280 / 10 = 128 (GDN),
# the slice width the column-piece model of bend/err_gemm.bend uses.
law partition_exact:
  for +b: Nat
  {LH.slice_beg(b, 640n, 4n) == Nat.mul(160n, b) : Nat} &
  {LH.slice_beg(b, 1280n, 10n) == Nat.mul(128n, b) : Nat}

# (9) The m16g leaves of the served traces, with tr and pa derived instead of assumed: for every block
# slice [s, s + n) (KT >= 1) of the served m16g DIET trace (bend/m16_diet.bend diet_m16g at the served
# Exl3M16Cfg) and every tile event i of it, the leaf has tr = its run position R.tr_at (1 <= tr <= FO:
# err_gemm_runs_laws.bend tr_pos / tr_bound_m16g, from fold_runs_m16g) and, in finisher slot c of
# group g of the weighted partition (gemm_m16_wpart.bend; grid G = the launch's 164), pa =
# E.fin_adds(c, nc(g)) (1 + pa <= G: gemm_m16_wpart_laws.bend contrib_bounds). Its path is dominated
# by the stock witness. own <= 1 and fa <= KT remain coordinates (see H_leaf).
law proj_m16g_served:
  for +op: E.Op
  for +m: Nat
  for +nt: Nat
  for +s: Nat
  for +n: Nat
  for +KT: Nat
  for +i: Nat
  for +own: Nat
  for +fa: Nat
  for +groups: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +g: Nat
  for +c: Nat
  for pj: {E.is_proj(op) == True{} : Bool}
  for rows: {Bool.and(Nat.is_le(2n, m), Nat.is_le(m, 8n)) == True{} : Bool}
  for col: {Nat.is_le(1n+nt, E.proj_tn(op)) == True{} : Bool}
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for it: {R.it_at(Diet.diet_m16g(s, n, KT, PE.pf(), PE.xr(), PE.fold(), PE.ws(), PE.xi()), i) == True{} : Bool}
  for ho: {Nat.is_le(own, 1n) == True{} : Bool}
  for hf: {Nat.is_le(fa, E.op_kt(op)) == True{} : Bool}
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for group: {Nat.is_lt(g, groups) == True{} : Bool}
  for s_grid: {G == E.op_grid(op) : Nat}
  {Eb.dom(128n, E.m16_path(op, R.tr_at(Diet.diet_m16g(s, n, KT, PE.pf(), PE.xr(), PE.fold(), PE.ws(), PE.xi()), i),
    own, fa, E.fin_adds(c, Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1))), E.proj_wit(op, nt)) == True{} : Bool}

# (10) The same for the tail ops on the served 8202 tail trace (all three phases; every phase slice,
# ring entry slots below PF: tr_bound_tail), pa from the op's phase partition (groups, KT of the phase).
law tail_served:
  for +op: E.Op
  for +m: Nat
  for +ks: Nat
  for +s0: Nat
  for +n0: Nat
  for +k0: Nat
  for +s1: Nat
  for +n1: Nat
  for +k1: Nat
  for +s2: Nat
  for +n2: Nat
  for +k2: Nat
  for +r1: Nat
  for +r2: Nat
  for +i: Nat
  for +own: Nat
  for +fa: Nat
  for +groups: Nat
  for +KT: Nat
  for +G: Nat
  for +nsm: Nat
  for +w0: Nat
  for +w1: Nat
  for +g: Nat
  for +c: Nat
  for tl: {E.is_tail(op) == True{} : Bool}
  for rows: {Bool.and(Nat.is_le(1n, m), Nat.is_le(m, 8n)) == True{} : Bool}
  for kt0: {Nat.is_lt(0n, k0) == True{} : Bool}
  for kt1: {Nat.is_lt(0n, k1) == True{} : Bool}
  for kt2: {Nat.is_lt(0n, k2) == True{} : Bool}
  for ring1: {Nat.is_lt(r1, PE.pf()) == True{} : Bool}
  for ring2: {Nat.is_lt(r2, PE.pf()) == True{} : Bool}
  for it: {R.it_at(Diet.diet_tail(DSpec.Ph{s0, n0, k0}, DSpec.Ph{s1, n1, k1}, DSpec.Ph{s2, n2, k2}, r1, r2, PE.pf(),
    PE.xr(), PE.fold(), PE.ws(), PE.xi()), i) == True{} : Bool}
  for ho: {Nat.is_le(own, 1n) == True{} : Bool}
  for hf: {Nat.is_le(fa, E.op_kt(op)) == True{} : Bool}
  for w0pos: {Nat.is_lt(0n, w0) == True{} : Bool}
  for w1pos: {Nat.is_lt(0n, w1) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  for group: {Nat.is_lt(g, groups) == True{} : Bool}
  for s_grid: {G == E.op_grid(op) : Nat}
  {Eb.dom(128n, E.m16_path(op, R.tr_at(Diet.diet_tail(DSpec.Ph{s0, n0, k0}, DSpec.Ph{s1, n1, k1}, DSpec.Ph{s2, n2, k2},
      r1, r2, PE.pf(), PE.xr(), PE.fold(), PE.ws(), PE.xi()), i),
    own, fa, E.fin_adds(c, Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1))), E.tail_wit(op, ks)) == True{} : Bool}
