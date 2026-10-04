# Laws: elpis decode GEMMs are never less precise than stock ExLlamaV3 355c6ee, as a theorem about
# ACCUMULATION SCHEDULES (Nat model; no floating-point value is modelled).
#   bend/precision_order.bend  classes and the order int8 < fp16 runs (shorter = more precise) < fp32
#   bend/precision_stock.bend  stock 355c6ee dispatch + schedules, transcribed from the stock sources
#   bend/precision_elpis.bend  elpis routes; the m16 fold schedule from the proven DIET trace models
# Served shapes: attention q|gate / k / v / o, GDN in_proj qkv / z / out_proj, MLP gate / up / down,
# lm_head; verify rows m = 1 .. 8. Outside this contract: float values and rounding, the autotune choice
# the device makes when no record is persisted, the Hadamard / scale epilogues, and whether the served
# process really launches these kernels (the GPU check 0080t3-decode-acc verifies launch names / grids).
import Base
import ./precision_order.bend as Ord
import ./precision_stock.bend as S
import ./precision_elpis.bend as E
import ./m16_diet.bend as Diet
import ./m16_diet_spec.bend as DSpec
import ./gemm_m16_wpart.bend as Wp
import ./precision_parta.bend as PA

# ==== (0) the encoded order ====

# int8 activations < fp16 runs < fp32 accumulation, strictly.
law order_classes:
  for +lo: Nat
  for +hi: Nat
  for +p: Bool
  {Ord.ge(Ord.Runs{lo, hi, p}, Ord.Int8{}) == True{} : Bool} &
  {Ord.ge(Ord.Int8{}, Ord.Runs{lo, hi, p}) == False{} : Bool} &
  {Ord.ge(Ord.Fp32{}, Ord.Runs{lo, hi, p}) == True{} : Bool} &
  {Ord.ge(Ord.Runs{lo, hi, p}, Ord.Fp32{}) == False{} : Bool}

# Inside the fp16-run class, with the same partial precision: a is at least as precise as b exactly
# when a's longest run is no longer than b's (a smaller run length n is more precise).
law shorter_runs_more_precise:
  for +l1: Nat
  for +h1: Nat
  for +l2: Nat
  for +h2: Nat
  for +p: Bool
  {Ord.ge(Ord.Runs{l1, h1, p}, Ord.Runs{l2, h2, p}) == Nat.is_le(h1, h2) : Bool}

# The order is reflexive (identical schedules are equally precise).
law ge_refl:
  for +a: Ord.Acc
  {Ord.ge(a, a) == True{} : Bool}

# Element-wise dominance implies the worst-case order (for a well-formed b).
law dom_implies_ge:
  for +a: Ord.Acc
  for +b: Ord.Acc
  for wfb: {Ord.wf(b) == True{} : Bool}
  for d: {Ord.dom(a, b) == True{} : Bool}
  {Ord.ge(a, b) == True{} : Bool}

# ==== (i) the served table ====

# For every served (op, m), m = 1 .. 8, under the served runtime outcomes (int8 launches succeed, narrow
# GEMV co-residency 164) and the persisted autotune records (gate / up: shape gs = 4, grid gg = 82;
# lm_head: ANY record (hs, hg); o_proj / out_proj / down: ANY fallback fb, never consulted):
#   - class(elpis) >= class(stock) (worst case), and
#   - elpis runs the stock kernel itself, or elpis's longest fp16 run is no longer than stock's
#     shortest one with partials at least as precise (every output element is at least as precise).
law served_never_less_precise:
  for +op: S.Op
  for +m: Nat
  for +gs: Nat
  for +gg: Nat
  for +hs: Nat
  for +hg: Nat
  for +fb: S.Tune
  for rows: {E.in_rows(m, 1n, 8n) == True{} : Bool}
  for s_gs: {gs == S.gu_shape() : Nat}
  for s_gg: {gg == S.gu_grid() : Nat}
  {Ord.ge(E.acc(op, m, S.served_env(), S.tunes(gs, gg, hs, hg, fb)),
    S.acc(op, m, S.served_env(), S.tunes(gs, gg, hs, hg, fb))) == True{} : Bool} &
  {Bool.or(E.is_stock(op, m), Ord.dom(E.acc(op, m, S.served_env(), S.tunes(gs, gg, hs, hg, fb)),
    S.acc(op, m, S.served_env(), S.tunes(gs, gg, hs, hg, fb)))) == True{} : Bool}

# Cross-check of the stock model against /tmp/kernel-work/Int8Linear/decacc/work/partA.md (the table
# computed by analyze_a.py from the same sources and the persisted autotune cache): the stock class of
# every served (op, m) except lm_head (whose class the unary checker cannot normalize; elpis runs that
# same kernel) is partA's run range, in k-values (PA.part_a, bend/precision_parta.bend).
law stock_table_partA:
  for +op: S.Op
  for +m: Nat
  for +gs: Nat
  for +gg: Nat
  for +hs: Nat
  for +hg: Nat
  for +fb: S.Tune
  for rows: {E.in_rows(m, 1n, 8n) == True{} : Bool}
  for s_gs: {gs == S.gu_shape() : Nat}
  for s_gg: {gg == S.gu_grid() : Nat}
  for nh: {PA.not_head(op) == True{} : Bool}
  {S.acc(op, m, S.served_env(), S.tunes(gs, gg, hs, hg, fb)) == PA.part_a(op, m) : Ord.Acc}

# Whatever the narrow-GEMV co-residency nc (a device outcome), the stock GEMV heuristic never picks the
# wide config (FOLD 2 = 32-value runs) at the served exl3_gemm_gr shapes
# (o_proj / out_proj 6144 -> 5120, gate / up 5120 -> 17408, down 17408 -> 5120; 4 bpw, cb 2, m <= 8).
law gemv_never_wide:
  for +m: Nat
  for +nc: Nat
  for rows: {Nat.is_le(m, 8n) == True{} : Bool}
  {S.is_wide(S.gemv_cfg(m, 6144n, 5120n, 4n, 2n, nc)) == False{} : Bool} &
  {S.is_wide(S.gemv_cfg(m, 5120n, 17408n, 4n, 2n, nc)) == False{} : Bool} &
  {S.is_wide(S.gemv_cfg(m, 17408n, 5120n, 4n, 2n, nc)) == False{} : Bool}

# ==== (ii) the elpis m16 fold schedule ====

# Every fp16 run of the served m16g main loop (EXL3_M16_DIET modes 1 / 2, bend/m16_diet.bend diet_m16g),
# for EVERY block slice [s, s + n) and KT >= 1, is at most FOLD = 2 k16 tiles (ext 3023 fold-32: the
# served EXL3_M16_FOLD32 = 1 instance folds every 32 k-values).
law fold_runs_m16g:
  for +s: Nat
  for +n: Nat
  for +KT: Nat
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  {E.runs_ok(Diet.diet_m16g(s, n, KT, E.pf(), E.xr(), E.fold(), E.ws(), E.xi()), 0n, E.fold()) == True{} : Bool}

# The same for the served 8202 layer tail (o_proj / out_proj phase 0 and 8201's gate + up and down
# phases), for every phase slice and every ring entry slot below PF.
law fold_runs_tail:
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
  for kt0: {Nat.is_lt(0n, k0) == True{} : Bool}
  for kt1: {Nat.is_lt(0n, k1) == True{} : Bool}
  for kt2: {Nat.is_lt(0n, k2) == True{} : Bool}
  for ring1: {Nat.is_lt(r1, E.pf()) == True{} : Bool}
  for ring2: {Nat.is_lt(r2, E.pf()) == True{} : Bool}
  {E.runs_ok(Diet.diet_tail(DSpec.Ph{s0, n0, k0}, DSpec.Ph{s1, n1, k1}, DSpec.Ph{s2, n2, k2}, r1, r2, E.pf(),
    E.xr(), E.fold(), E.ws(), E.xi()), 0n, E.fold()) == True{} : Bool}

# The bound is attained: block 0 of the served GDN in_proj m16g launch (2105 weights (100, 91), grid 164,
# KT 320) has a run of exactly FOLD = 2 tiles; and the m16 class is fp16 runs of 16 .. 16 FOLD = 32
# k-values with fp32 partials.
law fold_exact:
  {E.max_run(Diet.diet_m16g(0n, Wp.start(1n, Nat.mul(Wp.groups_gdn(), Wp.kt_served()), Wp.grid_served(),
      Wp.nsm_served(), Wp.w0_served(), Wp.w1_served()), Wp.kt_served(), E.pf(), E.xr(), E.fold(), E.ws(), E.xi()),
    0n, 0n) == E.fold() : Nat} &
  {E.m16_acc() == Ord.Runs{16n, 32n, True{}} : Ord.Acc}

# ==== (iii) the stock partition, generic ====

# For every slice start x, length and tiles_k >= 1, the fp16 runs of the stock main loop (fold only at a
# column end or the slice end) are exactly the maximal pieces of the slice's consecutive k-tiles that lie
# in one output column.
law stock_runs_are_column_pieces:
  for +iters: Nat
  for +x: Nat
  for +tk: Nat
  for tpos: {Nat.is_lt(0n, tk) == True{} : Bool}
  {S.runs(S.loop(iters, Nat.mod(x, tk), Nat.div(x, tk), tk), 0n) == S.col_runs(iters, x, tk, 0n) : List<&2, Nat>}

# The one-pass grid statistics equal the per-block reference (each block from its own slice_beg).
law grid_stat_is_ref:
  for left: Nat
  for +b: Nat
  for +T: Nat
  for +G: Nat
  for +tk: Nat
  for st: S.Stat
  {S.grid_stat(left, b, S.slice_beg(b, T, G), T, G, tk, st) == S.grid_ref(left, b, T, G, tk, st) : S.Stat}
