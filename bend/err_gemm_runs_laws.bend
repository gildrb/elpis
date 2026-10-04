# Verdict-safe port of three schedule laws of bend/precision_laws.bend (same statements, same models:
# bend/precision_elpis.bend, bend/precision_stock.bend, bend/m16_diet.bend): the fp16 runs of the
# served m16g and 8202-tail DIET traces are at most FOLD = 2 k16 tiles for every block slice, and the
# stock tensor-core loop's fp16 runs are exactly the column pieces of a block's slice. Proven
# symbolically in bend/err_gemm_runs_proof.bend (no closed unary product is normalized), so the
# error-bound laws of bend/err_gemm_laws.bend can use them under --verdict. Plus two corollaries the
# error-bound laws use: every tile of those traces has at most FOLD MMAs from itself to its run's fold
# (tr_bound_m16g / tr_bound_tail) and is at least one MMA (tr_pos).
import Base
import ./precision_elpis.bend as E
import ./precision_stock.bend as S
import ./m16_diet.bend as Diet
import ./m16_diet_spec.bend as DSpec
import ./err_gemm_runs.bend as R

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

# For every slice start x, length and tiles_k >= 1, the fp16 runs of the stock main loop (fold only at a
# column end or the slice end) are exactly the maximal pieces of the slice's consecutive k-tiles that lie
# in one output column.
law stock_runs_are_column_pieces:
  for +iters: Nat
  for +x: Nat
  for +tk: Nat
  for tpos: {Nat.is_lt(0n, tk) == True{} : Bool}
  {S.runs(S.loop(iters, Nat.mod(x, tk), Nat.div(x, tk), tk), 0n) == S.col_runs(iters, x, tk, 0n) : List<&2, Nat>}

# Every tile of the served m16g trace of any block slice has at most FOLD MMAs from itself to its run's
# fold (tr <= FO, the err_gemm leaf bound).
law tr_bound_m16g:
  for +s: Nat
  for +n: Nat
  for +KT: Nat
  for +i: Nat
  for tiles: {Nat.is_lt(0n, KT) == True{} : Bool}
  {Nat.is_le(R.tr_at(Diet.diet_m16g(s, n, KT, E.pf(), E.xr(), E.fold(), E.ws(), E.xi()), i), E.fold()) == True{} : Bool}

# The same for the served 8202 tail trace (all three phases).
law tr_bound_tail:
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
  for kt0: {Nat.is_lt(0n, k0) == True{} : Bool}
  for kt1: {Nat.is_lt(0n, k1) == True{} : Bool}
  for kt2: {Nat.is_lt(0n, k2) == True{} : Bool}
  for ring1: {Nat.is_lt(r1, E.pf()) == True{} : Bool}
  for ring2: {Nat.is_lt(r2, E.pf()) == True{} : Bool}
  {Nat.is_le(R.tr_at(Diet.diet_tail(DSpec.Ph{s0, n0, k0}, DSpec.Ph{s1, n1, k1}, DSpec.Ph{s2, n2, k2}, r1, r2, E.pf(),
    E.xr(), E.fold(), E.ws(), E.xi()), i), E.fold()) == True{} : Bool}

# A tile event has at least its own MMA.
law tr_pos:
  for +evs: List<&2, DSpec.Ev>
  for +i: Nat
  for it: {R.it_at(evs, i) == True{} : Bool}
  {Nat.is_le(1n, R.tr_at(evs, i)) == True{} : Bool}
