# Proofs of bend/err_gemm_runs_laws.bend. The fold-run and column-piece proofs are those of
# bend/precision_proof.bend (sections (ii) and (iii), copied unchanged; the same aliases), all symbolic
# in the slice: none normalizes a closed unary product, so they pass the BendTT kernel; precision_proof
# itself fails --verdict only on its closed served-table evaluations (gu_acc), which are not ported.
# No @unsafe definitions, axioms, holes or foreign code; every def precedes its uses.
import Base
import ./precision_elpis.bend as E
import ./precision_stock.bend as S
import ./err_gemm_runs.bend as R
import ./err_gemm_runs_laws.bend as Laws
import ./m16_diet.bend as Diet
import ./m16_diet_spec.bend as DSpec
import ./m16_diet_laws.bend as DL
import ./m16_diet_proof.bend as DP
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./gemm_m16_partition_laws.bend as PL
import ./gemm_m16_partition_proof.bend as PP
import ./exl3_round_proof.bend as RP
import ./nat_order_laws.bend as NO
import ./nat_order_proof.bend as NOP

# ==== (ii) the elpis m16 fold schedule (precision_proof.bend) ====

# -- skeleton-level run check: a Tile{g, it} of a phase starting at s is one k16 tile whose fold flag is
#    DSpec.rfold(it - s, fo) (m16_diet_spec.bend rwalk); a Flush closes the run (fold() + flush).
def sk_ok(evs: List<&2, PSpec.Ev>, +s: Nat, +fo: Nat, +open: Nat, +L: Nat) -> Bool:
  match evs:
    case Nil{}:
      Nat.is_le(open, L)
    case ev <> rest:
      match ev:
        case PSpec.Tile{g, it}:
          Bool.and(Nat.is_le(1n+open, L), sk_ok(rest, s, fo, E.rsel(DSpec.rfold(Nat.sub(it, s), fo), 0n, 1n+open), L))
        case PSpec.Flush{g}:
          Bool.and(Nat.is_le(open, L), sk_ok(rest, s, fo, 0n, L))

def sk_closed(evs: List<&2, PSpec.Ev>, +s: Nat, +fo: Nat, +open: Nat) -> Nat:
  match evs:
    case Nil{}:
      open
    case ev <> rest:
      match ev:
        case PSpec.Tile{g, it}:
          sk_closed(rest, s, fo, E.rsel(DSpec.rfold(Nat.sub(it, s), fo), 0n, 1n+open))
        case PSpec.Flush{g}:
          sk_closed(rest, s, fo, 0n)

def res_cons(+ev: DSpec.Ev, r: DSpec.Res) -> {DSpec.res_evs(DSpec.cons(ev, r)) == ev <> DSpec.res_evs(r) : List<&2, DSpec.Ev>}:
  match r:
    case DSpec.Res{e, o}:
      {==}

# rwalk's events have the skeleton's runs, whatever the bookkeeping state.
def walk_ok(+evs: List<&2, PSpec.Ev>, +s: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: DSpec.Ctx,
    +cs: Nat, +qs: Nat, +rim: DSpec.RIM, +open: Nat, +L: Nat)
  -> {E.runs_ok(DSpec.res_evs(DSpec.rwalk(evs, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)), open, L) == sk_ok(evs, s, fo, open, L) : Bool}:
  match evs:
    case Nil{}:
      {==}
    case ev <> rest:
      match ev:
        case PSpec.Tile{+g, +it}:
          +j = Nat.sub(it, s)
          +IT = {DSpec.It{DSpec.rchunk(j, xr), DSpec.r_we(qs, ws, ctx, rim), Nat.mul(cs, ws), Nat.mul(DSpec.rpiece(j, xr), xi), DSpec.rfold(j, fo)} : DSpec.Ev}
          +R = DSpec.rwalk(rest, s, pf, xr, fo, ws, xi, ctx, DSpec.nxt(cs, pf), DSpec.nxt(qs, pf), DSpec.r_next(ctx, rim))
          +o1 = E.rsel(DSpec.rfold(j, fo), 0n, 1n+open)
          %Equal.sym(List<&2, DSpec.Ev>, DSpec.res_evs(DSpec.cons(IT, R)), IT <> DSpec.res_evs(R), res_cons(IT, R)) :
            {E.runs_ok(_, open, L) == sk_ok(PSpec.Tile{g, it} <> rest, s, fo, open, L) : Bool}
          %Equal.sym(Bool, E.runs_ok(DSpec.res_evs(R), o1, L), sk_ok(rest, s, fo, o1, L),
              walk_ok(rest, s, pf, xr, fo, ws, xi, ctx, DSpec.nxt(cs, pf), DSpec.nxt(qs, pf), DSpec.r_next(ctx, rim), o1, L)) :
            {Bool.and(Nat.is_le(1n+open, L), _) == sk_ok(PSpec.Tile{g, it} <> rest, s, fo, open, L) : Bool}
          {==}
        case PSpec.Flush{+g}:
          +R = DSpec.rwalk(rest, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)
          %Equal.sym(List<&2, DSpec.Ev>, DSpec.res_evs(DSpec.cons(DSpec.Seg{g}, R)), DSpec.Seg{g} <> DSpec.res_evs(R), res_cons(DSpec.Seg{g}, R)) :
            {E.runs_ok(_, open, L) == sk_ok(PSpec.Flush{g} <> rest, s, fo, open, L) : Bool}
          %Equal.sym(Bool, E.runs_ok(DSpec.res_evs(R), 0n, L), sk_ok(rest, s, fo, 0n, L),
              walk_ok(rest, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim, 0n, L)) :
            {Bool.and(Nat.is_le(open, L), _) == sk_ok(PSpec.Flush{g} <> rest, s, fo, open, L) : Bool}
          {==}

def walk_closed(+evs: List<&2, PSpec.Ev>, +s: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: DSpec.Ctx,
    +cs: Nat, +qs: Nat, +rim: DSpec.RIM, +open: Nat)
  -> {E.closed(DSpec.res_evs(DSpec.rwalk(evs, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)), open) == sk_closed(evs, s, fo, open) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case ev <> rest:
      match ev:
        case PSpec.Tile{+g, +it}:
          +j = Nat.sub(it, s)
          +IT = {DSpec.It{DSpec.rchunk(j, xr), DSpec.r_we(qs, ws, ctx, rim), Nat.mul(cs, ws), Nat.mul(DSpec.rpiece(j, xr), xi), DSpec.rfold(j, fo)} : DSpec.Ev}
          +R = DSpec.rwalk(rest, s, pf, xr, fo, ws, xi, ctx, DSpec.nxt(cs, pf), DSpec.nxt(qs, pf), DSpec.r_next(ctx, rim))
          +o1 = E.rsel(DSpec.rfold(j, fo), 0n, 1n+open)
          %Equal.sym(List<&2, DSpec.Ev>, DSpec.res_evs(DSpec.cons(IT, R)), IT <> DSpec.res_evs(R), res_cons(IT, R)) :
            {E.closed(_, open) == sk_closed(PSpec.Tile{g, it} <> rest, s, fo, open) : Nat}
          walk_closed(rest, s, pf, xr, fo, ws, xi, ctx, DSpec.nxt(cs, pf), DSpec.nxt(qs, pf), DSpec.r_next(ctx, rim), o1)
        case PSpec.Flush{+g}:
          +R = DSpec.rwalk(rest, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)
          %Equal.sym(List<&2, DSpec.Ev>, DSpec.res_evs(DSpec.cons(DSpec.Seg{g}, R)), DSpec.Seg{g} <> DSpec.res_evs(R), res_cons(DSpec.Seg{g}, R)) :
            {E.closed(_, open) == sk_closed(PSpec.Flush{g} <> rest, s, fo, open) : Nat}
          walk_closed(rest, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim, 0n)

# -- arithmetic of the fold cadence (fo = 1 + bp) --

def f_sub_succ(+a: Nat, +b: Nat, h: {Nat.is_le(b, a) == True{} : Bool})
  -> {Nat.sub(1n+a, b) == 1n+Nat.sub(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.sub(1n, 1n+q) == 1n+Nat.sub(0n, 1n+q) : Nat}, PP.ar_false_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      f_sub_succ(p, q, h)

def f_le_succ(+a: Nat) -> {Nat.is_le(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      f_le_succ(p)

# c <= bp and c != bp give c + 1 <= bp.
def f_le_ne(+c: Nat, +bp: Nat, le: {Nat.is_le(c, bp) == True{} : Bool}, ne: {Nat.is_eq(c, bp) == False{} : Bool})
  -> {Nat.is_le(1n+c, bp) == True{} : Bool}:
  match c bp:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, PP.ar_true_false(ne))
    case 0n 1n+q:
      PP.ar_h_le_zero(q)
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, PP.ar_false_true(le))
    case 1n+p 1n+q:
      f_le_ne(p, q, le, ne)

# (1 + bp) - 1 = bp - 0 = bp: the fold test against FOLD - 1.
def f_ne_fix(+c: Nat, +bp: Nat, h: {Nat.is_eq(c, Nat.sub(bp, 0n)) == False{} : Bool})
  -> {Nat.is_eq(c, bp) == False{} : Bool}:
  %PP.ar_sub_zero_r(bp) : {Nat.is_eq(c, _) == False{} : Bool}
  h

# open <= (it - s) mod (1 + bp) and a non-folding tile it: open + 1 <= (it + 1 - s) mod (1 + bp).
def f_next(+it: Nat, +s: Nat, +bp: Nat, +open: Nat, hs: {Nat.is_le(s, it) == True{} : Bool},
    ho: {Nat.is_le(open, Nat.mod(Nat.sub(it, s), 1n+bp)) == True{} : Bool},
    hf: {DSpec.rfold(Nat.sub(it, s), 1n+bp) == False{} : Bool})
  -> {Nat.is_le(1n+open, Nat.mod(Nat.sub(1n+it, s), 1n+bp)) == True{} : Bool}:
  +j = Nat.sub(it, s)
  +c = Nat.mod(j, 1n+bp)
  +le1 = f_le_ne(c, bp, RP.mod_le(j, bp), f_ne_fix(c, bp, hf))
  %Equal.sym(Nat, Nat.sub(1n+it, s), 1n+j, f_sub_succ(it, s, hs)) : {Nat.is_le(1n+open, Nat.mod(_, 1n+bp)) == True{} : Bool}
  %Equal.sym(Nat, Nat.mod(1n+j, 1n+bp), RP.wrap(1n+c, bp), RP.mod_succ(j, bp)) : {Nat.is_le(1n+open, _) == True{} : Bool}
  %Equal.sym(Nat, RP.wrap(1n+c, bp), 1n+c, RP.wrap_id(c, bp, le1)) : {Nat.is_le(1n+open, _) == True{} : Bool}
  ho

# open <= (it - s) mod (1 + bp) gives open <= 1 + bp and 1 + open <= 1 + bp.
def f_open_le(+j: Nat, +bp: Nat, +open: Nat, ho: {Nat.is_le(open, Nat.mod(j, 1n+bp)) == True{} : Bool})
  -> {Nat.is_le(open, bp) == True{} : Bool}:
  PP.ar_le_trans(open, Nat.mod(j, 1n+bp), bp, ho, RP.mod_le(j, bp))

# -- one tile, then the flush decision --

def flush_ok(flag: Bool, +g: Nat, +T2: List<&2, PSpec.Ev>, +s: Nat, +fo: Nat, +o: Nat, +L: Nat,
    hle: {Nat.is_le(o, L) == True{} : Bool}, ko: {sk_ok(T2, s, fo, o, L) == True{} : Bool},
    kz: {sk_ok(T2, s, fo, 0n, L) == True{} : Bool})
  -> {sk_ok(PSpec.trace.flush(flag, g, T2), s, fo, o, L) == True{} : Bool}:
  match flag:
    case True{}:
      PP.ar_and_intro(Nat.is_le(o, L), sk_ok(T2, s, fo, 0n, L), hle, kz)
    case False{}:
      ko

def tile_ok(fold: Bool, +X: List<&2, PSpec.Ev>, +s: Nat, +fo: Nat, +open: Nat, +L: Nat,
    hle: {Nat.is_le(1n+open, L) == True{} : Bool}, k0: {sk_ok(X, s, fo, 0n, L) == True{} : Bool},
    k1: {fold == False{} : Bool} -> {sk_ok(X, s, fo, 1n+open, L) == True{} : Bool})
  -> {Bool.and(Nat.is_le(1n+open, L), sk_ok(X, s, fo, E.rsel(fold, 0n, 1n+open), L)) == True{} : Bool}:
  match fold:
    case True{}:
      PP.ar_and_intro(Nat.is_le(1n+open, L), sk_ok(X, s, fo, 0n, L), hle, k0)
    case False{}:
      PP.ar_and_intro(Nat.is_le(1n+open, L), sk_ok(X, s, fo, 1n+open, L), hle, k1({==}))

# Every run of the v2 trace from tile it (phase start s <= it, open run below (it - s) mod FOLD) is at
# most FOLD = 1 + bp tiles.
def trace_ok(+left: Nat, +it: Nat, +e: Nat, +KT: Nat, +s: Nat, +bp: Nat, +open: Nat,
    hs: {Nat.is_le(s, it) == True{} : Bool},
    ho: {Nat.is_le(open, Nat.mod(Nat.sub(it, s), 1n+bp)) == True{} : Bool})
  -> {sk_ok(PSpec.trace(left, it, e, KT), s, 1n+bp, open, 1n+bp) == True{} : Bool}:
  match left:
    case 0n:
      PP.ar_le_trans(open, bp, 1n+bp, f_open_le(Nat.sub(it, s), bp, open, ho), f_le_succ(bp))
    case 1n+r:
      +hs2 = hs
      +ho2 = ho
      +hs1 = PP.ar_le_trans(s, it, 1n+it, hs2, f_le_succ(it))
      +T2 = PSpec.trace(r, 1n+it, e, KT)
      +flag = Bool.or(Nat.is_eq(1n+it, e), Nat.is_eq(Nat.mod(1n+it, KT), 0n))
      +g = Nat.div(it, KT)
      +le_o = f_open_le(Nat.sub(it, s), bp, open, ho2)
      +kz = trace_ok(r, 1n+it, e, KT, s, bp, 0n, hs1, PP.ar_h_le_zero(Nat.mod(Nat.sub(1n+it, s), 1n+bp)))
      +x0 = flush_ok(flag, g, T2, s, 1n+bp, 0n, 1n+bp, PP.ar_h_le_zero(1n+bp), kz, kz)
      tile_ok(DSpec.rfold(Nat.sub(it, s), 1n+bp), PSpec.trace.flush(flag, g, T2), s, 1n+bp, open, 1n+bp, le_o, x0,
        hf => flush_ok(flag, g, T2, s, 1n+bp, 1n+open, 1n+bp, le_o,
          trace_ok(r, 1n+it, e, KT, s, bp, 1n+open, hs1, f_next(it, s, bp, open, hs2, ho2, hf)), kz))

# The trace from tile it with e = it + left, left >= 1, ends with a flush: the run is closed.
def flush_closed(flag: Bool, +g: Nat, +T2: List<&2, PSpec.Ev>, +s: Nat, +fo: Nat, +o: Nat,
    k: {sk_closed(T2, s, fo, E.rsel(flag, 0n, o)) == 0n : Nat})
  -> {sk_closed(PSpec.trace.flush(flag, g, T2), s, fo, o) == 0n : Nat}:
  match flag:
    case True{}:
      k
    case False{}:
      k

def trace_closed(+r: Nat, +it: Nat, +e: Nat, +KT: Nat, +s: Nat, +fo: Nat, +open: Nat,
    he: {Nat.add(1n+r, it) == e : Nat})
  -> {sk_closed(PSpec.trace(1n+r, it, e, KT), s, fo, open) == 0n : Nat}:
  match r:
    case 0n:
      +o1 = E.rsel(DSpec.rfold(Nat.sub(it, s), fo), 0n, 1n+open)
      %he : {sk_closed(PSpec.trace(1n, it, _, KT), s, fo, open) == 0n : Nat}
      %Equal.sym(Bool, Nat.is_eq(it, it), True{}, PP.ar_eq_refl(it)) :
        {sk_closed(PSpec.trace.flush(Bool.or(_, Nat.is_eq(Nat.mod(1n+it, KT), 0n)), Nat.div(it, KT), Nil{}), s, fo, o1) == 0n : Nat}
      {==}
    case 1n+q:
      +o1 = E.rsel(DSpec.rfold(Nat.sub(it, s), fo), 0n, 1n+open)
      +flag = Bool.or(Nat.is_eq(1n+it, e), Nat.is_eq(Nat.mod(1n+it, KT), 0n))
      +he2 = Equal.trans(Nat, Nat.add(1n+q, 1n+it), 1n+Nat.add(1n+q, it), e, PP.ar_add_succ_r(1n+q, it), he)
      flush_closed(flag, Nat.div(it, KT), PSpec.trace(1n+q, 1n+it, e, KT), s, fo, o1,
        trace_closed(q, 1n+it, e, KT, s, fo, E.rsel(flag, 0n, o1), he2))

# -- composition --

# Appending: B is checked from the run A leaves open.
def app_ok(+A: List<&2, DSpec.Ev>, +B: List<&2, DSpec.Ev>, +o: Nat, +L: Nat,
    ha: {E.runs_ok(A, o, L) == True{} : Bool}, hb: {E.runs_ok(B, E.closed(A, o), L) == True{} : Bool})
  -> {E.runs_ok(List.append(&2, DSpec.Ev, A, B), o, L) == True{} : Bool}:
  match A:
    case Nil{}:
      hb
    case ev <> rest:
      match ev:
        case DSpec.It{x, w, r, xo, +fold}:
          +hh = ha
          +o1 = E.rsel(fold, 0n, 1n+o)
          PP.ar_and_intro(Nat.is_le(1n+o, L), E.runs_ok(List.append(&2, DSpec.Ev, rest, B), o1, L),
            PP.ar_and_l(Nat.is_le(1n+o, L), E.runs_ok(rest, o1, L), hh),
            app_ok(rest, B, o1, L, PP.ar_and_r(Nat.is_le(1n+o, L), E.runs_ok(rest, o1, L), hh), hb))
        case DSpec.Seg{g}:
          +hh = ha
          PP.ar_and_intro(Nat.is_le(o, L), E.runs_ok(List.append(&2, DSpec.Ev, rest, B), 0n, L),
            PP.ar_and_l(Nat.is_le(o, L), E.runs_ok(rest, 0n, L), hh),
            app_ok(rest, B, 0n, L, PP.ar_and_r(Nat.is_le(o, L), E.runs_ok(rest, 0n, L), hh), hb))
        case DSpec.Pro{w}:
          app_ok(rest, B, o, L, ha, hb)
        case DSpec.Exit{st}:
          app_ok(rest, B, o, L, ha, hb)

def app0(+A: List<&2, DSpec.Ev>, +B: List<&2, DSpec.Ev>, +L: Nat,
    ha: {E.runs_ok(A, 0n, L) == True{} : Bool}, hc: {E.closed(A, 0n) == 0n : Nat},
    hb: {E.runs_ok(B, 0n, L) == True{} : Bool})
  -> {E.runs_ok(List.append(&2, DSpec.Ev, A, B), 0n, L) == True{} : Bool}:
  app_ok(A, B, 0n, L, ha, Equal.trans(Bool, E.runs_ok(B, E.closed(A, 0n), L), E.runs_ok(B, 0n, L), True{},
    Equal.cong(Nat, Bool, x => E.runs_ok(B, x, L), E.closed(A, 0n), 0n, hc), hb))

# The prologue moves no accumulator.
def pro_ok(t: Nat, +d: Nat, +ws: Nat, +ctx: DSpec.Ctx, +rim: DSpec.RIM, +o: Nat, +L: Nat,
    h: {Nat.is_le(o, L) == True{} : Bool})
  -> {E.runs_ok(DSpec.pro(t, d, ws, ctx, rim), o, L) == True{} : Bool}:
  match t:
    case 0n:
      h
    case 1n+u:
      pro_ok(u, 1n+d, ws, ctx, DSpec.r_next(ctx, rim), o, L, h)

def pro_closed(t: Nat, +d: Nat, +ws: Nat, +ctx: DSpec.Ctx, +rim: DSpec.RIM, +o: Nat)
  -> {E.closed(DSpec.pro(t, d, ws, ctx, rim), o) == o : Nat}:
  match t:
    case 0n:
      {==}
    case 1n+u:
      pro_closed(u, 1n+d, ws, ctx, DSpec.r_next(ctx, rim), o)

def out_runs(o: DSpec.Out, +L: Nat) -> {E.runs_ok(DSpec.out_evs(o), 0n, L) == True{} : Bool}:
  match o:
    case DSpec.Cont{st}:
      PP.ar_h_le_zero(L)
    case DSpec.End{}:
      PP.ar_h_le_zero(L)

def out_closed(o: DSpec.Out) -> {E.closed(DSpec.out_evs(o), 0n) == 0n : Nat}:
  match o:
    case DSpec.Cont{st}:
      {==}
    case DSpec.End{}:
      {==}

# -- one phase: v2's loop over [s, s + n), any bookkeeping state --

def tr_closed0(+n: Nat, +s: Nat, +kt: Nat, +fo: Nat)
  -> {sk_closed(PSpec.trace(n, s, Nat.add(s, n), kt), s, fo, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+r:
      trace_closed(r, s, Nat.add(s, 1n+r), kt, s, fo, 0n, PP.ar_add_comm(1n+r, s))

def walk_trace_ok(+s: Nat, +n: Nat, +kt: Nat, +pf: Nat, +xr: Nat, +bp: Nat, +ws: Nat, +xi: Nat, +ctx: DSpec.Ctx,
    +cs: Nat, +qs: Nat, +rim: DSpec.RIM, kpos: {Nat.is_lt(0n, kt) == True{} : Bool})
  -> {E.runs_ok(DSpec.res_evs(DSpec.rwalk(Part.mainloop(s, Nat.add(s, n), kt), s, pf, xr, 1n+bp, ws, xi, ctx, cs, qs, rim)), 0n, 1n+bp) == True{} : Bool}:
  +ML = Part.mainloop(s, Nat.add(s, n), kt)
  +TR = PSpec.trace(Nat.sub(Nat.add(s, n), s), s, Nat.add(s, n), kt)
  %Equal.sym(Bool, E.runs_ok(DSpec.res_evs(DSpec.rwalk(ML, s, pf, xr, 1n+bp, ws, xi, ctx, cs, qs, rim)), 0n, 1n+bp),
      sk_ok(ML, s, 1n+bp, 0n, 1n+bp), walk_ok(ML, s, pf, xr, 1n+bp, ws, xi, ctx, cs, qs, rim, 0n, 1n+bp)) :
    {_ == True{} : Bool}
  %Equal.sym(List<&2, PSpec.Ev>, ML, TR, PL.mainloop_trace(s, Nat.add(s, n), kt, PP.ar_le_add_r(s, n), kpos)) :
    {sk_ok(_, s, 1n+bp, 0n, 1n+bp) == True{} : Bool}
  trace_ok(Nat.sub(Nat.add(s, n), s), s, Nat.add(s, n), kt, s, bp, 0n, PP.ar_le_refl(s),
    PP.ar_h_le_zero(Nat.mod(Nat.sub(s, s), 1n+bp)))

def walk_trace_closed(+s: Nat, +n: Nat, +kt: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: DSpec.Ctx,
    +cs: Nat, +qs: Nat, +rim: DSpec.RIM, kpos: {Nat.is_lt(0n, kt) == True{} : Bool})
  -> {E.closed(DSpec.res_evs(DSpec.rwalk(Part.mainloop(s, Nat.add(s, n), kt), s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)), 0n) == 0n : Nat}:
  +ML = Part.mainloop(s, Nat.add(s, n), kt)
  +TR = PSpec.trace(Nat.sub(Nat.add(s, n), s), s, Nat.add(s, n), kt)
  %Equal.sym(Nat, E.closed(DSpec.res_evs(DSpec.rwalk(ML, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim)), 0n),
      sk_closed(ML, s, fo, 0n), walk_closed(ML, s, pf, xr, fo, ws, xi, ctx, cs, qs, rim, 0n)) :
    {_ == 0n : Nat}
  %Equal.sym(List<&2, PSpec.Ev>, ML, TR, PL.mainloop_trace(s, Nat.add(s, n), kt, PP.ar_le_add_r(s, n), kpos)) :
    {sk_closed(_, s, fo, 0n) == 0n : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.add(s, n), s), n, PP.ar_add_sub(s, n)) :
    {sk_closed(PSpec.trace(_, s, Nat.add(s, n), kt), s, fo, 0n) == 0n : Nat}
  tr_closed0(n, s, kt, fo)

def ph_runs(+s: Nat, +n: Nat, +kt: Nat, +pf: Nat, +xr: Nat, +bp: Nat, +ws: Nat, +xi: Nat, +ctx: DSpec.Ctx,
    st: DSpec.St, kpos: {Nat.is_lt(0n, kt) == True{} : Bool})
  -> {E.runs_ok(DSpec.res_evs(DSpec.ref_phase(DSpec.Ph{s, n, kt}, pf, xr, 1n+bp, ws, xi, ctx, st)), 0n, 1n+bp) == True{} : Bool}:
  match st:
    case DSpec.St{cs, qs, ij, rem, run, k}:
      walk_trace_ok(s, n, kt, pf, xr, bp, ws, xi, ctx, cs, qs, DSpec.RT{ij, rem, run, k}, kpos)

def ph_closed(+s: Nat, +n: Nat, +kt: Nat, +pf: Nat, +xr: Nat, +fo: Nat, +ws: Nat, +xi: Nat, +ctx: DSpec.Ctx,
    st: DSpec.St, kpos: {Nat.is_lt(0n, kt) == True{} : Bool})
  -> {E.closed(DSpec.res_evs(DSpec.ref_phase(DSpec.Ph{s, n, kt}, pf, xr, fo, ws, xi, ctx, st)), 0n) == 0n : Nat}:
  match st:
    case DSpec.St{cs, qs, ij, rem, run, k}:
      walk_trace_closed(s, n, kt, pf, xr, fo, ws, xi, ctx, cs, qs, DSpec.RT{ij, rem, run, k}, kpos)

# -- the kernel compositions --

def resall_ok(r: DSpec.Res, +L: Nat, h: {E.runs_ok(DSpec.res_evs(r), 0n, L) == True{} : Bool},
    hc: {E.closed(DSpec.res_evs(r), 0n) == 0n : Nat})
  -> {E.runs_ok(DSpec.res_all(r), 0n, L) == True{} : Bool}:
  match r:
    case DSpec.Res{+e, +o}:
      app0(e, DSpec.out_evs(o), L, h, hc, out_runs(o, L))

def then_ok(r: DSpec.Res, +s: Nat, +n: Nat, +kt: Nat, +cr: Nat, +pf: Nat, +xr: Nat, +bp: Nat, +ws: Nat, +xi: Nat,
    +ctx: DSpec.Ctx, h: {E.runs_ok(DSpec.res_evs(r), 0n, 1n+bp) == True{} : Bool},
    hc: {E.closed(DSpec.res_evs(r), 0n) == 0n : Nat}, +kpos: {Nat.is_lt(0n, kt) == True{} : Bool})
  -> {E.runs_ok(DSpec.ref_then(r, DSpec.Ph{s, n, kt}, cr, pf, xr, 1n+bp, ws, xi, ctx), 0n, 1n+bp) == True{} : Bool}:
  match r:
    case DSpec.Res{+e, +o}:
      +st = DSpec.set_cs(cr, DSpec.out_st(o))
      +P = DSpec.ref_phase(DSpec.Ph{s, n, kt}, pf, xr, 1n+bp, ws, xi, ctx, st)
      app0(e, List.append(&2, DSpec.Ev, DSpec.out_evs(o), DSpec.res_all(P)), 1n+bp, h, hc,
        app0(DSpec.out_evs(o), DSpec.res_all(P), 1n+bp, out_runs(o, 1n+bp), out_closed(o),
          resall_ok(P, 1n+bp, ph_runs(s, n, kt, pf, xr, bp, ws, xi, ctx, st, kpos),
            ph_closed(s, n, kt, pf, xr, 1n+bp, ws, xi, ctx, st, kpos))))

def then2_ok(r: DSpec.Res, +s1: Nat, +n1: Nat, +k1: Nat, +c1: Nat, +s2: Nat, +n2: Nat, +k2: Nat, +c2: Nat,
    +pf: Nat, +xr: Nat, +bp: Nat, +ws: Nat, +xi: Nat, +ctx: DSpec.Ctx,
    h: {E.runs_ok(DSpec.res_evs(r), 0n, 1n+bp) == True{} : Bool}, hc: {E.closed(DSpec.res_evs(r), 0n) == 0n : Nat},
    +kp1: {Nat.is_lt(0n, k1) == True{} : Bool}, +kp2: {Nat.is_lt(0n, k2) == True{} : Bool})
  -> {E.runs_ok(DSpec.ref_then2(r, DSpec.Ph{s1, n1, k1}, c1, DSpec.Ph{s2, n2, k2}, c2, pf, xr, 1n+bp, ws, xi, ctx), 0n, 1n+bp) == True{} : Bool}:
  match r:
    case DSpec.Res{+e, +o}:
      +st = DSpec.set_cs(c1, DSpec.out_st(o))
      +P = DSpec.ref_phase(DSpec.Ph{s1, n1, k1}, pf, xr, 1n+bp, ws, xi, ctx, st)
      +T = DSpec.ref_then(P, DSpec.Ph{s2, n2, k2}, c2, pf, xr, 1n+bp, ws, xi, ctx)
      app0(e, List.append(&2, DSpec.Ev, DSpec.out_evs(o), T), 1n+bp, h, hc,
        app0(DSpec.out_evs(o), T, 1n+bp, out_runs(o, 1n+bp), out_closed(o),
          then_ok(P, s2, n2, k2, c2, pf, xr, bp, ws, xi, ctx, ph_runs(s1, n1, k1, pf, xr, bp, ws, xi, ctx, st, kp1),
            ph_closed(s1, n1, k1, pf, xr, 1n+bp, ws, xi, ctx, st, kp1), kp2)))

def Laws.fold_runs_m16g(s, n, KT, tiles):
  +kp = tiles
  +pf = E.pf()
  +ws = E.ws()
  +ctx = {DSpec.GCtx{KT, n} : DSpec.Ctx}
  +PRO = DSpec.pro(Nat.sub(pf, 1n), 0n, ws, ctx, DSpec.g_init(s, KT))
  +W = DSpec.res_evs(DSpec.rwalk(Part.mainloop(s, Nat.add(s, n), KT), s, pf, E.xr(), E.fold(), ws, E.xi(), ctx, 0n,
    Nat.sub(pf, 1n), DSpec.pro_state(Nat.sub(pf, 1n), ctx, DSpec.g_init(s, KT))))
  %Equal.sym(List<&2, DSpec.Ev>, Diet.diet_m16g(s, n, KT, pf, E.xr(), E.fold(), ws, E.xi()),
      DSpec.ref_m16g(s, n, KT, pf, E.xr(), E.fold(), ws, E.xi()),
      DL.diet_m16g(s, n, KT, pf, E.xr(), E.fold(), ws, E.xi(), kp, {==}, {==}, {==}, {==}, {==}, {==})) :
    {E.runs_ok(_, 0n, E.fold()) == True{} : Bool}
  app0(PRO, W, 2n, pro_ok(Nat.sub(pf, 1n), 0n, ws, ctx, DSpec.g_init(s, KT), 0n, 2n, {==}),
    pro_closed(Nat.sub(pf, 1n), 0n, ws, ctx, DSpec.g_init(s, KT), 0n),
    walk_trace_ok(s, n, KT, pf, E.xr(), 1n, ws, E.xi(), ctx, 0n, Nat.sub(pf, 1n),
      DSpec.pro_state(Nat.sub(pf, 1n), ctx, DSpec.g_init(s, KT)), kp))

def Laws.fold_runs_tail(s0, n0, k0, s1, n1, k1, s2, n2, k2, r1, r2, kt0, kt1, kt2, ring1, ring2):
  +pf = E.pf()
  +ws = E.ws()
  +p0 = {DSpec.Ph{s0, n0, k0} : DSpec.Ph}
  +p1 = {DSpec.Ph{s1, n1, k1} : DSpec.Ph}
  +p2 = {DSpec.Ph{s2, n2, k2} : DSpec.Ph}
  +ctx = DSpec.t_ctx({[p0, p1, p2] : List<&2, DSpec.Ph>})
  +init = DSpec.t_init({[p0, p1, p2] : List<&2, DSpec.Ph>})
  +st0 = DSpec.st_of(0n, Nat.sub(pf, 1n), DSpec.pro_state(Nat.sub(pf, 1n), ctx, init))
  +P0 = DSpec.ref_phase(p0, pf, E.xr(), E.fold(), ws, E.xi(), ctx, st0)
  +k0p = kt0
  +k1p = kt1
  +k2p = kt2
  %Equal.sym(List<&2, DSpec.Ev>, Diet.diet_tail(p0, p1, p2, r1, r2, pf, E.xr(), E.fold(), ws, E.xi()),
      DSpec.ref_tail(p0, p1, p2, r1, r2, pf, E.xr(), E.fold(), ws, E.xi()),
      DL.diet_tail(s0, n0, k0, s1, n1, k1, s2, n2, k2, r1, r2, pf, E.xr(), E.fold(), ws, E.xi(), k0p, k1p, k2p,
        {==}, {==}, {==}, {==}, {==}, {==}, ring1, ring2)) :
    {E.runs_ok(_, 0n, E.fold()) == True{} : Bool}
  app0(DSpec.pro(Nat.sub(pf, 1n), 0n, ws, ctx, init),
    DSpec.ref_then2(P0, p1, r1, p2, r2, pf, E.xr(), E.fold(), ws, E.xi(), ctx), 2n,
    pro_ok(Nat.sub(pf, 1n), 0n, ws, ctx, init, 0n, 2n, {==}), pro_closed(Nat.sub(pf, 1n), 0n, ws, ctx, init, 0n),
    then2_ok(P0, s1, n1, k1, r1, s2, n2, k2, r2, pf, E.xr(), 1n, ws, E.xi(), ctx,
      ph_runs(s0, n0, k0, pf, E.xr(), 1n, ws, E.xi(), ctx, st0, k0p),
      ph_closed(s0, n0, k0, pf, E.xr(), E.fold(), ws, E.xi(), ctx, st0, k0p), k1p, k2p))

# ==== (iii) stock runs are column pieces ====

def c_or_true_r(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def c_sel_pick(b: Bool, +x: Nat) -> {S.sel(b, 0n, x) == RP.pick0(b, x) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# c <= tp gives tp <= c == (c == tp).
def c_le_eq(+c: Nat, +tp: Nat, h: {Nat.is_le(c, tp) == True{} : Bool})
  -> {Nat.is_le(tp, c) == Nat.is_eq(c, tp) : Bool}:
  match c tp:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(0n, 1n+p) == Nat.is_eq(1n+p, 0n) : Bool}, PP.ar_false_true(h))
    case 1n+p 1n+q:
      c_le_eq(p, q, h)

# The loop's next k index: (k + 1 == tiles_k ? 0 : k + 1) with k = x % tk is (x + 1) % tk.
def c_next_k(+x: Nat, +tp: Nat)
  -> {S.sel(Nat.is_le(tp, Nat.mod(x, 1n+tp)), 0n, 1n+Nat.mod(x, 1n+tp)) == Nat.mod(1n+x, 1n+tp) : Nat}:
  +c = Nat.mod(x, 1n+tp)
  %Equal.sym(Bool, Nat.is_le(tp, c), Nat.is_eq(c, tp), c_le_eq(c, tp, RP.mod_le(x, tp))) :
    {S.sel(_, 0n, 1n+c) == Nat.mod(1n+x, 1n+tp) : Nat}
  %Equal.sym(Nat, S.sel(Nat.is_eq(c, tp), 0n, 1n+c), RP.pick0(Nat.is_eq(c, tp), 1n+c), c_sel_pick(Nat.is_eq(c, tp), 1n+c)) :
    {_ == Nat.mod(1n+x, 1n+tp) : Nat}
  Equal.sym(Nat, Nat.mod(1n+x, 1n+tp), RP.wrap(1n+c, tp), RP.mod_succ(x, tp))

# The column-end test of the next tile: (x + 1) % tk == 0 iff x % tk == tk - 1.
def c_pick_zero(a: Bool, +y: Nat) -> {Nat.is_eq(RP.pick0(a, 1n+y), 0n) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def c_colend(+x: Nat, +tp: Nat)
  -> {Nat.is_eq(Nat.mod(1n+x, 1n+tp), 0n) == Nat.is_eq(Nat.mod(x, 1n+tp), tp) : Bool}:
  +c = Nat.mod(x, 1n+tp)
  %Equal.sym(Nat, Nat.mod(1n+x, 1n+tp), RP.wrap(1n+c, tp), RP.mod_succ(x, tp)) :
    {Nat.is_eq(_, 0n) == Nat.is_eq(c, tp) : Bool}
  c_pick_zero(Nat.is_eq(c, tp), c)

def c_subz(+c: Nat, +tp: Nat) -> {Nat.is_eq(c, Nat.sub(tp, 0n)) == Nat.is_eq(c, tp) : Bool}:
  %Equal.sym(Nat, Nat.sub(tp, 0n), tp, PP.ar_sub_zero_r(tp)) : {Nat.is_eq(c, _) == Nat.is_eq(c, tp) : Bool}
  {==}

# One loop iteration with the fold flags abstracted: A1 (the loop's slice2_k == tiles_k - 1) and A2
# (the column cut) are both `a`, the next k index is (x + 1) % tk; `k` continues on tile x + 1.
def c_step(a: Bool, +r: Nat, +x: Nat, +tp: Nat, +n: Nat, +n1: Nat, +open: Nat, +k1: Nat, +A1: Bool, +A2: Bool,
    h1: {A1 == a : Bool}, h2: {A2 == a : Bool}, hk: {k1 == Nat.mod(1n+x, 1n+tp) : Nat},
    k: @o:Nat -> {Bool.or(Nat.is_lt(0n, r), Nat.is_eq(o, 0n)) == True{} : Bool} ->
      {S.runs(S.loop(r, Nat.mod(1n+x, 1n+tp), n1, 1n+tp), o) == S.col_runs(r, 1n+x, 1n+tp, o) : List<&2, Nat>})
  -> {S.runs(S.red(Bool.or(A1, Nat.is_eq(1n+r, 1n)), n, S.loop(r, k1, n1, 1n+tp)), 1n+open) ==
      S.col_runs.close(Bool.or(A2, Nat.is_eq(r, 0n)), 1n+open,
        S.col_runs(r, 1n+x, 1n+tp, S.col_runs.next(Bool.or(A2, Nat.is_eq(r, 0n)), 1n+open))) : List<&2, Nat>}:
  match a:
    case True{}:
      %Equal.sym(Bool, A1, True{}, h1) : {S.runs(S.red(Bool.or(_, Nat.is_eq(1n+r, 1n)), n, S.loop(r, k1, n1, 1n+tp)), 1n+open) ==
        S.col_runs.close(Bool.or(A2, Nat.is_eq(r, 0n)), 1n+open, S.col_runs(r, 1n+x, 1n+tp, S.col_runs.next(Bool.or(A2, Nat.is_eq(r, 0n)), 1n+open))) : List<&2, Nat>}
      %Equal.sym(Bool, A2, True{}, h2) : {S.runs(S.red(True{}, n, S.loop(r, k1, n1, 1n+tp)), 1n+open) ==
        S.col_runs.close(Bool.or(_, Nat.is_eq(r, 0n)), 1n+open, S.col_runs(r, 1n+x, 1n+tp, S.col_runs.next(Bool.or(_, Nat.is_eq(r, 0n)), 1n+open))) : List<&2, Nat>}
      %Equal.sym(Nat, k1, Nat.mod(1n+x, 1n+tp), hk) : {S.runs(S.red(True{}, n, S.loop(r, _, n1, 1n+tp)), 1n+open) ==
        S.col_runs.close(True{}, 1n+open, S.col_runs(r, 1n+x, 1n+tp, S.col_runs.next(True{}, 1n+open))) : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, t => (1n+open) <> t, S.runs(S.loop(r, Nat.mod(1n+x, 1n+tp), n1, 1n+tp), 0n),
        S.col_runs(r, 1n+x, 1n+tp, 0n), k(0n, c_or_true_r(Nat.is_lt(0n, r))))
    case False{}:
      match r:
        case 0n:
          %Equal.sym(Bool, A1, False{}, h1) : {S.runs(S.red(Bool.or(_, Nat.is_eq(1n+0n, 1n)), n, S.loop(0n, k1, n1, 1n+tp)), 1n+open) ==
            S.col_runs.close(Bool.or(A2, Nat.is_eq(0n, 0n)), 1n+open, S.col_runs(0n, 1n+x, 1n+tp, S.col_runs.next(Bool.or(A2, Nat.is_eq(0n, 0n)), 1n+open))) : List<&2, Nat>}
          %Equal.sym(Bool, A2, False{}, h2) : {S.runs(S.red(Nat.is_eq(1n+0n, 1n), n, S.loop(0n, k1, n1, 1n+tp)), 1n+open) ==
            S.col_runs.close(Bool.or(_, Nat.is_eq(0n, 0n)), 1n+open, S.col_runs(0n, 1n+x, 1n+tp, S.col_runs.next(Bool.or(_, Nat.is_eq(0n, 0n)), 1n+open))) : List<&2, Nat>}
          %Equal.sym(Nat, k1, Nat.mod(1n+x, 1n+tp), hk) : {S.runs(S.red(Nat.is_eq(1n+0n, 1n), n, S.loop(0n, _, n1, 1n+tp)), 1n+open) ==
            S.col_runs.close(Nat.is_eq(0n, 0n), 1n+open, S.col_runs(0n, 1n+x, 1n+tp, S.col_runs.next(Nat.is_eq(0n, 0n), 1n+open))) : List<&2, Nat>}
          {==}
        case 1n+q:
          %Equal.sym(Bool, A1, False{}, h1) : {S.runs(S.red(Bool.or(_, Nat.is_eq(1n+1n+q, 1n)), n, S.loop(1n+q, k1, n1, 1n+tp)), 1n+open) ==
            S.col_runs.close(Bool.or(A2, Nat.is_eq(1n+q, 0n)), 1n+open, S.col_runs(1n+q, 1n+x, 1n+tp, S.col_runs.next(Bool.or(A2, Nat.is_eq(1n+q, 0n)), 1n+open))) : List<&2, Nat>}
          %Equal.sym(Bool, A2, False{}, h2) : {S.runs(S.red(Nat.is_eq(1n+1n+q, 1n), n, S.loop(1n+q, k1, n1, 1n+tp)), 1n+open) ==
            S.col_runs.close(Bool.or(_, Nat.is_eq(1n+q, 0n)), 1n+open, S.col_runs(1n+q, 1n+x, 1n+tp, S.col_runs.next(Bool.or(_, Nat.is_eq(1n+q, 0n)), 1n+open))) : List<&2, Nat>}
          %Equal.sym(Nat, k1, Nat.mod(1n+x, 1n+tp), hk) : {S.runs(S.red(Nat.is_eq(1n+1n+q, 1n), n, S.loop(1n+q, _, n1, 1n+tp)), 1n+open) ==
            S.col_runs.close(Nat.is_eq(1n+q, 0n), 1n+open, S.col_runs(1n+q, 1n+x, 1n+tp, S.col_runs.next(Nat.is_eq(1n+q, 0n), 1n+open))) : List<&2, Nat>}
          k(1n+open, {==})

# runs(loop(iters, x % tk, n, tk), open) == col_runs(iters, x, tk, open), whenever the loop has an
# iteration left or no run is open.
def c_pieces(+iters: Nat, +x: Nat, +tp: Nat, +n: Nat, +open: Nat,
    h0: {Bool.or(Nat.is_lt(0n, iters), Nat.is_eq(open, 0n)) == True{} : Bool})
  -> {S.runs(S.loop(iters, Nat.mod(x, 1n+tp), n, 1n+tp), open) == S.col_runs(iters, x, 1n+tp, open) : List<&2, Nat>}:
  match iters:
    case 0n:
      %Equal.sym(Nat, open, 0n, PP.ar_eq_true(open, 0n, h0)) : {S.runs(Nil{}, _) == Nil{} : List<&2, Nat>}
      {==}
    case 1n+r:
      +c = Nat.mod(x, 1n+tp)
      +W = Nat.is_le(tp, c)
      c_step(Nat.is_eq(c, tp), r, x, tp, n, S.sel(W, 1n+n, n), open, S.sel(W, 0n, 1n+c),
        Nat.is_eq(c, Nat.sub(tp, 0n)), Nat.is_eq(Nat.mod(1n+x, 1n+tp), 0n),
        c_subz(c, tp), c_colend(x, tp), c_next_k(x, tp),
        o => h => c_pieces(r, 1n+x, tp, S.sel(W, 1n+n, n), o, h))

def Laws.stock_runs_are_column_pieces(iters, x, tk, tpos):
  match tk:
    case 0n:
      Empty.absurd({S.runs(S.loop(iters, Nat.mod(x, 0n), Nat.div(x, 0n), 0n), 0n) == S.col_runs(iters, x, 0n, 0n) : List<&2, Nat>},
        PP.ar_false_true(tpos))
    case 1n+tp:
      c_pieces(iters, x, tp, Nat.div(x, 1n+tp), 0n, c_or_true_r(Nat.is_lt(0n, iters)))

# ==== corollaries: the per-tile run position ====

# o + (MMAs to the end of the open run) <= L whenever every run of the trace is at most L.
def rem_ok(+evs: List<&2, DSpec.Ev>, +o: Nat, +L: Nat, +h: {E.runs_ok(evs, o, L) == True{} : Bool})
  -> {Nat.is_le(Nat.add(o, R.rem(evs)), L) == True{} : Bool}:
  match evs:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(o, 0n), o, NO.add_zero_r(o)) : {Nat.is_le(_, L) == True{} : Bool}
      h
    case ev <> rest:
      match ev:
        case DSpec.It{x, w, r, xo, fold}:
          match fold:
            case True{}:
              %Equal.sym(Nat, Nat.add(o, 1n), Nat.add(1n, o), NO.add_comm(o, 1n)) : {Nat.is_le(_, L) == True{} : Bool}
              NO.and_l(Nat.is_le(1n+o, L), E.runs_ok(rest, 0n, L), h)
            case False{}:
              %Equal.sym(Nat, Nat.add(o, 1n+R.rem(rest)), 1n+Nat.add(o, R.rem(rest)), NO.add_succ_r(o, R.rem(rest))) :
                {Nat.is_le(_, L) == True{} : Bool}
              rem_ok(rest, 1n+o, L, NO.and_r(Nat.is_le(1n+o, L), E.runs_ok(rest, 1n+o, L), h))
        case DSpec.Seg{g}:
          %Equal.sym(Nat, Nat.add(o, 0n), o, NO.add_zero_r(o)) : {Nat.is_le(_, L) == True{} : Bool}
          NO.and_l(Nat.is_le(o, L), E.runs_ok(rest, 0n, L), h)
        case DSpec.Pro{w}:
          rem_ok(rest, o, L, h)
        case DSpec.Exit{st}:
          rem_ok(rest, o, L, h)

# Every tile's tr is at most L whenever every run of the trace is at most L.
def tr_ok(+evs: List<&2, DSpec.Ev>, +i: Nat, +o: Nat, +L: Nat, +h: {E.runs_ok(evs, o, L) == True{} : Bool})
  -> {Nat.is_le(R.tr_at(evs, i), L) == True{} : Bool}:
  match evs:
    case Nil{}:
      NO.le_zero(L)
    case ev <> rest:
      match ev:
        case DSpec.It{+x, +w, +r, +xo, +fold}:
          match i:
            case 0n:
              +t = R.rem_it(fold, R.rem(rest))
              NO.le_trans(t, Nat.add(o, t), L, NO.le_add_l(o, t), rem_ok(DSpec.It{x, w, r, xo, fold} <> rest, o, L, h))
            case 1n+j:
              tr_ok(rest, j, E.rsel(fold, 0n, 1n+o), L,
                NO.and_r(Nat.is_le(1n+o, L), E.runs_ok(rest, E.rsel(fold, 0n, 1n+o), L), h))
        case DSpec.Seg{g}:
          match i:
            case 0n:
              NO.le_zero(L)
            case 1n+j:
              tr_ok(rest, j, 0n, L, NO.and_r(Nat.is_le(o, L), E.runs_ok(rest, 0n, L), h))
        case DSpec.Pro{w}:
          match i:
            case 0n:
              NO.le_zero(L)
            case 1n+j:
              tr_ok(rest, j, o, L, h)
        case DSpec.Exit{st}:
          match i:
            case 0n:
              NO.le_zero(L)
            case 1n+j:
              tr_ok(rest, j, o, L, h)

def pos_it(fold: Bool, +n: Nat) -> {Nat.is_le(1n, R.rem_it(fold, n)) == True{} : Bool}:
  match fold:
    case True{}:
      {==}
    case False{}:
      NO.le_zero(n)

def Laws.tr_bound_m16g(s, n, KT, i, tiles):
  tr_ok(Diet.diet_m16g(s, n, KT, E.pf(), E.xr(), E.fold(), E.ws(), E.xi()), i, 0n, E.fold(),
    Laws.fold_runs_m16g(s, n, KT, tiles))

def Laws.tr_bound_tail(s0, n0, k0, s1, n1, k1, s2, n2, k2, r1, r2, i, kt0, kt1, kt2, ring1, ring2):
  tr_ok(Diet.diet_tail(DSpec.Ph{s0, n0, k0}, DSpec.Ph{s1, n1, k1}, DSpec.Ph{s2, n2, k2}, r1, r2, E.pf(),
      E.xr(), E.fold(), E.ws(), E.xi()), i, 0n, E.fold(),
    Laws.fold_runs_tail(s0, n0, k0, s1, n1, k1, s2, n2, k2, r1, r2, kt0, kt1, kt2, ring1, ring2))

def Laws.tr_pos(evs, i, it):
  match evs:
    case Nil{}:
      Empty.absurd({Nat.is_le(1n, R.tr_at(Nil{}, i)) == True{} : Bool}, NO.false_true(it))
    case ev <> rest:
      match ev:
        case DSpec.It{x, w, r, xo, fold}:
          match i:
            case 0n:
              pos_it(fold, R.rem(rest))
            case 1n+j:
              Laws.tr_pos(rest, j, it)
        case DSpec.Seg{g}:
          match i:
            case 0n:
              Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, NO.false_true(it))
            case 1n+j:
              Laws.tr_pos(rest, j, it)
        case DSpec.Pro{w}:
          match i:
            case 0n:
              Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, NO.false_true(it))
            case 1n+j:
              Laws.tr_pos(rest, j, it)
        case DSpec.Exit{st}:
          match i:
            case 0n:
              Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, NO.false_true(it))
            case 1n+j:
              Laws.tr_pos(rest, j, it)

