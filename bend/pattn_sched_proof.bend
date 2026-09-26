# Proofs of pattn_sched_laws.bend (ext 3010 prefill attention tile schedule). Nat lemmas come from
# gemm_m16_partition_proof.bend (Ar); the ceiling-division and boolean helpers from
# attn_stride_proof.bend (SP), whose Impl.cdiv is the one pattn_sched.bend uses (Stride.cdiv).
import Base
import ./pattn_sched.bend as P
import ./pattn_sched_spec.bend as Spec
import ./pattn_sched_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar
import ./attn_stride_proof.bend as SP

def Laws.lanes_once():
  ({==}, {==})

# ---------------------------------------------------------------------------------------------
# Tile / span membership

# c * 32 <= p < c * 32 + 32 (and s) iff s && c == p / 32
def ps_core(+c: Nat, +p: Nat, +s: Bool)
  -> {Bool.and(Nat.is_le(Nat.mul(c, 32n), p), Bool.and(Nat.is_lt(p, Nat.add(Nat.mul(c, 32n), 32n)), s)) ==
     Bool.and(s, Nat.is_eq(c, Nat.div(p, 32n))) : Bool}:
  match s:
    case False{}:
      SP.sp_and3_false(Nat.is_le(Nat.mul(c, 32n), p), Nat.is_lt(p, Nat.add(Nat.mul(c, 32n), 32n)))
    case True{}:
      +m = Nat.mul(c, 32n)
      +t = Nat.div(p, 32n)
      +z = Nat.is_lt(p, Nat.add(m, 32n))
      %Equal.sym(Bool, Bool.and(z, True{}), z, SP.sp_and_true_r(z)) : {Bool.and(Nat.is_le(m, p), _) == Nat.is_eq(c, t) : Bool}
      %Equal.sym(Nat, Nat.add(m, 32n), Nat.add(32n, m), Ar.ar_add_comm(m, 32n)) : {Bool.and(Nat.is_le(m, p), Nat.is_lt(p, _)) == Nat.is_eq(c, t) : Bool}
      %Ar.ar_div_lt(1n+c, p, 32n, {==}) : {Bool.and(Nat.is_le(m, p), _) == Nat.is_eq(c, t) : Bool}
      %Equal.sym(Bool, Nat.is_le(m, p), Nat.is_le(c, t), Ar.ar_div_le(c, p, 32n, {==})) : {Bool.and(_, Nat.is_lt(t, 1n+c)) == Nat.is_eq(c, t) : Bool}
      SP.sp_le_lt_eq(c, t)

def Laws.span_member(g, d):
  %SP.sp_and_true_r(Nat.is_lt(d, Nat.add(Nat.mul(g, 32n), 32n))) : {Bool.and(Nat.is_le(Nat.mul(g, 32n), d), _) == Nat.is_eq(g, P.span(d)) : Bool}
  ps_core(g, d, True{})

# (x && e) && !e == False
def ps_and_not(+x: Bool, +e: Bool) -> {Bool.and(Bool.and(x, e), Bool.not(e)) == False{} : Bool}:
  match x e:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Laws.tile_unique(L, q, qb, r, it, p):
  +X = Bool.and(Nat.is_lt(it, P.ntiles(L, q, qb)), P.mask_ok(P.masked(L, q, qb, it), L, q, qb, r, p))
  +e = Nat.is_eq(it, Nat.div(p, 32n))
  %Equal.sym(Bool, P.visits(L, q, qb, r, it, p), Bool.and(X, e), ps_core(it, p, X)) : {Bool.and(_, Bool.not(e)) == False{} : Bool}
  ps_and_not(X, e)

def Laws.span_flush(g, s, k, sb, kb):
  +S = Nat.mul(s, 16n)
  +o = Nat.add(S, k)
  +h1 = Ar.ard_tr(Nat.is_lt(o, Nat.add(S, 16n)), Nat.is_lt(k, 16n), Ar.ar_lt_add_cancel(S, k, 16n), kb)
  +h2 = Ar.ar_le_mul_mono(1n+s, 2n, 16n,
    Ar.ard_rt(Nat.is_lt(s, 2n), Nat.is_le(1n+s, 2n), Ar.ar_lt_succ_le(s, 2n), sb))
  +h1b = Equal.trans(Bool, Nat.is_lt(o, Nat.add(16n, S)), Nat.is_lt(o, Nat.add(S, 16n)), True{},
    Equal.cong(Nat, Bool, z => Nat.is_lt(o, z), Nat.add(16n, S), Nat.add(S, 16n), Ar.ar_add_comm(16n, S)), h1)
  +small = Ar.ar_lt_le_trans(o, Nat.mul(1n+s, 16n), 32n, h1b, h2)
  Ar.ard_fst({Nat.div(Nat.add(Nat.mul(g, 32n), o), 32n) == g : Nat}, {Nat.mod(Nat.add(Nat.mul(g, 32n), o), 32n) == o : Nat},
    Ar.ar_div_unique(g, o, 32n, small))

def Laws.gqa_rows(kvh, w, qb, r, wb, rb):
  +w6 = wb
  +r16 = rb
  (Ar.ard_fst({Nat.div(Nat.add(Nat.mul(kvh, 6n), w), 6n) == kvh : Nat}, {Nat.mod(Nat.add(Nat.mul(kvh, 6n), w), 6n) == w : Nat}, Ar.ar_div_unique(kvh, w, 6n, w6)),
   Ar.ard_snd({Nat.div(Nat.add(Nat.mul(kvh, 6n), w), 6n) == kvh : Nat}, {Nat.mod(Nat.add(Nat.mul(kvh, 6n), w), 6n) == w : Nat}, Ar.ar_div_unique(kvh, w, 6n, w6)),
   Ar.ard_fst({Nat.div(Nat.add(Nat.mul(qb, 16n), r), 16n) == qb : Nat}, {Nat.mod(Nat.add(Nat.mul(qb, 16n), r), 16n) == r : Nat}, Ar.ar_div_unique(qb, r, 16n, r16)),
   Ar.ard_snd({Nat.div(Nat.add(Nat.mul(qb, 16n), r), 16n) == qb : Nat}, {Nat.mod(Nat.add(Nat.mul(qb, 16n), r), 16n) == r : Nat}, Ar.ar_div_unique(qb, r, 16n, r16)))

# ---------------------------------------------------------------------------------------------
# Page addressing

def Laws.tile_in_page(it):
  +u = Nat.div(it, 8n)
  +v = Nat.mod(it, 8n)
  +vlt = Ar.ard_dm_lt(it, 8n, {==})
  +vs = Ar.ard_tr(Nat.is_lt(Nat.mul(v, 32n), 256n), Nat.is_lt(v, 8n), Ar.ar_mul_lt_cancel(v, 8n, 32n, {==}), vlt)
  +e1 = Equal.trans(Nat, Nat.mul(it, 32n), Nat.mul(Nat.add(Nat.mul(u, 8n), v), 32n), Nat.add(Nat.mul(u, 256n), Nat.mul(v, 32n)),
    Equal.cong(Nat, Nat, z => Nat.mul(z, 32n), it, Nat.add(Nat.mul(u, 8n), v), Equal.sym(Nat, Nat.add(Nat.mul(u, 8n), v), it, Ar.ard_dm_eq(it, 8n, {==}))),
    Equal.trans(Nat, Nat.mul(Nat.add(Nat.mul(u, 8n), v), 32n), Nat.add(Nat.mul(Nat.mul(u, 8n), 32n), Nat.mul(v, 32n)), Nat.add(Nat.mul(u, 256n), Nat.mul(v, 32n)),
      Ar.ar_mul_add_l(Nat.mul(u, 8n), v, 32n),
      Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(v, 32n)), Nat.mul(Nat.mul(u, 8n), 32n), Nat.mul(u, 256n), Ar.ar_mul_assoc(u, 8n, 32n))))
  +e2 = Equal.trans(Nat, Nat.mod(Nat.mul(it, 32n), 256n), Nat.mod(Nat.add(Nat.mul(u, 256n), Nat.mul(v, 32n)), 256n), Nat.mul(v, 32n),
    Equal.cong(Nat, Nat, z => Nat.mod(z, 256n), Nat.mul(it, 32n), Nat.add(Nat.mul(u, 256n), Nat.mul(v, 32n)), e1),
    Ar.ard_snd({Nat.div(Nat.add(Nat.mul(u, 256n), Nat.mul(v, 32n)), 256n) == u : Nat}, {Nat.mod(Nat.add(Nat.mul(u, 256n), Nat.mul(v, 32n)), 256n) == Nat.mul(v, 32n) : Nat},
      Ar.ar_div_unique(u, Nat.mul(v, 32n), 256n, vs)))
  %Equal.sym(Nat, Nat.mod(Nat.mul(it, 32n), 256n), Nat.mul(v, 32n), e2) : {Nat.is_le(Nat.add(_, 32n), 256n) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(Nat.mul(v, 32n), 32n), Nat.add(32n, Nat.mul(v, 32n)), Ar.ar_add_comm(Nat.mul(v, 32n), 32n)) : {Nat.is_le(_, 256n) == True{} : Bool}
  Ar.ar_le_mul_mono(1n+v, 8n, 32n, Ar.ard_rt(Nat.is_lt(v, 8n), Nat.is_le(1n+v, 8n), Ar.ar_lt_succ_le(v, 8n), vlt))

# ---------------------------------------------------------------------------------------------
# Causal coverage

# The row's absolute position (L - q) + (16 qb + r) is below L
def ps_pos_lt(+L: Nat, +q: Nat, +j: Nat, row: {Nat.is_lt(j, q) == True{} : Bool}, len: {Nat.is_le(q, L) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.sub(L, q), j), L) == True{} : Bool}:
  +D = Nat.sub(L, q)
  +h = Ar.ard_tr(Nat.is_lt(Nat.add(D, j), Nat.add(D, q)), Nat.is_lt(j, q), Ar.ar_lt_add_cancel(D, j, q), row)
  +eL = Equal.trans(Nat, Nat.add(D, q), Nat.add(q, D), L, Ar.ar_add_comm(D, q), Ar.ar_sub_add(L, q, len))
  %eL : {Nat.is_lt(Nat.add(D, j), _) == True{} : Bool}
  h

# The kernel's row bound q_abs0 + r is the spec's (L - q) + (16 qb + r)
def ps_assoc(+L: Nat, +q: Nat, +qb: Nat, +r: Nat)
  -> {P.row_abs(L, q, qb, r) == Nat.add(Nat.sub(L, q), P.q_pos(qb, r)) : Nat}:
  Ar.ar_add_assoc(Nat.sub(L, q), Nat.mul(qb, 16n), r)

# Soundness per mask state: a kept key of a tile ending by n0 + 32 is at or before q_abs0 + r
def ps_sound_m(m: Bool, +L: Nat, +q: Nat, +qb: Nat, +r: Nat, +it: Nat, +p: Nat,
    hm: {P.masked(L, q, qb, it) == m : Bool},
    hlt: {Nat.is_lt(p, Nat.add(P.n0(it), 32n)) == True{} : Bool},
    hk: {P.mask_ok(m, L, q, qb, r, p) == True{} : Bool})
  -> {Nat.is_le(p, P.row_abs(L, q, qb, r)) == True{} : Bool}:
  match m:
    case True{}:
      Ar.ar_and_l(Nat.is_le(p, P.row_abs(L, q, qb, r)), Nat.is_lt(p, L), hk)
    case False{}:
      +A = P.q_abs0(L, q, qb)
      +B = Nat.add(P.n0(it), 31n)
      +hBA = Ar.p6_nlt_le(A, B, hm)
      +hpB = Ar.ard_tr(Nat.is_le(p, B), Nat.is_lt(p, 1n+B), Ar.p1_le_lt_succ(p, B),
        Equal.trans(Bool, Nat.is_lt(p, 1n+B), Nat.is_lt(p, Nat.add(P.n0(it), 32n)), True{},
          Equal.cong(Nat, Bool, z => Nat.is_lt(p, z), 1n+B, Nat.add(P.n0(it), 32n), Equal.sym(Nat, Nat.add(P.n0(it), 32n), 1n+B, Ar.ar_add_succ_r(P.n0(it), 31n))),
          hlt))
      Ar.ar_le_trans(p, A, Nat.add(A, r), Ar.ar_le_trans(p, B, A, hpB, hBA), Ar.ar_le_add_r(A, r))

# The kept keys under a true mask are inside the chunk: the mask state never matters for the bound
def ps_complete_m(m: Bool, +L: Nat, +q: Nat, +qb: Nat, +r: Nat, +p: Nat,
    hpa: {Nat.is_le(p, P.row_abs(L, q, qb, r)) == True{} : Bool},
    hpL: {Nat.is_lt(p, L) == True{} : Bool})
  -> {P.mask_ok(m, L, q, qb, r, p) == True{} : Bool}:
  match m:
    case False{}:
      {==}
    case True{}:
      Ar.ar_and_intro(Nat.is_le(p, P.row_abs(L, q, qb, r)), Nat.is_lt(p, L), hpa, hpL)

# visits(it, p) gives the tile end and the mask part
def ps_part_lt(+L: Nat, +q: Nat, +qb: Nat, +r: Nat, +it: Nat, +p: Nat,
    h: {P.visits(L, q, qb, r, it, p) == True{} : Bool})
  -> {Nat.is_lt(p, Nat.add(P.n0(it), 32n)) == True{} : Bool}:
  +R2 = Bool.and(Nat.is_lt(it, P.ntiles(L, q, qb)), P.mask_ok(P.masked(L, q, qb, it), L, q, qb, r, p))
  Ar.ar_and_l(Nat.is_lt(p, Nat.add(P.n0(it), 32n)), R2,
    Ar.ar_and_r(Nat.is_le(P.n0(it), p), Bool.and(Nat.is_lt(p, Nat.add(P.n0(it), 32n)), R2), h))

def ps_part_k(+L: Nat, +q: Nat, +qb: Nat, +r: Nat, +it: Nat, +p: Nat,
    h: {P.visits(L, q, qb, r, it, p) == True{} : Bool})
  -> {P.mask_ok(P.masked(L, q, qb, it), L, q, qb, r, p) == True{} : Bool}:
  +R2 = Bool.and(Nat.is_lt(it, P.ntiles(L, q, qb)), P.mask_ok(P.masked(L, q, qb, it), L, q, qb, r, p))
  Ar.ar_and_r(Nat.is_lt(it, P.ntiles(L, q, qb)), P.mask_ok(P.masked(L, q, qb, it), L, q, qb, r, p),
    Ar.ar_and_r(Nat.is_lt(p, Nat.add(P.n0(it), 32n)), R2,
      Ar.ar_and_r(Nat.is_le(P.n0(it), p), Bool.and(Nat.is_lt(p, Nat.add(P.n0(it), 32n)), R2), h)))

def ps_sound(+L: Nat, +q: Nat, +qb: Nat, +r: Nat, +it: Nat, +p: Nat,
    +h: {P.visits(L, q, qb, r, it, p) == True{} : Bool})
  -> {Nat.is_le(p, Nat.add(Nat.sub(L, q), P.q_pos(qb, r))) == True{} : Bool}:
  +hlt = ps_part_lt(L, q, qb, r, it, p, h)
  +hk = ps_part_k(L, q, qb, r, it, p, h)
  +hs = ps_sound_m(P.masked(L, q, qb, it), L, q, qb, r, it, p, {==}, hlt, hk)
  %ps_assoc(L, q, qb, r) : {Nat.is_le(p, _) == True{} : Bool}
  hs

def Laws.no_key_past(L, q, qb, r, it, p, row, len, hit):
  +hs = ps_sound(L, q, qb, r, it, p, hit)
  (hs, Ar.ar_le_lt_trans(p, Nat.add(Nat.sub(L, q), P.q_pos(qb, r)), L, hs, ps_pos_lt(L, q, P.q_pos(qb, r), row, len)))

# A visible key is kept by its own tile p / 32
def ps_complete(+L: Nat, +q: Nat, +qb: Nat, +r: Nat, +p: Nat,
    rb: {Nat.is_lt(r, 16n) == True{} : Bool},
    row: {Nat.is_lt(P.q_pos(qb, r), q) == True{} : Bool},
    len: {Nat.is_le(q, L) == True{} : Bool},
    hs: {Nat.is_le(p, Nat.add(Nat.sub(L, q), P.q_pos(qb, r))) == True{} : Bool})
  -> {Bool.and(Nat.is_lt(Nat.div(p, 32n), P.ntiles(L, q, qb)), P.mask_ok(P.masked(L, q, qb, Nat.div(p, 32n)), L, q, qb, r, p)) == True{} : Bool}:
  +t = Nat.div(p, 32n)
  +A = P.q_abs0(L, q, qb)
  +a = P.row_abs(L, q, qb, r)
  +hpa = Equal.trans(Bool, Nat.is_le(p, a), Nat.is_le(p, Nat.add(Nat.sub(L, q), P.q_pos(qb, r))), True{},
    Equal.cong(Nat, Bool, z => Nat.is_le(p, z), a, Nat.add(Nat.sub(L, q), P.q_pos(qb, r)), ps_assoc(L, q, qb, r)), hs)
  +haL = Equal.trans(Bool, Nat.is_lt(a, L), Nat.is_lt(Nat.add(Nat.sub(L, q), P.q_pos(qb, r)), L), True{},
    Equal.cong(Nat, Bool, z => Nat.is_lt(z, L), a, Nat.add(Nat.sub(L, q), P.q_pos(qb, r)), ps_assoc(L, q, qb, r)),
    ps_pos_lt(L, q, P.q_pos(qb, r), row, len))
  +hpL = Ar.ar_le_lt_trans(p, a, L, hpa, haL)
  +hlo = Ar.ard_le_mul_div(p, 32n, {==})
  +ha16 = Ar.ard_tr(Nat.is_lt(a, Nat.add(A, 16n)), Nat.is_lt(r, 16n), Ar.ar_lt_add_cancel(A, r, 16n), rb)
  +h1 = Ar.ar_le_lt_trans(Nat.mul(t, 32n), p, Nat.add(A, 16n), hlo, Ar.ar_le_lt_trans(p, a, Nat.add(A, 16n), hpa, ha16))
  +h2 = Ar.ar_le_lt_trans(Nat.mul(t, 32n), p, L, hlo, hpL)
  +hmin = Ar.ard_tr(Nat.is_lt(Nat.mul(t, 32n), P.n_hi(L, q, qb)),
    Bool.and(Nat.is_lt(Nat.mul(t, 32n), Nat.add(A, 16n)), Nat.is_lt(Nat.mul(t, 32n), L)),
    Ar.ar_min_lt(Nat.mul(t, 32n), Nat.add(A, 16n), L),
    Ar.ar_and_intro(Nat.is_lt(Nat.mul(t, 32n), Nat.add(A, 16n)), Nat.is_lt(Nat.mul(t, 32n), L), h1, h2))
  +hnt = SP.sp_lt_cdiv(t, P.n_hi(L, q, qb), 32n, {==}, hmin)
  Ar.ar_and_intro(Nat.is_lt(t, P.ntiles(L, q, qb)), P.mask_ok(P.masked(L, q, qb, t), L, q, qb, r, p), hnt,
    ps_complete_m(P.masked(L, q, qb, t), L, q, qb, r, p, hpa, hpL))

# visits(p / 32, p) == the loop-and-mask part X(p / 32)
def ps_own(+L: Nat, +q: Nat, +qb: Nat, +r: Nat, +p: Nat)
  -> {P.visits(L, q, qb, r, Nat.div(p, 32n), p) ==
     Bool.and(Nat.is_lt(Nat.div(p, 32n), P.ntiles(L, q, qb)), P.mask_ok(P.masked(L, q, qb, Nat.div(p, 32n)), L, q, qb, r, p)) : Bool}:
  +t = Nat.div(p, 32n)
  +X = Bool.and(Nat.is_lt(t, P.ntiles(L, q, qb)), P.mask_ok(P.masked(L, q, qb, t), L, q, qb, r, p))
  %Equal.sym(Bool, P.visits(L, q, qb, r, t, p), Bool.and(X, Nat.is_eq(t, t)), ps_core(t, p, X)) : {_ == X : Bool}
  %Equal.sym(Bool, Nat.is_eq(t, t), True{}, Ar.ar_eq_refl(t)) : {Bool.and(X, _) == X : Bool}
  SP.sp_and_true_r(X)

def Laws.attend_once(L, q, qb, r, p, rb, row, len):
  +t = Nat.div(p, 32n)
  +X = Bool.and(Nat.is_lt(t, P.ntiles(L, q, qb)), P.mask_ok(P.masked(L, q, qb, t), L, q, qb, r, p))
  +S = Spec.sees(L, q, P.q_pos(qb, r), p)
  +eX = Ar.ar_bool_ext(X, S,
    h => ps_sound(L, q, qb, r, t, p, Ar.ard_tr(P.visits(L, q, qb, r, t, p), X, ps_own(L, q, qb, r, p), h)),
    h => ps_complete(L, q, qb, r, p, rb, row, len, h))
  %Equal.sym(Bool, P.visits(L, q, qb, r, t, p), S, Equal.trans(Bool, P.visits(L, q, qb, r, t, p), X, S, ps_own(L, q, qb, r, p), eX)) : {Spec.once(_) == Spec.once(S) : Nat}
  {==}
