# Proofs of the ext 3007 fused pre-attention laws (attn_pre_laws.bend) about the Bend model
# attn_pre.bend. Structural evidence only: no unsafe definitions, axioms, holes, foreign proof code or
# answer tables. Nat arithmetic lemmas come from the proven m16 partition library
# (gemm_m16_partition_proof.bend) and the ceiling-division bound from attn_split_proof.bend.
import Base
import ./attn_pre.bend as Impl
import ./attn_pre_spec.bend as Spec
import ./attn_pre_laws.bend as Laws
import ./gemm_m16_partition_proof.bend as Ar
import ./attn_split_proof.bend as AS

# ==== small helpers ====

def ap_or_false(x: Bool) -> {Bool.or(x, False{}) == x : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

# lim <= step: the second iteration's index x0 + step is past lim
def ap_past(+x0: Nat, +step: Nat, +lim: Nat, fits: {Nat.is_le(lim, step) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(x0, step), lim) == False{} : Bool}:
  +le = Ar.ar_le_trans(lim, step, Nat.add(x0, step), fits, Ar.ar_le_add_l(x0, step))
  Equal.trans(Bool, Nat.is_lt(Nat.add(x0, step), lim), Bool.not(Nat.is_le(lim, Nat.add(x0, step))), False{},
    Ar.ar_lt_not_le(Nat.add(x0, step), lim),
    Equal.cong(Bool, Bool, b => Bool.not(b), Nat.is_le(lim, Nat.add(x0, step)), True{}, le))

# a loop whose condition is false yields nothing, whatever its fuel
def ap_go_nil(fuel: Nat, go: Bool, +x: Nat, +s: Nat, +l: Nat, e: {go == False{} : Bool})
  -> {Impl.loop.go(fuel, go, x, s, l) == Nil{} : List<&2, Nat>}:
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      match go:
        case False{}:
          {==}
        case True{}:
          Empty.absurd({Impl.loop.go(1n+f, True{}, x, s, l) == Nil{} : List<&2, Nat>},
            Ar.ar_false_true(Equal.sym(Bool, True{}, False{}, e)))

def ap_ls_go(go: Bool, +x0: Nat, +step: Nat, +lim: Nat, fits: {Nat.is_le(lim, step) == True{} : Bool})
  -> {Impl.loop.go(1n+lim, go, x0, step, lim) == Spec.opt(go, x0) : List<&2, Nat>}:
  match go:
    case False{}:
      {==}
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, xs => x0 <> xs,
        Impl.loop.go(lim, Nat.is_lt(Nat.add(x0, step), lim), Nat.add(x0, step), step, lim), Nil{},
        ap_go_nil(lim, Nat.is_lt(Nat.add(x0, step), lim), Nat.add(x0, step), step, lim,
          ap_past(x0, step, lim, fits)))

# `for (x = x0; x < lim; x += step)` with step >= lim runs at most once
def ap_loop_single(+x0: Nat, +step: Nat, +lim: Nat, fits: {Nat.is_le(lim, step) == True{} : Bool})
  -> {Impl.loop(x0, step, lim) == Spec.opt(Nat.is_lt(x0, lim), x0) : List<&2, Nat>}:
  ap_ls_go(Nat.is_lt(x0, lim), x0, step, lim, fits)

# membership in a one-iteration list pins the index
def ap_mem_opt(c: Bool, +x0: Nat, +h: Nat, e: {Spec.member(Spec.opt(c, x0), h) == True{} : Bool})
  -> {x0 == h : Nat}:
  match c:
    case False{}:
      Empty.absurd({x0 == h : Nat}, Ar.ar_false_true(e))
    case True{}:
      Ar.ar_eq_true(x0, h, Equal.trans(Bool, Nat.is_eq(x0, h), Bool.or(Nat.is_eq(x0, h), False{}), True{},
        Equal.sym(Bool, Bool.or(Nat.is_eq(x0, h), False{}), Nat.is_eq(x0, h), ap_or_false(Nat.is_eq(x0, h))), e))

# x == q m (m > 0) gives x / m == q
def ap_div_exact(+x: Nat, +q: Nat, +m: Nat, pos: {Nat.is_lt(0n, m) == True{} : Bool}, e: {x == Nat.mul(q, m) : Nat})
  -> {Nat.div(x, m) == q : Nat}:
  %Equal.sym(Nat, x, Nat.mul(q, m), e) : {Nat.div(_, m) == q : Nat}
  %Ar.ar_add_zero_r(Nat.mul(q, m)) : {Nat.div(_, m) == q : Nat}
  Ar.p7_div_q(q, 0n, m, pos)

# ==== (1) head jobs ====

def Laws.grid_covers(J, P, jpos, ppos):
  +pp = Equal.trans(Bool, Nat.is_lt(0n, Nat.min(P, J)), Bool.and(Nat.is_lt(0n, P), Nat.is_lt(0n, J)), True{},
    Ar.ar_min_lt(0n, P, J), Ar.ar_and_intro(Nat.is_lt(0n, P), Nat.is_lt(0n, J), ppos, jpos))
  (AS.as_up(J, Nat.min(P, J), pp), pp)

def Laws.heads_single(z, y, Pb, Z, J, fits):
  ap_loop_single(Nat.add(Nat.mul(z, Pb), y), Nat.mul(Z, Pb), J, fits)

def Laws.heads_cover(h, Pb, Z, J, pos, fits, inside):
  +ps = pos
  +ins = inside
  +ft = fits
  +hz = Ar.ar_lt_le_trans(h, J, Nat.mul(Z, Pb), ins, ft)
  +deq = Ar.p7_dm_eq(h, Pb, ps)
  +D = Nat.add(Nat.mul(Nat.div(h, Pb), Pb), Nat.mod(h, Pb))
  +single = ap_loop_single(D, Nat.mul(Z, Pb), J, ft)
  (Equal.trans(Bool, Nat.is_lt(Nat.div(h, Pb), Z), Nat.is_lt(h, Nat.mul(Z, Pb)), True{}, Ar.ar_div_lt(Z, h, Pb, ps), hz),
   Ar.p7_dm_lt(h, Pb, ps),
   Equal.trans(List<&2, Nat>, Impl.heads(Nat.div(h, Pb), Nat.mod(h, Pb), Pb, Z, J), Spec.opt(Nat.is_lt(D, J), D), h <> Nil{},
     single,
     (%Equal.sym(Nat, D, h, deq) : {Spec.opt(Nat.is_lt(_, J), _) == h <> Nil{} : List<&2, Nat>}
      %Equal.sym(Bool, Nat.is_lt(h, J), True{}, ins) : {Spec.opt(_, h) == h <> Nil{} : List<&2, Nat>}
      {==})))

def Laws.heads_exclusive(z, y, h, Pb, Z, J, row, fits, hit):
  +x0 = Nat.add(Nat.mul(z, Pb), y)
  +c = Nat.is_lt(x0, J)
  +m = Equal.trans(Bool, Spec.member(Spec.opt(c, x0), h), Spec.member(Impl.heads(z, y, Pb, Z, J), h), True{},
    Equal.cong(List<&2, Nat>, Bool, xs => Spec.member(xs, h), Spec.opt(c, x0), Impl.heads(z, y, Pb, Z, J),
      Equal.sym(List<&2, Nat>, Impl.heads(z, y, Pb, Z, J), Spec.opt(c, x0), ap_loop_single(x0, Nat.mul(Z, Pb), J, fits))),
    hit)
  +xh = ap_mem_opt(c, x0, h, m)
  +rw = row
  +dq = Ar.p7_div_q(z, y, Pb, rw)
  +dr = Ar.p7_mod_r(z, y, Pb, rw)
  (%xh : {z == Nat.div(_, Pb) : Nat}
   Equal.sym(Nat, Nat.div(x0, Pb), z, dq),
   %xh : {y == Nat.mod(_, Pb) : Nat}
   Equal.sym(Nat, Nat.mod(x0, Pb), y, dr))

# ==== (2) definitional equalities ====

def Laws.rope_dest(b, S, tok, n, h, hd, t, j):
  ({==}, {==})

def Laws.k_is_q_map(r, n, h, hd):
  {==}

def Laws.rope_pairs_match(pd, rdim, t):
  ({==}, {==})

# ==== (4) quantization: exact group offsets, slots, words ====

# kvh (C 128) + cc 128 == ((kvh C + cc) 4) 32
def ap_g0_ring(+kvh: Nat, +C: Nat, +cc: Nat)
  -> {Nat.add(Nat.mul(kvh, Nat.mul(C, 128n)), Nat.mul(cc, 128n)) ==
      Nat.mul(Nat.mul(Nat.add(Nat.mul(kvh, C), cc), 4n), 32n) : Nat}:
  +K = Nat.mul(kvh, C)
  +X = Nat.add(K, cc)
  Equal.trans(Nat, Nat.add(Nat.mul(kvh, Nat.mul(C, 128n)), Nat.mul(cc, 128n)), Nat.add(Nat.mul(K, 128n), Nat.mul(cc, 128n)),
    Nat.mul(Nat.mul(X, 4n), 32n),
    Equal.cong(Nat, Nat, u => Nat.add(u, Nat.mul(cc, 128n)), Nat.mul(kvh, Nat.mul(C, 128n)), Nat.mul(K, 128n),
      Equal.sym(Nat, Nat.mul(K, 128n), Nat.mul(kvh, Nat.mul(C, 128n)), Ar.ar_mul_assoc(kvh, C, 128n))),
    Equal.trans(Nat, Nat.add(Nat.mul(K, 128n), Nat.mul(cc, 128n)), Nat.mul(X, 128n), Nat.mul(Nat.mul(X, 4n), 32n),
      Equal.sym(Nat, Nat.mul(X, 128n), Nat.add(Nat.mul(K, 128n), Nat.mul(cc, 128n)), Ar.ar_mul_add_l(K, cc, 128n)),
      Equal.sym(Nat, Nat.mul(Nat.mul(X, 4n), 32n), Nat.mul(X, 128n), Ar.ar_mul_assoc(X, 4n, 32n))))

def Laws.g0_exact(kvh, C, cc):
  ap_div_exact(Nat.add(Nat.mul(kvh, Nat.mul(C, 128n)), Nat.mul(cc, 128n)), Nat.mul(Nat.add(Nat.mul(kvh, C), cc), 4n), 32n,
    {==}, ap_g0_ring(kvh, C, cc))

def Laws.gpt_exact(n, C):
  ap_div_exact(Nat.mul(n, Nat.mul(C, 128n)), Nat.mul(Nat.mul(n, C), 4n), 32n, {==},
    Equal.trans(Nat, Nat.mul(n, Nat.mul(C, 128n)), Nat.mul(Nat.mul(n, C), 128n), Nat.mul(Nat.mul(Nat.mul(n, C), 4n), 32n),
      Equal.sym(Nat, Nat.mul(Nat.mul(n, C), 128n), Nat.mul(n, Nat.mul(C, 128n)), Ar.ar_mul_assoc(n, C, 128n)),
      Equal.sym(Nat, Nat.mul(Nat.mul(Nat.mul(n, C), 4n), 32n), Nat.mul(Nat.mul(n, C), 128n), Ar.ar_mul_assoc(Nat.mul(n, C), 4n, 32n))))

def Laws.cache_slot(bt, bps, b, ti):
  +lt = Ar.p7_dm_lt(ti, 256n, {==})
  (Ar.p7_div_q(bt(Impl.bt_index(bps, b, ti)), Nat.mod(ti, 256n), 256n, lt),
   Ar.p7_mod_r(bt(Impl.bt_index(bps, b, ti)), Nat.mod(ti, 256n), 256n, lt))

# (q1 m + r1 == q2 m + r2, r < m): both parts, as separate lemmas
def ap_inj_q(+q1: Nat, +r1: Nat, +q2: Nat, +r2: Nat, +m: Nat, s1: {Nat.is_lt(r1, m) == True{} : Bool},
    s2: {Nat.is_lt(r2, m) == True{} : Bool}, same: {Nat.add(Nat.mul(q1, m), r1) == Nat.add(Nat.mul(q2, m), r2) : Nat})
  -> {q1 == q2 : Nat}:
  Ar.ard_fst({q1 == q2 : Nat}, {r1 == r2 : Nat}, Ar.ar_divmod_inj(q1, r1, q2, r2, m, s1, s2, same))

def ap_inj_r(+q1: Nat, +r1: Nat, +q2: Nat, +r2: Nat, +m: Nat, s1: {Nat.is_lt(r1, m) == True{} : Bool},
    s2: {Nat.is_lt(r2, m) == True{} : Bool}, same: {Nat.add(Nat.mul(q1, m), r1) == Nat.add(Nat.mul(q2, m), r2) : Nat})
  -> {r1 == r2 : Nat}:
  Ar.ard_snd({q1 == q2 : Nat}, {r1 == r2 : Nat}, Ar.ar_divmod_inj(q1, r1, q2, r2, m, s1, s2, same))

def Laws.word_inj(p1, g1, i1, p2, g2, i2, gpt, bits, gg1, gg2, ii1, ii2, same):
  +a1 = gg1
  +a2 = gg2
  +b1 = ii1
  +b2 = ii2
  +sm = same
  +q = ap_inj_q(Nat.add(Nat.mul(p1, gpt), g1), i1, Nat.add(Nat.mul(p2, gpt), g2), i2, bits, b1, b2, sm)
  (ap_inj_q(p1, g1, p2, g2, gpt, a1, a2, q), ap_inj_r(p1, g1, p2, g2, gpt, a1, a2, q),
   ap_inj_r(Nat.add(Nat.mul(p1, gpt), g1), i1, Nat.add(Nat.mul(p2, gpt), g2), i2, bits, b1, b2, sm))

# ==== (2) lanes ====

# t < 4 hd8, j < 2: the lane's half offset t 2 + j is inside the head (< 8 hd8)
def ap_lane_lt(+t: Nat, +j: Nat, +hd8: Nat, tt: {Nat.is_lt(t, Nat.mul(hd8, 4n)) == True{} : Bool},
    jj: {Nat.is_lt(j, 2n) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(t, 2n), j), Nat.mul(hd8, 8n)) == True{} : Bool}:
  %Ar.ar_mul_assoc(hd8, 4n, 2n) : {Nat.is_lt(Nat.add(Nat.mul(t, 2n), j), _) == True{} : Bool}
  Ar.p7_mr_lt(t, j, Nat.mul(hd8, 4n), 2n, tt, jj)

# 0 < hd8 gives 0 < m hd8 ... as 0 < hd8 m
def ap_pos_mul(+a: Nat, +m: Nat, apos: {Nat.is_lt(0n, a) == True{} : Bool}, mpos: {Nat.is_lt(0n, m) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.mul(a, m)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(0n, Nat.mul(a, m)), Nat.is_lt(0n, a), True{}, Ar.ar_mul_lt_cancel(0n, a, m, mpos), apos)

def Laws.head_lanes_inj(r1, h1, t1, j1, r2, h2, t2, j2, n, hd8, hh1, hh2, tt1, tt2, jj1, jj2, same):
  +hd = Nat.mul(hd8, 8n)
  +x1 = Nat.add(Nat.mul(t1, 2n), j1)
  +x2 = Nat.add(Nat.mul(t2, 2n), j2)
  +b1 = jj1
  +b2 = jj2
  +l1 = ap_lane_lt(t1, j1, hd8, tt1, b1)
  +l2 = ap_lane_lt(t2, j2, hd8, tt2, b2)
  +sm = same
  +a1 = hh1
  +a2 = hh2
  +q = ap_inj_q(Nat.add(Nat.mul(r1, n), h1), x1, Nat.add(Nat.mul(r2, n), h2), x2, hd, l1, l2, sm)
  +x = ap_inj_r(Nat.add(Nat.mul(r1, n), h1), x1, Nat.add(Nat.mul(r2, n), h2), x2, hd, l1, l2, sm)
  (ap_inj_q(r1, h1, r2, h2, n, a1, a2, q), ap_inj_r(r1, h1, r2, h2, n, a1, a2, q),
   ap_inj_q(t1, j1, t2, j2, 2n, b1, b2, x), ap_inj_r(t1, j1, t2, j2, 2n, b1, b2, x))

def Laws.head_lanes_cover(e, n, hd8, npos, dpos):
  +np = npos
  +hd = Nat.mul(hd8, 8n)
  +hp = ap_pos_mul(hd8, 8n, dpos, {==})
  +Q = Nat.div(e, hd)
  +x = Nat.mod(e, hd)
  +xlt = Ar.p7_dm_lt(e, hd, hp)
  +tlt = Equal.trans(Bool, Nat.is_lt(Nat.div(x, 2n), Nat.mul(hd8, 4n)), Nat.is_lt(x, Nat.mul(Nat.mul(hd8, 4n), 2n)), True{},
    Ar.ar_div_lt(Nat.mul(hd8, 4n), x, 2n, {==}),
    (%Equal.sym(Nat, Nat.mul(Nat.mul(hd8, 4n), 2n), Nat.mul(hd8, 8n), Ar.ar_mul_assoc(hd8, 4n, 2n)) : {Nat.is_lt(x, _) == True{} : Bool}
     xlt))
  (Ar.p7_dm_lt(Q, n, np), tlt, Ar.p7_dm_lt(x, 2n, {==}),
   Equal.trans(Nat,
     Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(Q, n), n), Nat.mod(Q, n)), hd), Nat.add(Nat.mul(Nat.div(x, 2n), 2n), Nat.mod(x, 2n))),
     Nat.add(Nat.mul(Q, hd), x), e,
     Equal.trans(Nat,
       Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(Q, n), n), Nat.mod(Q, n)), hd), Nat.add(Nat.mul(Nat.div(x, 2n), 2n), Nat.mod(x, 2n))),
       Nat.add(Nat.mul(Q, hd), Nat.add(Nat.mul(Nat.div(x, 2n), 2n), Nat.mod(x, 2n))),
       Nat.add(Nat.mul(Q, hd), x),
       Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(u, hd), Nat.add(Nat.mul(Nat.div(x, 2n), 2n), Nat.mod(x, 2n))),
         Nat.add(Nat.mul(Nat.div(Q, n), n), Nat.mod(Q, n)), Q, Ar.p7_dm_eq(Q, n, np)),
       Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(Q, hd), u),
         Nat.add(Nat.mul(Nat.div(x, 2n), 2n), Nat.mod(x, 2n)), x, Ar.p7_dm_eq(x, 2n, {==}))),
     Ar.p7_dm_eq(e, hd, hp)))

# A 2 == B 2 gives A == B
def ap_half(+A: Nat, +B: Nat, e: {Nat.mul(A, 2n) == Nat.mul(B, 2n) : Nat}) -> {A == B : Nat}:
  ap_inj_q(A, 0n, B, 0n, 2n, {==}, {==}, Equal.cong(Nat, Nat, u => Nat.add(u, 0n), Nat.mul(A, 2n), Nat.mul(B, 2n), e))

def Laws.qg_reads_inj(r1, h1, t1, j1, r2, h2, t2, j2, n, hd8, hh1, hh2, tt1, tt2, jj1, jj2, same):
  +hd = Nat.mul(hd8, 8n)
  +x1 = Nat.add(Nat.mul(t1, 2n), j1)
  +x2 = Nat.add(Nat.mul(t2, 2n), j2)
  +b1 = jj1
  +b2 = jj2
  +l1 = ap_lane_lt(t1, j1, hd8, tt1, b1)
  +l2 = ap_lane_lt(t2, j2, hd8, tt2, b2)
  +sm = same
  +a1 = hh1
  +a2 = hh2
  +Q1 = Nat.add(Nat.mul(r1, n), h1)
  +Q2 = Nat.add(Nat.mul(r2, n), h2)
  +q = ap_half(Q1, Q2, ap_inj_q(Nat.mul(Q1, 2n), x1, Nat.mul(Q2, 2n), x2, hd, l1, l2, sm))
  +x = ap_inj_r(Nat.mul(Q1, 2n), x1, Nat.mul(Q2, 2n), x2, hd, l1, l2, sm)
  (ap_inj_q(r1, h1, r2, h2, n, a1, a2, q), ap_inj_r(r1, h1, r2, h2, n, a1, a2, q),
   ap_inj_q(t1, j1, t2, j2, 2n, b1, b2, x), ap_inj_r(t1, j1, t2, j2, 2n, b1, b2, x))

# (A + hd) + y == (A' + 1) hd + y shape for the gate half: A hd + hd == (A + 1) hd
def ap_succ_mul(+A: Nat, +hd: Nat) -> {Nat.add(Nat.mul(A, hd), hd) == Nat.mul(Nat.add(A, 1n), hd) : Nat}:
  Equal.sym(Nat, Nat.mul(Nat.add(A, 1n), hd), Nat.add(Nat.mul(A, hd), hd),
    Equal.trans(Nat, Nat.mul(Nat.add(A, 1n), hd), Nat.add(Nat.mul(A, hd), Nat.mul(1n, hd)), Nat.add(Nat.mul(A, hd), hd),
      Ar.ar_mul_add_l(A, 1n, hd),
      Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(A, hd), u), Nat.mul(1n, hd), hd, Ar.ar_mul_one_l(hd))))

def ap_zero_ne_one(e: {0n == 1n : Nat}) -> Empty:
  Ar.ar_zero_succ(0n, e)

def Laws.qg_q_ne_g(r1, h1, t, j, r2, h2, i, k, n, hd8, tt, jj, ii, kk, same):
  +hd = Nat.mul(hd8, 8n)
  +x = Nat.add(Nat.mul(t, 2n), j)
  +y = Nat.add(Nat.mul(i, 8n), k)
  +A = Nat.mul(Nat.add(Nat.mul(r1, n), h1), 2n)
  +B = Nat.mul(Nat.add(Nat.mul(r2, n), h2), 2n)
  +lx = ap_lane_lt(t, j, hd8, tt, jj)
  +ly = Ar.p7_mr_lt(i, k, hd8, 8n, ii, kk)
  # g_in = (B hd + hd) + y == (B + 1) hd + y
  +g = Equal.cong(Nat, Nat, u => Nat.add(u, y), Nat.add(Nat.mul(B, hd), hd), Nat.mul(Nat.add(B, 1n), hd), ap_succ_mul(B, hd))
  +ab = ap_inj_q(A, x, Nat.add(B, 1n), y, hd, lx, ly, Equal.trans(Nat, Nat.add(Nat.mul(A, hd), x), Nat.add(Nat.add(Nat.mul(B, hd), hd), y),
    Nat.add(Nat.mul(Nat.add(B, 1n), hd), y), same, g))
  # A = Q1 2 + 0 is even, B + 1 = Q2 2 + 1 is odd
  +m0 = Ar.p7_mod_r(Nat.add(Nat.mul(r1, n), h1), 0n, 2n, {==})
  +m1 = Ar.p7_mod_r(Nat.add(Nat.mul(r2, n), h2), 1n, 2n, {==})
  ap_zero_ne_one(
    Equal.trans(Nat, 0n, Nat.mod(Nat.add(A, 0n), 2n), 1n, Equal.sym(Nat, Nat.mod(Nat.add(A, 0n), 2n), 0n, m0),
      Equal.trans(Nat, Nat.mod(Nat.add(A, 0n), 2n), Nat.mod(A, 2n), 1n,
        Equal.cong(Nat, Nat, u => Nat.mod(u, 2n), Nat.add(A, 0n), A, Ar.ar_add_zero_r(A)),
        Equal.trans(Nat, Nat.mod(A, 2n), Nat.mod(Nat.add(B, 1n), 2n), 1n,
          Equal.cong(Nat, Nat, u => Nat.mod(u, 2n), A, Nat.add(B, 1n), ab), m1))))

# ==== (2) deinterleave sources ====

# Q (8 hd8) + x == (Q hd8 + x / 8) 8 + x % 8
def ap_split8(+Q: Nat, +hd8: Nat, +x: Nat)
  -> {Nat.add(Nat.mul(Q, Nat.mul(hd8, 8n)), x) == Nat.add(Nat.mul(Nat.add(Nat.mul(Q, hd8), Nat.div(x, 8n)), 8n), Nat.mod(x, 8n)) : Nat}:
  +d = Nat.div(x, 8n)
  +m = Nat.mod(x, 8n)
  +A = Nat.mul(Q, hd8)
  # Q (hd8 8) + x == A 8 + (d 8 + m) == (A 8 + d 8) + m == (A + d) 8 + m
  Equal.trans(Nat, Nat.add(Nat.mul(Q, Nat.mul(hd8, 8n)), x), Nat.add(Nat.mul(A, 8n), Nat.add(Nat.mul(d, 8n), m)),
    Nat.add(Nat.mul(Nat.add(A, d), 8n), m),
    Equal.trans(Nat, Nat.add(Nat.mul(Q, Nat.mul(hd8, 8n)), x), Nat.add(Nat.mul(A, 8n), x), Nat.add(Nat.mul(A, 8n), Nat.add(Nat.mul(d, 8n), m)),
      Equal.cong(Nat, Nat, u => Nat.add(u, x), Nat.mul(Q, Nat.mul(hd8, 8n)), Nat.mul(A, 8n),
        Equal.sym(Nat, Nat.mul(A, 8n), Nat.mul(Q, Nat.mul(hd8, 8n)), Ar.ar_mul_assoc(Q, hd8, 8n))),
      Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(A, 8n), u), x, Nat.add(Nat.mul(d, 8n), m),
        Equal.sym(Nat, Nat.add(Nat.mul(d, 8n), m), x, Ar.p7_dm_eq(x, 8n, {==})))),
    Equal.trans(Nat, Nat.add(Nat.mul(A, 8n), Nat.add(Nat.mul(d, 8n), m)), Nat.add(Nat.add(Nat.mul(A, 8n), Nat.mul(d, 8n)), m),
      Nat.add(Nat.mul(Nat.add(A, d), 8n), m),
      Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(A, 8n), Nat.mul(d, 8n)), m), Nat.add(Nat.mul(A, 8n), Nat.add(Nat.mul(d, 8n), m)),
        Ar.ar_add_assoc(Nat.mul(A, 8n), Nat.mul(d, 8n), m)),
      Equal.cong(Nat, Nat, u => Nat.add(u, m), Nat.add(Nat.mul(A, 8n), Nat.mul(d, 8n)), Nat.mul(Nat.add(A, d), 8n),
        Equal.sym(Nat, Nat.mul(Nat.add(A, d), 8n), Nat.add(Nat.mul(A, 8n), Nat.mul(d, 8n)), Ar.ar_mul_add_l(A, d, 8n)))))

# e == I 8 + m (m < 8) gives e / 8 == I and e % 8 == m
def ap_div8(+e: Nat, +I: Nat, +m: Nat, lt: {Nat.is_lt(m, 8n) == True{} : Bool}, eq: {e == Nat.add(Nat.mul(I, 8n), m) : Nat})
  -> {Nat.div(e, 8n) == I : Nat}:
  %Equal.sym(Nat, e, Nat.add(Nat.mul(I, 8n), m), eq) : {Nat.div(_, 8n) == I : Nat}
  Ar.p7_div_q(I, m, 8n, lt)

def ap_mod8(+e: Nat, +I: Nat, +m: Nat, lt: {Nat.is_lt(m, 8n) == True{} : Bool}, eq: {e == Nat.add(Nat.mul(I, 8n), m) : Nat})
  -> {Nat.mod(e, 8n) == m : Nat}:
  %Equal.sym(Nat, e, Nat.add(Nat.mul(I, 8n), m), eq) : {Nat.mod(_, 8n) == m : Nat}
  Ar.p7_mod_r(I, m, 8n, lt)

# deint_src(Q hd8 + d, hd8) == (Q 2) hd8 + d for d < hd8
def ap_src(+Q: Nat, +d: Nat, +hd8: Nat, lt: {Nat.is_lt(d, hd8) == True{} : Bool})
  -> {Spec.deint_src(Nat.add(Nat.mul(Q, hd8), d), hd8) == Nat.add(Nat.mul(Nat.mul(Q, 2n), hd8), d) : Nat}:
  +l = lt
  %Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(Q, hd8), d), hd8), Q, Ar.p7_div_q(Q, d, hd8, l))
    : {Nat.add(Nat.mul(Nat.mul(_, 2n), hd8), Nat.mod(Nat.add(Nat.mul(Q, hd8), d), hd8)) == Nat.add(Nat.mul(Nat.mul(Q, 2n), hd8), d) : Nat}
  %Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(Q, hd8), d), hd8), d, Ar.p7_mod_r(Q, d, hd8, l))
    : {Nat.add(Nat.mul(Nat.mul(Q, 2n), hd8), _) == Nat.add(Nat.mul(Nat.mul(Q, 2n), hd8), d) : Nat}
  {==}

# (A hd8 + d) 8 + m == A (8 hd8) + (d 8 + m) : regroup for the source element
def ap_join8(+A: Nat, +hd8: Nat, +d: Nat, +m: Nat)
  -> {Nat.add(Nat.mul(Nat.add(Nat.mul(A, hd8), d), 8n), m) == Nat.add(Nat.mul(A, Nat.mul(hd8, 8n)), Nat.add(Nat.mul(d, 8n), m)) : Nat}:
  +B = Nat.mul(A, hd8)
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(B, d), 8n), m), Nat.add(Nat.add(Nat.mul(B, 8n), Nat.mul(d, 8n)), m),
    Nat.add(Nat.mul(A, Nat.mul(hd8, 8n)), Nat.add(Nat.mul(d, 8n), m)),
    Equal.cong(Nat, Nat, u => Nat.add(u, m), Nat.mul(Nat.add(B, d), 8n), Nat.add(Nat.mul(B, 8n), Nat.mul(d, 8n)), Ar.ar_mul_add_l(B, d, 8n)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(B, 8n), Nat.mul(d, 8n)), m), Nat.add(Nat.mul(B, 8n), Nat.add(Nat.mul(d, 8n), m)),
      Nat.add(Nat.mul(A, Nat.mul(hd8, 8n)), Nat.add(Nat.mul(d, 8n), m)),
      Ar.ar_add_assoc(Nat.mul(B, 8n), Nat.mul(d, 8n), m),
      Equal.cong(Nat, Nat, u => Nat.add(u, Nat.add(Nat.mul(d, 8n), m)), Nat.mul(B, 8n), Nat.mul(A, Nat.mul(hd8, 8n)), Ar.ar_mul_assoc(A, hd8, 8n))))

def Laws.q_source(r, nq, h, hd8, t, j, lane, half):
  +Q = Nat.add(Nat.mul(r, nq), h)
  +hd = Nat.mul(hd8, 8n)
  +x = Nat.add(Nat.mul(t, 2n), j)
  +xlt = ap_lane_lt(t, j, hd8, lane, half)
  +d = Nat.div(x, 8n)
  +m = Nat.mod(x, 8n)
  +mlt = Ar.p7_dm_lt(x, 8n, {==})
  +dlt = Equal.trans(Bool, Nat.is_lt(d, hd8), Nat.is_lt(x, Nat.mul(hd8, 8n)), True{}, Ar.ar_div_lt(hd8, x, 8n, {==}), xlt)
  +I = Nat.add(Nat.mul(Q, hd8), d)
  +e = Nat.add(Nat.mul(Q, hd), x)
  +eeq = ap_split8(Q, hd8, x)
  # RHS == ((Q 2) hd8 + d) 8 + m == (Q 2) hd + (d 8 + m) == (Q 2) hd + x == LHS
  Equal.sym(Nat, Spec.deint_q_elem(e, hd8), Nat.add(Nat.mul(Nat.mul(Q, 2n), hd), x),
    (%Equal.sym(Nat, Nat.div(e, 8n), I, ap_div8(e, I, m, mlt, eeq))
       : {Nat.add(Nat.mul(Spec.deint_src(_, hd8), 8n), Nat.mod(e, 8n)) == Nat.add(Nat.mul(Nat.mul(Q, 2n), hd), x) : Nat}
     %Equal.sym(Nat, Nat.mod(e, 8n), m, ap_mod8(e, I, m, mlt, eeq))
       : {Nat.add(Nat.mul(Spec.deint_src(I, hd8), 8n), _) == Nat.add(Nat.mul(Nat.mul(Q, 2n), hd), x) : Nat}
     %Equal.sym(Nat, Spec.deint_src(I, hd8), Nat.add(Nat.mul(Nat.mul(Q, 2n), hd8), d), ap_src(Q, d, hd8, dlt))
       : {Nat.add(Nat.mul(_, 8n), m) == Nat.add(Nat.mul(Nat.mul(Q, 2n), hd), x) : Nat}
     Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.mul(Q, 2n), hd8), d), 8n), m),
       Nat.add(Nat.mul(Nat.mul(Q, 2n), hd), Nat.add(Nat.mul(d, 8n), m)), Nat.add(Nat.mul(Nat.mul(Q, 2n), hd), x),
       ap_join8(Nat.mul(Q, 2n), hd8, d, m),
       Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(Nat.mul(Q, 2n), hd), u), Nat.add(Nat.mul(d, 8n), m), x, Ar.p7_dm_eq(x, 8n, {==})))))

# ((a + b) + c) + k == (a + c) + (b + k)
def ap_swap4(+a: Nat, +b: Nat, +c: Nat, +k: Nat)
  -> {Nat.add(Nat.add(Nat.add(a, b), c), k) == Nat.add(Nat.add(a, c), Nat.add(b, k)) : Nat}:
  +abc = Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, c), b),
    Ar.ar_add_assoc(a, b, c),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(a, c), b),
      Equal.cong(Nat, Nat, u => Nat.add(a, u), Nat.add(b, c), Nat.add(c, b), Ar.ar_add_comm(b, c)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), Ar.ar_add_assoc(a, c, b))))
  Equal.trans(Nat, Nat.add(Nat.add(Nat.add(a, b), c), k), Nat.add(Nat.add(Nat.add(a, c), b), k), Nat.add(Nat.add(a, c), Nat.add(b, k)),
    Equal.cong(Nat, Nat, u => Nat.add(u, k), Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(a, c), b), abc),
    Ar.ar_add_assoc(Nat.add(a, c), b, k))

def Laws.g_source(r, nq, h, hd8, i, j, vec, half):
  +Q = Nat.add(Nat.mul(r, nq), h)
  +hd = Nat.mul(hd8, 8n)
  +vl = vec
  +hl = half
  +y = Nat.add(Nat.mul(i, 8n), j)
  +I = Nat.add(Nat.mul(Q, hd8), i)
  +e = Nat.add(Nat.mul(Q, hd), y)
  # e == I 8 + j
  +eeq: {e == Nat.add(Nat.mul(I, 8n), j) : Nat} =
    (%Ar.p7_div_q(i, j, 8n, hl) : {e == Nat.add(Nat.mul(Nat.add(Nat.mul(Q, hd8), _), 8n), j) : Nat}
     %Ar.p7_mod_r(i, j, 8n, hl) : {e == Nat.add(Nat.mul(Nat.add(Nat.mul(Q, hd8), Nat.div(y, 8n)), 8n), _) : Nat}
     ap_split8(Q, hd8, y))
  +A = Nat.mul(Nat.mul(Q, 2n), hd8)
  Equal.sym(Nat, Spec.deint_g_elem(e, hd8), Nat.add(Nat.add(Nat.mul(Nat.mul(Q, 2n), hd), hd), y),
    (%Equal.sym(Nat, Nat.div(e, 8n), I, ap_div8(e, I, j, hl, eeq))
       : {Nat.add(Nat.mul(Nat.add(Spec.deint_src(_, hd8), hd8), 8n), Nat.mod(e, 8n)) == Nat.add(Nat.add(Nat.mul(Nat.mul(Q, 2n), hd), hd), y) : Nat}
     %Equal.sym(Nat, Nat.mod(e, 8n), j, ap_mod8(e, I, j, hl, eeq))
       : {Nat.add(Nat.mul(Nat.add(Spec.deint_src(I, hd8), hd8), 8n), _) == Nat.add(Nat.add(Nat.mul(Nat.mul(Q, 2n), hd), hd), y) : Nat}
     %Equal.sym(Nat, Spec.deint_src(I, hd8), Nat.add(A, i), ap_src(Q, i, hd8, vl))
       : {Nat.add(Nat.mul(Nat.add(_, hd8), 8n), j) == Nat.add(Nat.add(Nat.mul(Nat.mul(Q, 2n), hd), hd), y) : Nat}
     # ((A + i) + hd8) 8 + j == ((A 8 + i 8) + hd8 8) + j == (A 8 + hd8 8) + (i 8 + j)
     Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(Nat.add(A, i), hd8), 8n), j),
       Nat.add(Nat.add(Nat.add(Nat.mul(A, 8n), Nat.mul(i, 8n)), hd), j),
       Nat.add(Nat.add(Nat.mul(Nat.mul(Q, 2n), hd), hd), y),
       Equal.cong(Nat, Nat, u => Nat.add(u, j), Nat.mul(Nat.add(Nat.add(A, i), hd8), 8n),
         Nat.add(Nat.add(Nat.mul(A, 8n), Nat.mul(i, 8n)), hd),
         Equal.trans(Nat, Nat.mul(Nat.add(Nat.add(A, i), hd8), 8n), Nat.add(Nat.mul(Nat.add(A, i), 8n), hd),
           Nat.add(Nat.add(Nat.mul(A, 8n), Nat.mul(i, 8n)), hd),
           Ar.ar_mul_add_l(Nat.add(A, i), hd8, 8n),
           Equal.cong(Nat, Nat, u => Nat.add(u, hd), Nat.mul(Nat.add(A, i), 8n), Nat.add(Nat.mul(A, 8n), Nat.mul(i, 8n)),
             Ar.ar_mul_add_l(A, i, 8n)))),
       Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.mul(A, 8n), Nat.mul(i, 8n)), hd), j),
         Nat.add(Nat.add(Nat.mul(A, 8n), hd), y), Nat.add(Nat.add(Nat.mul(Nat.mul(Q, 2n), hd), hd), y),
         ap_swap4(Nat.mul(A, 8n), Nat.mul(i, 8n), hd, j),
         Equal.cong(Nat, Nat, u => Nat.add(Nat.add(u, hd), y), Nat.mul(A, 8n), Nat.mul(Nat.mul(Q, 2n), hd),
           Ar.ar_mul_assoc(Nat.mul(Q, 2n), hd8, 8n))))))

def Laws.word_group(phys, gpt, g0, bits, lane, pos):
  +P = Nat.add(Nat.mul(phys, gpt), g0)
  +q = Nat.div(lane, bits)
  +r = Nat.mod(lane, bits)
  Equal.sym(Nat, Nat.add(Nat.mul(Nat.add(Nat.mul(phys, gpt), Nat.add(g0, q)), bits), r), Nat.add(Nat.mul(P, bits), lane),
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(Nat.mul(phys, gpt), Nat.add(g0, q)), bits), r), Nat.add(Nat.mul(Nat.add(P, q), bits), r),
      Nat.add(Nat.mul(P, bits), lane),
      Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(u, bits), r), Nat.add(Nat.mul(phys, gpt), Nat.add(g0, q)), Nat.add(P, q),
        Equal.sym(Nat, Nat.add(P, q), Nat.add(Nat.mul(phys, gpt), Nat.add(g0, q)), Ar.ar_add_assoc(Nat.mul(phys, gpt), g0, q))),
      Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(P, q), bits), r), Nat.add(Nat.add(Nat.mul(P, bits), Nat.mul(q, bits)), r),
        Nat.add(Nat.mul(P, bits), lane),
        Equal.cong(Nat, Nat, u => Nat.add(u, r), Nat.mul(Nat.add(P, q), bits), Nat.add(Nat.mul(P, bits), Nat.mul(q, bits)),
          Ar.ar_mul_add_l(P, q, bits)),
        Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(P, bits), Nat.mul(q, bits)), r), Nat.add(Nat.mul(P, bits), Nat.add(Nat.mul(q, bits), r)),
          Nat.add(Nat.mul(P, bits), lane),
          Ar.ar_add_assoc(Nat.mul(P, bits), Nat.mul(q, bits), r),
          Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(P, bits), u), Nat.add(Nat.mul(q, bits), r), lane, Ar.p7_dm_eq(lane, bits, pos))))))

# ==== (4) chunk tiling ====

# l < 32, v < 4, cc < C: the chunk half offset cc 128 + (l 4 + v) is inside the head (< C 128)
def ap_span_lt(+cc: Nat, +l: Nat, +v: Nat, +C: Nat, c1: {Nat.is_lt(cc, C) == True{} : Bool},
    l1: {Nat.is_lt(l, 32n) == True{} : Bool}, v1: {Nat.is_lt(v, 4n) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(cc, 128n), Nat.add(Nat.mul(l, 4n), v)), Nat.mul(C, 128n)) == True{} : Bool}:
  Ar.p7_mr_lt(cc, Nat.add(Nat.mul(l, 4n), v), C, 128n, c1, Ar.p7_mr_lt(l, v, 32n, 4n, l1, v1))

# kv_src == Q hd + (cc 128 + (l 4 + v))
def ap_src_norm(+r: Nat, +n: Nat, +k: Nat, +hd: Nat, +cc: Nat, +l: Nat, +v: Nat)
  -> {Impl.kv_src(r, n, k, hd, cc, l, v) ==
      Nat.add(Nat.mul(Nat.add(Nat.mul(r, n), k), hd), Nat.add(Nat.mul(cc, 128n), Nat.add(Nat.mul(l, 4n), v))) : Nat}:
  Ar.ar_add_assoc(Nat.mul(Nat.add(Nat.mul(r, n), k), hd), Nat.mul(cc, 128n), Nat.add(Nat.mul(l, 4n), v))

def Laws.chunk_tile_inj(r1, k1, c1, l1, v1, r2, k2, c2, l2, v2, n, C, kk1, kk2, cc1, cc2, ll1, ll2, vv1, vv2, same):
  +hd = Nat.mul(C, 128n)
  +a1 = kk1
  +a2 = kk2
  +b1 = cc1
  +b2 = cc2
  +d1 = ll1
  +d2 = ll2
  +f1 = vv1
  +f2 = vv2
  +w1 = Nat.add(Nat.mul(l1, 4n), v1)
  +w2 = Nat.add(Nat.mul(l2, 4n), v2)
  +x1 = Nat.add(Nat.mul(c1, 128n), w1)
  +x2 = Nat.add(Nat.mul(c2, 128n), w2)
  +Q1 = Nat.add(Nat.mul(r1, n), k1)
  +Q2 = Nat.add(Nat.mul(r2, n), k2)
  +s1 = ap_span_lt(c1, l1, v1, C, b1, d1, f1)
  +s2 = ap_span_lt(c2, l2, v2, C, b2, d2, f2)
  +sm: {Nat.add(Nat.mul(Q1, hd), x1) == Nat.add(Nat.mul(Q2, hd), x2) : Nat} =
    Equal.trans(Nat, Nat.add(Nat.mul(Q1, hd), x1), Impl.kv_src(r1, n, k1, hd, c1, l1, v1), Nat.add(Nat.mul(Q2, hd), x2),
      Equal.sym(Nat, Impl.kv_src(r1, n, k1, hd, c1, l1, v1), Nat.add(Nat.mul(Q1, hd), x1), ap_src_norm(r1, n, k1, hd, c1, l1, v1)),
      Equal.trans(Nat, Impl.kv_src(r1, n, k1, hd, c1, l1, v1), Impl.kv_src(r2, n, k2, hd, c2, l2, v2), Nat.add(Nat.mul(Q2, hd), x2),
        same, ap_src_norm(r2, n, k2, hd, c2, l2, v2)))
  +q = ap_inj_q(Q1, x1, Q2, x2, hd, s1, s2, sm)
  +x = ap_inj_r(Q1, x1, Q2, x2, hd, s1, s2, sm)
  +m1 = Ar.p7_mr_lt(l1, v1, 32n, 4n, d1, f1)
  +m2 = Ar.p7_mr_lt(l2, v2, 32n, 4n, d2, f2)
  +w = ap_inj_r(c1, w1, c2, w2, 128n, m1, m2, x)
  (ap_inj_q(r1, k1, r2, k2, n, a1, a2, q), ap_inj_r(r1, k1, r2, k2, n, a1, a2, q),
   ap_inj_q(c1, w1, c2, w2, 128n, m1, m2, x),
   ap_inj_q(l1, v1, l2, v2, 4n, f1, f2, w), ap_inj_r(l1, v1, l2, v2, 4n, f1, f2, w))

def Laws.chunk_tile_cover(e, n, C, npos, cpos):
  +np = npos
  +hd = Nat.mul(C, 128n)
  +hp = ap_pos_mul(C, 128n, cpos, {==})
  +Q = Nat.div(e, hd)
  +x = Nat.mod(e, hd)
  +w = Nat.mod(x, 128n)
  +T = Nat.add(Nat.mul(Nat.div(w, 4n), 4n), Nat.mod(w, 4n))
  +X = Nat.add(Nat.mul(Nat.div(x, 128n), 128n), w)
  +R = Nat.add(Nat.mul(Nat.div(Q, n), n), Nat.mod(Q, n))
  (Ar.p7_dm_lt(Q, n, np),
   Equal.trans(Bool, Nat.is_lt(Nat.div(x, 128n), C), Nat.is_lt(x, hd), True{}, Ar.ar_div_lt(C, x, 128n, {==}), Ar.p7_dm_lt(e, hd, hp)),
   Equal.trans(Bool, Nat.is_lt(Nat.div(w, 4n), 32n), Nat.is_lt(w, Nat.mul(32n, 4n)), True{}, Ar.ar_div_lt(32n, w, 4n, {==}),
     Ar.p7_dm_lt(x, 128n, {==})),
   Ar.p7_dm_lt(w, 4n, {==}),
   Equal.trans(Nat, Impl.kv_src(Nat.div(Q, n), n, Nat.mod(Q, n), hd, Nat.div(x, 128n), Nat.div(w, 4n), Nat.mod(w, 4n)),
     Nat.add(Nat.mul(R, hd), Nat.add(Nat.mul(Nat.div(x, 128n), 128n), T)), e,
     ap_src_norm(Nat.div(Q, n), n, Nat.mod(Q, n), hd, Nat.div(x, 128n), Nat.div(w, 4n), Nat.mod(w, 4n)),
     Equal.trans(Nat, Nat.add(Nat.mul(R, hd), Nat.add(Nat.mul(Nat.div(x, 128n), 128n), T)), Nat.add(Nat.mul(R, hd), X), e,
       Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(R, hd), Nat.add(Nat.mul(Nat.div(x, 128n), 128n), u)), T, w, Ar.p7_dm_eq(w, 4n, {==})),
       Equal.trans(Nat, Nat.add(Nat.mul(R, hd), X), Nat.add(Nat.mul(R, hd), x), e,
         Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(R, hd), u), X, x, Ar.p7_dm_eq(x, 128n, {==})),
         Equal.trans(Nat, Nat.add(Nat.mul(R, hd), x), Nat.add(Nat.mul(Q, hd), x), e,
           Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(u, hd), x), R, Q, Ar.p7_dm_eq(Q, n, np)),
           Ar.p7_dm_eq(e, hd, hp))))))

# head_dim 128 C: chunks = C, warps = cdiv(64 C, 32) = 2 C
def ap_chunks(+C: Nat) -> {Impl.chunks(Nat.mul(C, 128n)) == C : Nat}:
  ap_div_exact(Nat.mul(C, 128n), C, 128n, {==}, {==})

def ap_sub1(+y: Nat) -> {Nat.sub(Nat.add(y, 32n), 1n) == Nat.add(y, 31n) : Nat}:
  Equal.trans(Nat, Nat.sub(Nat.add(y, 32n), 1n), Nat.sub(1n+Nat.add(y, 31n), 1n), Nat.add(y, 31n),
    Equal.cong(Nat, Nat, u => Nat.sub(u, 1n), Nat.add(y, 32n), 1n+Nat.add(y, 31n), Ar.ar_add_succ_r(y, 31n)),
    Ar.ar_sub_zero_r(Nat.add(y, 31n)))

def ap_warps(+C: Nat) -> {Impl.warps(Nat.mul(C, 128n)) == Nat.mul(2n, C) : Nat}:
  +h2 = ap_div_exact(Nat.mul(C, 128n), Nat.mul(C, 64n), 2n, {==},
    Equal.sym(Nat, Nat.mul(Nat.mul(C, 64n), 2n), Nat.mul(C, 128n), Ar.ar_mul_assoc(C, 64n, 2n)))
  %Equal.sym(Nat, Nat.div(Nat.mul(C, 128n), 2n), Nat.mul(C, 64n), h2)
    : {Nat.div(Nat.sub(Nat.add(_, 32n), 1n), 32n) == Nat.mul(2n, C) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.add(Nat.mul(C, 64n), 32n), 1n), Nat.add(Nat.mul(C, 64n), 31n), ap_sub1(Nat.mul(C, 64n)))
    : {Nat.div(_, 32n) == Nat.mul(2n, C) : Nat}
  %Ar.ar_mul_assoc(C, 2n, 32n) : {Nat.div(Nat.add(_, 31n), 32n) == Nat.mul(2n, C) : Nat}
  %Ar.ar_mul_comm(C, 2n) : {Nat.div(Nat.add(Nat.mul(Nat.mul(C, 2n), 32n), 31n), 32n) == _ : Nat}
  Ar.p7_div_q(Nat.mul(C, 2n), 31n, 32n, {==})

def Laws.warp_chunks(C, w, ww):
  +wl = ww
  +C2 = Nat.mul(2n, C)
  (ap_warps(C), ap_chunks(C),
   (%Equal.sym(Nat, Impl.warps(Nat.mul(C, 128n)), C2, ap_warps(C))
      : {Impl.loop(w, _, Nat.mul(2n, Impl.chunks(Nat.mul(C, 128n)))) == w <> Nil{} : List<&2, Nat>}
    %Equal.sym(Nat, Impl.chunks(Nat.mul(C, 128n)), C, ap_chunks(C))
      : {Impl.loop(w, C2, Nat.mul(2n, _)) == w <> Nil{} : List<&2, Nat>}
    Equal.trans(List<&2, Nat>, Impl.loop(w, C2, C2), Spec.opt(Nat.is_lt(w, C2), w), w <> Nil{},
      ap_loop_single(w, C2, C2, Ar.ar_le_refl(C2)),
      (%Equal.sym(Bool, Nat.is_lt(w, C2), True{}, wl) : {Spec.opt(_, w) == w <> Nil{} : List<&2, Nat>}
       {==}))))

def ap_cc_v(+C: Nat, +c: Nat, cw: {Nat.is_lt(c, Nat.mul(2n, C)) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(c, C), C) == True{} : Bool}:
  match C:
    case 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(c, 0n), 0n) == True{} : Bool},
        Ar.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(c, 0n), True{}, Equal.sym(Bool, Nat.is_lt(c, 0n), False{}, Ar.ar_h_lt_zero(c)), cw)))
    case 1n+p:
      Equal.trans(Bool, Nat.is_lt(Nat.sub(c, 1n+p), 1n+p), Nat.is_lt(c, Nat.add(1n+p, 1n+p)), True{},
        Ar.ar_sub_lt_iff(c, 1n+p, 1n+p, {==}),
        (%Ar.ar_add_zero_r(1n+p) : {Nat.is_lt(c, Nat.add(1n+p, _)) == True{} : Bool}
         cw))

def ap_cc(v: Bool, +c: Nat, +C: Nat, e: {Nat.is_ge(c, C) == v : Bool}, cw: {Nat.is_lt(c, Nat.mul(2n, C)) == True{} : Bool})
  -> {Nat.is_lt(Impl.cc_of.pick(v, c, C), C) == True{} : Bool}:
  match v:
    case False{}:
      +nle = Equal.trans(Bool, Nat.is_le(C, c), Nat.is_ge(c, C), False{}, Equal.sym(Bool, Nat.is_ge(c, C), Nat.is_le(C, c), Ar.ar_ge_flip(c, C)), e)
      Equal.trans(Bool, Nat.is_lt(c, C), Bool.not(Nat.is_le(C, c)), True{}, Ar.ar_lt_not_le(c, C),
        Equal.cong(Bool, Bool, b => Bool.not(b), Nat.is_le(C, c), False{}, nle))
    case True{}:
      ap_cc_v(C, c, cw)


def Laws.chunk_cc(C, c, cw):
  +w = cw
  %Equal.sym(Nat, Impl.chunks(Nat.mul(C, 128n)), C, ap_chunks(C))
    : {Nat.is_lt(Impl.cc_of.pick(Nat.is_ge(c, _), c, _), C) == True{} : Bool}
  ap_cc(Nat.is_ge(c, C), c, C, {==}, w)

# (row n) (C 128) == (row ((n C) 4)) 32
def ap_row_ring(+row: Nat, +n: Nat, +C: Nat)
  -> {Nat.mul(Nat.mul(row, n), Nat.mul(C, 128n)) == Nat.mul(Nat.mul(row, Nat.mul(Nat.mul(n, C), 4n)), 32n) : Nat}:
  +G = Nat.mul(Nat.mul(n, C), 4n)
  +M = Nat.mul(Nat.mul(n, C), 128n)
  Equal.trans(Nat, Nat.mul(Nat.mul(row, n), Nat.mul(C, 128n)), Nat.mul(row, M), Nat.mul(Nat.mul(row, G), 32n),
    Equal.trans(Nat, Nat.mul(Nat.mul(row, n), Nat.mul(C, 128n)), Nat.mul(row, Nat.mul(n, Nat.mul(C, 128n))), Nat.mul(row, M),
      Ar.ar_mul_assoc(row, n, Nat.mul(C, 128n)),
      Equal.cong(Nat, Nat, u => Nat.mul(row, u), Nat.mul(n, Nat.mul(C, 128n)), M,
        Equal.sym(Nat, M, Nat.mul(n, Nat.mul(C, 128n)), Ar.ar_mul_assoc(n, C, 128n)))),
    Equal.sym(Nat, Nat.mul(Nat.mul(row, G), 32n), Nat.mul(row, M),
      Equal.trans(Nat, Nat.mul(Nat.mul(row, G), 32n), Nat.mul(row, Nat.mul(G, 32n)), Nat.mul(row, M),
        Ar.ar_mul_assoc(row, G, 32n),
        Equal.cong(Nat, Nat, u => Nat.mul(row, u), Nat.mul(G, 32n), M, Ar.ar_mul_assoc(Nat.mul(n, C), 4n, 32n)))))

def Laws.quant_refines(bt, b, S, tok, seqlen, bps, n, kvh, C, cc, bx, usage, w, l, v, chunk):
  +ck = chunk
  +row = Nat.add(Nat.mul(b, S), tok)
  +hd = Nat.mul(C, 128n)
  +G = Nat.mul(Nat.mul(n, C), 4n)
  +K = Nat.add(Nat.mul(kvh, C), cc)
  +ch = Nat.add(Nat.mul(bx, usage), w)
  +T = Nat.add(Nat.mul(l, 4n), v)
  +RN = Nat.mul(row, n)
  # (RN + kvh) hd + cc 128 == (row G + K 4) 32
  +core: {Nat.add(Nat.mul(Nat.add(RN, kvh), hd), Nat.mul(cc, 128n)) == Nat.mul(Nat.add(Nat.mul(row, G), Nat.mul(K, 4n)), 32n) : Nat} =
    Equal.trans(Nat, Nat.add(Nat.mul(Nat.add(RN, kvh), hd), Nat.mul(cc, 128n)),
      Nat.add(Nat.add(Nat.mul(RN, hd), Nat.mul(kvh, hd)), Nat.mul(cc, 128n)),
      Nat.mul(Nat.add(Nat.mul(row, G), Nat.mul(K, 4n)), 32n),
      Equal.cong(Nat, Nat, u => Nat.add(u, Nat.mul(cc, 128n)), Nat.mul(Nat.add(RN, kvh), hd),
        Nat.add(Nat.mul(RN, hd), Nat.mul(kvh, hd)), Ar.ar_mul_add_l(RN, kvh, hd)),
      Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(RN, hd), Nat.mul(kvh, hd)), Nat.mul(cc, 128n)),
        Nat.add(Nat.mul(RN, hd), Nat.add(Nat.mul(kvh, hd), Nat.mul(cc, 128n))),
        Nat.mul(Nat.add(Nat.mul(row, G), Nat.mul(K, 4n)), 32n),
        Ar.ar_add_assoc(Nat.mul(RN, hd), Nat.mul(kvh, hd), Nat.mul(cc, 128n)),
        Equal.trans(Nat, Nat.add(Nat.mul(RN, hd), Nat.add(Nat.mul(kvh, hd), Nat.mul(cc, 128n))),
          Nat.add(Nat.mul(Nat.mul(row, G), 32n), Nat.mul(Nat.mul(K, 4n), 32n)),
          Nat.mul(Nat.add(Nat.mul(row, G), Nat.mul(K, 4n)), 32n),
          Equal.trans(Nat, Nat.add(Nat.mul(RN, hd), Nat.add(Nat.mul(kvh, hd), Nat.mul(cc, 128n))),
            Nat.add(Nat.mul(Nat.mul(row, G), 32n), Nat.add(Nat.mul(kvh, hd), Nat.mul(cc, 128n))),
            Nat.add(Nat.mul(Nat.mul(row, G), 32n), Nat.mul(Nat.mul(K, 4n), 32n)),
            Equal.cong(Nat, Nat, u => Nat.add(u, Nat.add(Nat.mul(kvh, hd), Nat.mul(cc, 128n))), Nat.mul(RN, hd),
              Nat.mul(Nat.mul(row, G), 32n), ap_row_ring(row, n, C)),
            Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(Nat.mul(row, G), 32n), u), Nat.add(Nat.mul(kvh, hd), Nat.mul(cc, 128n)),
              Nat.mul(Nat.mul(K, 4n), 32n), ap_g0_ring(kvh, C, cc))),
          Equal.sym(Nat, Nat.mul(Nat.add(Nat.mul(row, G), Nat.mul(K, 4n)), 32n),
            Nat.add(Nat.mul(Nat.mul(row, G), 32n), Nat.mul(Nat.mul(K, 4n), 32n)),
            Ar.ar_mul_add_l(Nat.mul(row, G), Nat.mul(K, 4n), 32n)))))
  (%Equal.sym(Nat, ch, K, ck)
     : {Impl.kv_src(row, n, kvh, hd, cc, l, v) == Nat.add(Nat.mul(Nat.add(Nat.mul(row, G), Nat.mul(_, 4n)), 32n), T) : Nat}
   Equal.cong(Nat, Nat, u => Nat.add(u, T), Nat.add(Nat.mul(Nat.add(RN, kvh), hd), Nat.mul(cc, 128n)),
     Nat.mul(Nat.add(Nat.mul(row, G), Nat.mul(K, 4n)), 32n), core),
   Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(Impl.token_phys(~bt, bps, b, Impl.token_idx(tok, seqlen)), G), u),
     Impl.g0(kvh, hd, cc), Nat.mul(ch, 4n),
     Equal.trans(Nat, Impl.g0(kvh, hd, cc), Nat.mul(K, 4n), Nat.mul(ch, 4n), Laws.g0_exact(kvh, C, cc),
       Equal.cong(Nat, Nat, u => Nat.mul(u, 4n), K, ch, Equal.sym(Nat, ch, K, ck)))))

# ==== (3) RoPE pairs ====

def ap_half_ph(+ph: Nat) -> {Nat.div(Nat.mul(ph, 2n), 2n) == ph : Nat}:
  ap_div_exact(Nat.mul(ph, 2n), ph, 2n, {==}, {==})

# NEOX: element s (< 2) of pair t of block r is r pd + (s ph + t), pd = 2 ph
def ap_neox_el(s: Nat, +r: Nat, +t: Nat, +ph: Nat, ss: {Nat.is_lt(s, 2n) == True{} : Bool})
  -> {Spec.side_of(s, Impl.neox_pair(Impl.offset(Nat.mul(ph, 2n), r), t, Nat.mul(ph, 2n))) ==
      Nat.add(Nat.mul(r, Nat.mul(ph, 2n)), Nat.add(Nat.mul(s, ph), t)) : Nat}:
  match s:
    case 0n:
      Equal.cong(Nat, Nat, u => Nat.add(u, t), Nat.mul(Nat.mul(ph, 2n), r), Nat.mul(r, Nat.mul(ph, 2n)), Ar.ar_mul_comm(Nat.mul(ph, 2n), r))
    case 1n+p:
      match p:
        case 0n:
          # (Nat.mul(Nat.mul(ph, 2n), r) + t) + Nat.mul(ph, 2n) / 2 == Nat.mul(r, Nat.mul(ph, 2n)) + ((ph + 0) + t)
          Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(ph, 2n), r), t), Nat.div(Nat.mul(ph, 2n), 2n)), Nat.add(Nat.add(Nat.mul(Nat.mul(ph, 2n), r), t), ph), Nat.add(Nat.mul(r, Nat.mul(ph, 2n)), Nat.add(Nat.add(ph, 0n), t)),
            Equal.cong(Nat, Nat, u => Nat.add(Nat.add(Nat.mul(Nat.mul(ph, 2n), r), t), u), Nat.div(Nat.mul(ph, 2n), 2n), ph, ap_half_ph(ph)),
            Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(ph, 2n), r), t), ph), Nat.add(Nat.mul(Nat.mul(ph, 2n), r), Nat.add(t, ph)), Nat.add(Nat.mul(r, Nat.mul(ph, 2n)), Nat.add(Nat.add(ph, 0n), t)),
              Ar.ar_add_assoc(Nat.mul(Nat.mul(ph, 2n), r), t, ph),
              Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(ph, 2n), r), Nat.add(t, ph)), Nat.add(Nat.mul(r, Nat.mul(ph, 2n)), Nat.add(t, ph)), Nat.add(Nat.mul(r, Nat.mul(ph, 2n)), Nat.add(Nat.add(ph, 0n), t)),
                Equal.cong(Nat, Nat, u => Nat.add(u, Nat.add(t, ph)), Nat.mul(Nat.mul(ph, 2n), r), Nat.mul(r, Nat.mul(ph, 2n)), Ar.ar_mul_comm(Nat.mul(ph, 2n), r)),
                Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(r, Nat.mul(ph, 2n)), u), Nat.add(t, ph), Nat.add(Nat.add(ph, 0n), t),
                  Equal.trans(Nat, Nat.add(t, ph), Nat.add(ph, t), Nat.add(Nat.add(ph, 0n), t), Ar.ar_add_comm(t, ph),
                    Equal.cong(Nat, Nat, u => Nat.add(u, t), ph, Nat.add(ph, 0n), Equal.sym(Nat, Nat.add(ph, 0n), ph, Ar.ar_add_zero_r(ph))))))))
        case 1n+q:
          Empty.absurd({Spec.side_of(2n+q, Impl.neox_pair(Nat.mul(Nat.mul(ph, 2n), r), t, Nat.mul(ph, 2n))) == Nat.add(Nat.mul(r, Nat.mul(ph, 2n)), Nat.add(Nat.mul(2n+q, ph), t)) : Nat},
            Ar.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(q, 0n), True{}, Equal.sym(Bool, Nat.is_lt(q, 0n), False{}, Ar.ar_h_lt_zero(q)), ss)))

# GPT-J: element s (< 2) of pair t of block r is r Nat.mul(ph, 2n) + (t 2 + s)
def ap_gptj_el(s: Nat, +r: Nat, +t: Nat, +ph: Nat, ss: {Nat.is_lt(s, 2n) == True{} : Bool})
  -> {Spec.side_of(s, Impl.gptj_pair(Impl.offset(Nat.mul(ph, 2n), r), t)) ==
      Nat.add(Nat.mul(r, Nat.mul(ph, 2n)), Nat.add(Nat.mul(t, 2n), s)) : Nat}:
  match s:
    case 0n:
      Equal.trans(Nat, Nat.add(Nat.mul(Nat.mul(ph, 2n), r), Nat.mul(t, 2n)), Nat.add(Nat.mul(r, Nat.mul(ph, 2n)), Nat.mul(t, 2n)), Nat.add(Nat.mul(r, Nat.mul(ph, 2n)), Nat.add(Nat.mul(t, 2n), 0n)),
        Equal.cong(Nat, Nat, u => Nat.add(u, Nat.mul(t, 2n)), Nat.mul(Nat.mul(ph, 2n), r), Nat.mul(r, Nat.mul(ph, 2n)), Ar.ar_mul_comm(Nat.mul(ph, 2n), r)),
        Equal.cong(Nat, Nat, u => Nat.add(Nat.mul(r, Nat.mul(ph, 2n)), u), Nat.mul(t, 2n), Nat.add(Nat.mul(t, 2n), 0n), Equal.sym(Nat, Nat.add(Nat.mul(t, 2n), 0n), Nat.mul(t, 2n), Ar.ar_add_zero_r(Nat.mul(t, 2n)))))
    case 1n+p:
      match p:
        case 0n:
          Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.mul(ph, 2n), r), Nat.mul(t, 2n)), 1n), Nat.add(Nat.mul(Nat.mul(ph, 2n), r), Nat.add(Nat.mul(t, 2n), 1n)), Nat.add(Nat.mul(r, Nat.mul(ph, 2n)), Nat.add(Nat.mul(t, 2n), 1n)),
            Ar.ar_add_assoc(Nat.mul(Nat.mul(ph, 2n), r), Nat.mul(t, 2n), 1n),
            Equal.cong(Nat, Nat, u => Nat.add(u, Nat.add(Nat.mul(t, 2n), 1n)), Nat.mul(Nat.mul(ph, 2n), r), Nat.mul(r, Nat.mul(ph, 2n)), Ar.ar_mul_comm(Nat.mul(ph, 2n), r)))
        case 1n+q:
          Empty.absurd({Spec.side_of(2n+q, Impl.gptj_pair(Nat.mul(Nat.mul(ph, 2n), r), t)) == Nat.add(Nat.mul(r, Nat.mul(ph, 2n)), Nat.add(Nat.mul(t, 2n), 2n+q)) : Nat},
            Ar.ar_false_true(Equal.trans(Bool, False{}, Nat.is_lt(q, 0n), True{}, Equal.sym(Bool, Nat.is_lt(q, 0n), False{}, Ar.ar_h_lt_zero(q)), ss)))

# s ph + t < ph 2 for s < 2, t < ph
def ap_neox_in(+s: Nat, +t: Nat, +ph: Nat, ss: {Nat.is_lt(s, 2n) == True{} : Bool}, tt: {Nat.is_lt(t, ph) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(s, ph), t), Nat.mul(ph, 2n)) == True{} : Bool}:
  %Ar.ar_mul_comm(2n, ph) : {Nat.is_lt(Nat.add(Nat.mul(s, ph), t), _) == True{} : Bool}
  Ar.p7_mr_lt(s, t, 2n, ph, ss, tt)

def Laws.rope_neox_inj(r1, t1, s1, r2, t2, s2, ph, tt1, tt2, ss1, ss2, same):
  +pd = Nat.mul(ph, 2n)
  +a1 = ss1
  +a2 = ss2
  +b1 = tt1
  +b2 = tt2
  +x1 = Nat.add(Nat.mul(s1, ph), t1)
  +x2 = Nat.add(Nat.mul(s2, ph), t2)
  +i1 = ap_neox_in(s1, t1, ph, a1, b1)
  +i2 = ap_neox_in(s2, t2, ph, a2, b2)
  +e: {Nat.add(Nat.mul(r1, pd), x1) == Nat.add(Nat.mul(r2, pd), x2) : Nat} =
    Equal.trans(Nat, Nat.add(Nat.mul(r1, pd), x1), Spec.side_of(s1, Impl.neox_pair(Impl.offset(pd, r1), t1, pd)), Nat.add(Nat.mul(r2, pd), x2),
      Equal.sym(Nat, Spec.side_of(s1, Impl.neox_pair(Impl.offset(pd, r1), t1, pd)), Nat.add(Nat.mul(r1, pd), x1), ap_neox_el(s1, r1, t1, ph, a1)),
      Equal.trans(Nat, Spec.side_of(s1, Impl.neox_pair(Impl.offset(pd, r1), t1, pd)), Spec.side_of(s2, Impl.neox_pair(Impl.offset(pd, r2), t2, pd)),
        Nat.add(Nat.mul(r2, pd), x2), same, ap_neox_el(s2, r2, t2, ph, a2)))
  +x = ap_inj_r(r1, x1, r2, x2, pd, i1, i2, e)
  (ap_inj_q(r1, x1, r2, x2, pd, i1, i2, e), ap_inj_r(s1, t1, s2, t2, ph, b1, b2, x), ap_inj_q(s1, t1, s2, t2, ph, b1, b2, x))

def Laws.rope_gptj_inj(r1, t1, s1, r2, t2, s2, ph, tt1, tt2, ss1, ss2, same):
  +pd = Nat.mul(ph, 2n)
  +a1 = ss1
  +a2 = ss2
  +x1 = Nat.add(Nat.mul(t1, 2n), s1)
  +x2 = Nat.add(Nat.mul(t2, 2n), s2)
  +i1 = Ar.p7_mr_lt(t1, s1, ph, 2n, tt1, a1)
  +i2 = Ar.p7_mr_lt(t2, s2, ph, 2n, tt2, a2)
  +e: {Nat.add(Nat.mul(r1, pd), x1) == Nat.add(Nat.mul(r2, pd), x2) : Nat} =
    Equal.trans(Nat, Nat.add(Nat.mul(r1, pd), x1), Spec.side_of(s1, Impl.gptj_pair(Impl.offset(pd, r1), t1)), Nat.add(Nat.mul(r2, pd), x2),
      Equal.sym(Nat, Spec.side_of(s1, Impl.gptj_pair(Impl.offset(pd, r1), t1)), Nat.add(Nat.mul(r1, pd), x1), ap_gptj_el(s1, r1, t1, ph, a1)),
      Equal.trans(Nat, Spec.side_of(s1, Impl.gptj_pair(Impl.offset(pd, r1), t1)), Spec.side_of(s2, Impl.gptj_pair(Impl.offset(pd, r2), t2)),
        Nat.add(Nat.mul(r2, pd), x2), same, ap_gptj_el(s2, r2, t2, ph, a2)))
  +x = ap_inj_r(r1, x1, r2, x2, pd, i1, i2, e)
  (ap_inj_q(r1, x1, r2, x2, pd, i1, i2, e), ap_inj_q(t1, s1, t2, s2, 2n, a1, a2, x), ap_inj_r(t1, s1, t2, s2, 2n, a1, a2, x))

def Laws.rope_pairs_cover(a, ph, pos):
  +ps = pos
  +pd = Nat.mul(ph, 2n)
  +pp = ap_pos_mul(ph, 2n, ps, {==})
  +R = Nat.div(a, pd)
  +u = Nat.mod(a, pd)
  +ult = Ar.p7_dm_lt(a, pd, pp)
  +s = Nat.div(u, ph)
  +t = Nat.mod(u, ph)
  +slt = Equal.trans(Bool, Nat.is_lt(s, 2n), Nat.is_lt(u, Nat.mul(2n, ph)), True{}, Ar.ar_div_lt(2n, u, ph, ps),
    (%Ar.ar_mul_comm(ph, 2n) : {Nat.is_lt(u, _) == True{} : Bool}
     ult))
  +tlt = Ar.p7_dm_lt(u, ph, ps)
  +gs = Nat.mod(u, 2n)
  +gt = Nat.div(u, 2n)
  +gslt = Ar.p7_dm_lt(u, 2n, {==})
  +gtlt = Equal.trans(Bool, Nat.is_lt(gt, ph), Nat.is_lt(u, pd), True{}, Ar.ar_div_lt(ph, u, 2n, {==}), ult)
  +ra = Ar.p7_dm_eq(a, pd, pp)
  (tlt, slt,
   Equal.trans(Nat, Spec.side_of(s, Impl.neox_pair(Impl.offset(pd, R), t, pd)), Nat.add(Nat.mul(R, pd), Nat.add(Nat.mul(s, ph), t)), a,
     ap_neox_el(s, R, t, ph, slt),
     Equal.trans(Nat, Nat.add(Nat.mul(R, pd), Nat.add(Nat.mul(s, ph), t)), Nat.add(Nat.mul(R, pd), u), a,
       Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(R, pd), x), Nat.add(Nat.mul(s, ph), t), u, Ar.p7_dm_eq(u, ph, ps)), ra)),
   gtlt,
   Equal.trans(Nat, Spec.side_of(gs, Impl.gptj_pair(Impl.offset(pd, R), gt)), Nat.add(Nat.mul(R, pd), Nat.add(Nat.mul(gt, 2n), gs)), a,
     ap_gptj_el(gs, R, gt, ph, gslt),
     Equal.trans(Nat, Nat.add(Nat.mul(R, pd), Nat.add(Nat.mul(gt, 2n), gs)), Nat.add(Nat.mul(R, pd), u), a,
       Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(R, pd), x), Nat.add(Nat.mul(gt, 2n), gs), u, Ar.p7_dm_eq(u, 2n, {==})), ra)))
