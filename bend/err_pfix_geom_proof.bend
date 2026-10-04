# Integer geometry of the ext 3031 chain plan and of stock's split (model err_pfix.bend): the facts err_pfix_proof.bend
# needs about the kernel's divisions, stated and proven here by structural induction and the division laws of
# gemm_m16_partition_proof.bend. No @unsafe definitions, axioms, holes or foreign code; every def precedes its uses.
import Base
import ./err_pfix.bend as Ef
import ./gemm_m16_partition_proof.bend as Ar

# chain length E = (q64 + 256) / 256 is at least 1
law pg_e_pos:
  for +q64: Nat
  {Nat.is_le(1n, Ef.e_len(q64)) == True{} : Bool}

# the K = ceil(n / E) chains of E tiles cover the row's n >= 1 tiles: (K - 1) E < n <= K E
law pg_chains:
  for +n: Nat
  for +E: Nat
  for npos: {Nat.is_le(1n, n) == True{} : Bool}
  for epos: {Nat.is_le(1n, E) == True{} : Bool}
  {Nat.is_lt(Nat.mul(Nat.sub(Ef.n_chains(n, E), 1n), E), n) == True{} : Bool} &
  {Nat.is_le(n, Nat.mul(Ef.n_chains(n, E), E)) == True{} : Bool}

# a row of stock's 64-row block from q64 (p <= q64 + 63) has at most 10 chains: n <= 8 E + 2
law pg_k10:
  for +q64: Nat
  for +p: Nat
  for phi: {Nat.is_le(p, Nat.add(q64, 63n)) == True{} : Bool}
  {Nat.is_le(Ef.n_chains(Ef.n_tiles(p), Ef.e_len(q64)), 10n) == True{} : Bool}

# its masked tiles (index >= I = (q64 + 1) / 32) are at most its last 3: n <= I + 3
law pg_masked3:
  for +q64: Nat
  for +p: Nat
  for phi: {Nat.is_le(p, Nat.add(q64, 63n)) == True{} : Bool}
  {Nat.is_le(Ef.n_tiles(p), Nat.add(Ef.interior_tiles(q64), 3n)) == True{} : Bool}

# no stock split count 2 .. 8 has shorter splits than E: for q64 < nh, E <= ceil(ceil(nh / ns) / 32)
law pg_split_ge_e:
  for +q64: Nat
  for +nh: Nat
  for +ns: Nat
  for nlo: {Nat.is_lt(q64, nh) == True{} : Bool}
  for ns1: {Nat.is_le(1n, ns) == True{} : Bool}
  for ns8: {Nat.is_le(ns, 8n) == True{} : Bool}
  {Nat.is_le(Ef.e_len(q64), Ef.split_len(nh, ns)) == True{} : Bool}

# stock's non-empty split count Ks = ceil(n / S): a row longer than one split (S < n) spans Ks >= 2 splits, n <= Ks S;
# a row inside split 0 (1 <= n <= S) has Ks = 1
law pg_ks_split:
  for +n: Nat
  for +S: Nat
  for spos: {Nat.is_le(1n, S) == True{} : Bool}
  for long: {Nat.is_lt(S, n) == True{} : Bool}
  {Nat.is_le(2n, Ef.cdiv(n, S)) == True{} : Bool} &
  {Nat.is_le(n, Nat.mul(Ef.cdiv(n, S), S)) == True{} : Bool}

law pg_ks_one:
  for +n: Nat
  for +S: Nat
  for npos: {Nat.is_le(1n, n) == True{} : Bool}
  for short: {Nat.is_le(n, S) == True{} : Bool}
  {Ef.cdiv(n, S) == 1n : Nat}

# a visible tile T < n lies in chain k = T / E at local tile t = T mod E: T = k E + t, k < K = ceil(n / E), and t is
# inside chain k: t + 1 <= chain_len(n, E, k) = min(E, n - k E)
law pg_leaf:
  for +n: Nat
  for +E: Nat
  for +T: Nat
  for epos: {Nat.is_le(1n, E) == True{} : Bool}
  for tv: {Nat.is_lt(T, n) == True{} : Bool}
  {Nat.add(Nat.mul(Nat.div(T, E), E), Nat.mod(T, E)) == T : Nat} &
  {Nat.is_lt(Nat.div(T, E), Ef.n_chains(n, E)) == True{} : Bool} &
  {Nat.is_le(1n+Nat.mod(T, E), Ef.chain_len(n, E, Nat.div(T, E))) == True{} : Bool}

# a chain is no longer than E and than the row
law pg_chain_len:
  for +n: Nat
  for +E: Nat
  for +k: Nat
  {Nat.is_le(Ef.chain_len(n, E, k), E) == True{} : Bool} &
  {Nat.is_le(Ef.chain_len(n, E, k), n) == True{} : Bool}

# a chain whose first tile k E is masked (k E >= I >= 1) is one of the last 3: k >= 1 and K <= k + 3, given
# n <= I + 3 and (K - 1) E < n, E >= 1
law pg_head_pen:
  for +E: Nat
  for +n: Nat
  for +K: Nat
  for +I: Nat
  for +k: Nat
  for epos: {Nat.is_le(1n, E) == True{} : Bool}
  for ipos: {Nat.is_le(1n, I) == True{} : Bool}
  for head: {Nat.is_le(I, Nat.mul(k, E)) == True{} : Bool}
  for m3: {Nat.is_le(n, Nat.add(I, 3n)) == True{} : Bool}
  for klo: {Nat.is_lt(Nat.mul(Nat.sub(K, 1n), E), n) == True{} : Bool}
  {Nat.is_le(1n, k) == True{} : Bool} &
  {Nat.is_le(K, Nat.add(k, 3n)) == True{} : Bool}

# chunk invariance of q_abs64 (law pfix_chunk_invariant of err_pfix_laws.bend)
law pg_chunk_invariant:
  for +u: Nat
  for +i: Nat
  {Nat.add(Nat.mul(u, 64n), Nat.mul(Nat.div(i, 64n), 64n)) == Nat.mul(Nat.div(Nat.add(Nat.mul(u, 64n), i), 64n), 64n) : Nat}

# ---------------------------------------------------------------------------------------------
# Generic helpers

# (a + (1 + bp)) - 1 == a + bp
def pg_pred(+a: Nat, +bp: Nat) -> {Nat.sub(Nat.add(a, 1n+bp), 1n) == Nat.add(a, bp) : Nat}:
  %Equal.sym(Nat, Nat.add(a, 1n+bp), 1n+Nat.add(a, bp), Ar.ar_add_succ_r(a, bp)) : {Nat.sub(_, 1n) == Nat.add(a, bp) : Nat}
  Ar.ar_sub_zero_r(Nat.add(a, bp))

# 1 <= n gives 0 < n
def pg_lt0(+n: Nat, h: {Nat.is_le(1n, n) == True{} : Bool}) -> {Nat.is_lt(0n, n) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(0n, n), Nat.is_le(1n, n), Ar.ar_lt_succ_le(0n, n), h)

# a <= b gives a + c <= b + c
def pg_add_r_mono(+a: Nat, +b: Nat, +c: Nat, h: {Nat.is_le(a, b) == True{} : Bool})
  -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  %Ar.ar_add_comm(c, a) : {Nat.is_le(_, Nat.add(b, c)) == True{} : Bool}
  %Ar.ar_add_comm(c, b) : {Nat.is_le(Nat.add(c, a), _) == True{} : Bool}
  Ar.ard_tr(Nat.is_le(Nat.add(c, a), Nat.add(c, b)), Nat.is_le(a, b), Ar.ar_le_add_cancel(c, a, b), h)

# min(a, b) <= a
def pg_min_le_l(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      pg_min_le_l(ap, bp)

# min(a, b) <= b
def pg_min_le_r(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n _:
      Ar.ar_h_le_zero(b)
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      pg_min_le_r(ap, bp)

# a - b <= a
def pg_sub_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  Ar.ard_tr(Nat.is_le(Nat.sub(a, b), a), Nat.is_le(a, Nat.add(b, a)), Ar.ar_le_sub_iff(a, b, a), Ar.ar_le_add_l(b, a))

# ---------------------------------------------------------------------------------------------
# Ceiling division Ef.cdiv (b >= 1)

# i < ceil(L / b) iff not (L <= i b)
def pg_live(+i: Nat, +L: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_lt(i, Ef.cdiv(L, b)) == Bool.not(Nat.is_le(L, Nat.mul(i, b))) : Bool}:
  match b:
    case 0n:
      Empty.absurd({Nat.is_lt(i, Ef.cdiv(L, 0n)) == Bool.not(Nat.is_le(L, Nat.mul(i, 0n))) : Bool}, Ar.ar_false_true(pos))
    case 1n+bp:
      %Equal.sym(Nat, Nat.sub(Nat.add(L, 1n+bp), 1n), Nat.add(L, bp), pg_pred(L, bp)) : {Nat.is_lt(i, Nat.div(_, 1n+bp)) == Bool.not(Nat.is_le(L, Nat.mul(i, 1n+bp))) : Bool}
      +a = Nat.add(L, bp)
      +dv = Nat.div(a, 1n+bp)
      +m = Nat.mul(i, 1n+bp)
      Equal.trans(Bool, Nat.is_lt(i, dv), Nat.is_le(1n+i, dv), Bool.not(Nat.is_le(L, m)),
        Ar.ar_lt_succ_le(i, dv),
      Equal.trans(Bool, Nat.is_le(1n+i, dv), Nat.is_le(1n+Nat.add(bp, m), a), Bool.not(Nat.is_le(L, m)),
        Equal.sym(Bool, Nat.is_le(Nat.mul(1n+i, 1n+bp), a), Nat.is_le(1n+i, dv), Ar.ar_div_le(1n+i, a, 1n+bp, pos)),
      Equal.trans(Bool, Nat.is_le(1n+Nat.add(bp, m), a), Nat.is_lt(Nat.add(bp, m), a), Bool.not(Nat.is_le(L, m)),
        Equal.sym(Bool, Nat.is_lt(Nat.add(bp, m), a), Nat.is_le(1n+Nat.add(bp, m), a), Ar.ar_lt_succ_le(Nat.add(bp, m), a)),
      Equal.trans(Bool, Nat.is_lt(Nat.add(bp, m), a), Nat.is_lt(Nat.add(bp, m), Nat.add(bp, L)), Bool.not(Nat.is_le(L, m)),
        Equal.cong(Nat, Bool, t => Nat.is_lt(Nat.add(bp, m), t), a, Nat.add(bp, L), Ar.ar_add_comm(L, bp)),
      Equal.trans(Bool, Nat.is_lt(Nat.add(bp, m), Nat.add(bp, L)), Nat.is_lt(m, L), Bool.not(Nat.is_le(L, m)),
        Ar.ar_lt_add_cancel(bp, m, L),
        Ar.ar_lt_not_le(m, L))))))

# i b < L gives i < ceil(L / b)
def pg_live_fwd(+i: Nat, +L: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool},
    h: {Nat.is_lt(Nat.mul(i, b), L) == True{} : Bool})
  -> {Nat.is_lt(i, Ef.cdiv(L, b)) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(i, Ef.cdiv(L, b)), Bool.not(Nat.is_le(L, Nat.mul(i, b))), pg_live(i, L, b, pos),
    Ar.ard_rt(Nat.is_lt(Nat.mul(i, b), L), Bool.not(Nat.is_le(L, Nat.mul(i, b))), Ar.ar_lt_not_le(Nat.mul(i, b), L), h))

# i < ceil(L / b) gives i b < L
def pg_live_bwd(+i: Nat, +L: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool},
    h: {Nat.is_lt(i, Ef.cdiv(L, b)) == True{} : Bool})
  -> {Nat.is_lt(Nat.mul(i, b), L) == True{} : Bool}:
  Ar.ard_tr(Nat.is_lt(Nat.mul(i, b), L), Bool.not(Nat.is_le(L, Nat.mul(i, b))), Ar.ar_lt_not_le(Nat.mul(i, b), L),
    Ar.ard_rt(Nat.is_lt(i, Ef.cdiv(L, b)), Bool.not(Nat.is_le(L, Nat.mul(i, b))), pg_live(i, L, b, pos), h))

# L <= ceil(L / b) b
def pg_cover(+L: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool})
  -> {Nat.is_le(L, Nat.mul(Ef.cdiv(L, b), b)) == True{} : Bool}:
  +c = Ef.cdiv(L, b)
  +x = Nat.is_le(L, Nat.mul(c, b))
  Ar.p2_not_false(x, Equal.trans(Bool, Bool.not(x), Nat.is_lt(c, c), False{},
    Equal.sym(Bool, Nat.is_lt(c, c), Bool.not(x), pg_live(c, L, b, pos)), Ar.ar_lt_irrefl(c)))

# L <= m b gives ceil(L / b) <= m
def pg_cd_le(+L: Nat, +b: Nat, +m: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool},
    h: {Nat.is_le(L, Nat.mul(m, b)) == True{} : Bool})
  -> {Nat.is_le(Ef.cdiv(L, b), m) == True{} : Bool}:
  +c = Ef.cdiv(L, b)
  +x = Nat.is_le(L, Nat.mul(m, b))
  +nx = Equal.cong(Bool, Bool, z => Bool.not(z), x, True{}, h)
  +lf = Equal.trans(Bool, Nat.is_lt(m, c), Bool.not(x), False{}, pg_live(m, L, b, pos), nx)
  Ar.p2_not_false(Nat.is_le(c, m), Equal.trans(Bool, Bool.not(Nat.is_le(c, m)), Nat.is_lt(m, c), False{},
    Equal.sym(Bool, Nat.is_lt(m, c), Bool.not(Nat.is_le(c, m)), Ar.ar_lt_not_le(m, c)), lf))

# ceil(L / b) >= 1 for L >= 1
def pg_cd_pos(+L: Nat, +b: Nat, +pos: {Nat.is_lt(0n, b) == True{} : Bool}, h: {Nat.is_le(1n, L) == True{} : Bool})
  -> {Nat.is_le(1n, Ef.cdiv(L, b)) == True{} : Bool}:
  +c = Ef.cdiv(L, b)
  Ar.ard_rt(Nat.is_lt(0n, c), Nat.is_le(1n, c), Ar.ar_lt_succ_le(0n, c), pg_live_fwd(0n, L, b, pos, pg_lt0(L, h)))

# ---------------------------------------------------------------------------------------------
# The laws

def pg_e_pos(q64):
  Ar.ard_rt(Nat.is_le(Nat.mul(1n, 256n), Nat.add(q64, 256n)), Nat.is_le(1n, Ef.e_len(q64)),
    Ar.ar_div_le(1n, Nat.add(q64, 256n), 256n, {==}), Ar.ar_le_add_l(q64, 256n))

def pg_chains(n, E, npos, epos):
  +pos = pg_lt0(E, epos)
  +K = Ef.cdiv(n, E)
  +k1 = pg_cd_pos(n, E, pos, npos)
  +j = Nat.sub(K, 1n)
  +km = Ar.ard_rt(Nat.is_le(j, j), Nat.is_lt(j, K), Ar.p1_le_pred(j, K, k1), Ar.ar_le_refl(j))
  (pg_live_bwd(j, n, E, pos, km), pg_cover(n, E, pos))

# 2 + 8 E <= 10 E for E >= 1
def pg_ten(+E: Nat, epos: {Nat.is_le(1n, E) == True{} : Bool})
  -> {Nat.is_le(Nat.add(2n, Nat.mul(E, 8n)), Nat.mul(10n, E)) == True{} : Bool}:
  +Y = Nat.mul(E, 8n)
  +A = Nat.mul(E, 2n)
  +A2 = Nat.mul(2n, E)
  +B2 = Nat.mul(8n, E)
  +T = Nat.mul(10n, E)
  +h2 = Ar.ar_le_mul_mono(1n, E, 2n, epos)
  +s1 = Equal.cong(Nat, Nat, t => Nat.add(t, Y), A, A2, Ar.ar_mul_comm(E, 2n))
  +s2 = Equal.cong(Nat, Nat, t => Nat.add(A2, t), Y, B2, Ar.ar_mul_comm(E, 8n))
  +s3 = Equal.sym(Nat, T, Nat.add(A2, B2), Ar.ar_mul_add_l(2n, 8n, E))
  +s = Equal.trans(Nat, Nat.add(A, Y), Nat.add(A2, B2), T, Equal.trans(Nat, Nat.add(A, Y), Nat.add(A2, Y), Nat.add(A2, B2), s1, s2), s3)
  Equal.trans(Bool, Nat.is_le(Nat.add(2n, Y), T), Nat.is_le(Nat.add(2n, Y), Nat.add(A, Y)), True{},
    Equal.cong(Nat, Bool, t => Nat.is_le(Nat.add(2n, Y), t), T, Nat.add(A, Y), Equal.sym(Nat, Nat.add(A, Y), T, s)),
    pg_add_r_mono(2n, A, Y, h2))

def pg_k10(q64, p, phi):
  +E = Ef.e_len(q64)
  +pos = pg_lt0(E, pg_e_pos(q64))
  +M = Nat.mul(E, 256n)
  +a = Nat.add(q64, 256n)
  +nx = Ar.ard_lt_next(a, 256n, {==})
  +na = Equal.trans(Bool, Nat.is_lt(Nat.add(256n, q64), Nat.add(256n, M)), Nat.is_lt(a, Nat.add(256n, M)), True{},
    Equal.cong(Nat, Bool, t => Nat.is_lt(t, Nat.add(256n, M)), Nat.add(256n, q64), a, Ar.ar_add_comm(256n, q64)), nx)
  +qm = Ar.ard_rt(Nat.is_lt(Nat.add(256n, q64), Nat.add(256n, M)), Nat.is_lt(q64, M), Ar.ar_lt_add_cancel(256n, q64, M), na)
  +q1 = Ar.ar_lt_trans(q64, M, 1n+M, qm, Ar.p2_lt_succ(M))
  +q63 = Ar.ard_rt(Nat.is_lt(q64, 1n+M), Nat.is_lt(Nat.add(63n, q64), Nat.add(64n, M)), {==}, q1)
  +q63b = Equal.trans(Bool, Nat.is_lt(Nat.add(q64, 63n), Nat.add(64n, M)), Nat.is_lt(Nat.add(63n, q64), Nat.add(64n, M)), True{},
    Equal.cong(Nat, Bool, t => Nat.is_lt(t, Nat.add(64n, M)), Nat.add(q64, 63n), Nat.add(63n, q64), Ar.ar_add_comm(q64, 63n)), q63)
  +pm = Ar.ar_le_lt_trans(p, Nat.add(q64, 63n), Nat.add(64n, M), phi, q63b)
  +Y = Nat.mul(E, 8n)
  +Q = Nat.add(2n, Y)
  +pq = Equal.trans(Bool, Nat.is_lt(p, Nat.mul(Q, 32n)), Nat.is_lt(p, Nat.add(64n, M)), True{},
    Equal.cong(Nat, Bool, t => Nat.is_lt(p, Nat.add(64n, t)), Nat.mul(Y, 32n), M, Ar.ar_mul_assoc(E, 8n, 32n)), pm)
  +x = Nat.div(p, 32n)
  +xq = Ar.ard_tr(Nat.is_lt(x, Q), Nat.is_lt(p, Nat.mul(Q, 32n)), Ar.ar_div_lt(Q, p, 32n, {==}), pq)
  +hn = Ar.ard_rt(Nat.is_lt(x, Q), Nat.is_le(1n+x, Q), Ar.ar_lt_succ_le(x, Q), xq)
  pg_cd_le(1n+x, E, 10n, pos, Ar.ar_le_trans(1n+x, Q, Nat.mul(10n, E), hn, pg_ten(E, pg_e_pos(q64))))

def pg_masked3(q64, p, phi):
  +I = Ef.interior_tiles(q64)
  +W = Nat.mul(I, 32n)
  +nx = Ar.ard_lt_next(Nat.add(q64, 1n), 32n, {==})
  +n1 = Equal.trans(Bool, Nat.is_lt(Nat.add(1n, q64), Nat.mul(1n+I, 32n)), Nat.is_lt(Nat.add(q64, 1n), Nat.mul(1n+I, 32n)), True{},
    Equal.cong(Nat, Bool, t => Nat.is_lt(t, Nat.mul(1n+I, 32n)), Nat.add(1n, q64), Nat.add(q64, 1n), Ar.ar_add_comm(1n, q64)), nx)
  +h31 = Ar.ard_rt(Nat.is_lt(Nat.add(1n, q64), Nat.mul(1n+I, 32n)), Nat.is_lt(q64, Nat.add(31n, W)), {==}, n1)
  +w2 = Ar.ard_rt(Nat.is_le(W, Nat.add(2n, W)), Nat.is_le(Nat.add(31n, W), Nat.add(33n, W)), {==}, Ar.ar_le_add_l(2n, W))
  +h33 = Ar.ar_lt_le_trans(q64, Nat.add(31n, W), Nat.add(33n, W), h31, w2)
  +h96 = Ar.ard_rt(Nat.is_lt(q64, Nat.add(33n, W)), Nat.is_lt(Nat.add(63n, q64), Nat.add(96n, W)), {==}, h33)
  +h96b = Equal.trans(Bool, Nat.is_lt(Nat.add(q64, 63n), Nat.add(96n, W)), Nat.is_lt(Nat.add(63n, q64), Nat.add(96n, W)), True{},
    Equal.cong(Nat, Bool, t => Nat.is_lt(t, Nat.add(96n, W)), Nat.add(q64, 63n), Nat.add(63n, q64), Ar.ar_add_comm(q64, 63n)), h96)
  +pm = Ar.ar_le_lt_trans(p, Nat.add(q64, 63n), Nat.add(96n, W), phi, h96b)
  +Q = Nat.add(3n, I)
  +pq = Ar.ard_rt(Nat.is_lt(p, Nat.add(96n, W)), Nat.is_lt(p, Nat.mul(Q, 32n)), {==}, pm)
  +x = Nat.div(p, 32n)
  +xq = Ar.ard_tr(Nat.is_lt(x, Q), Nat.is_lt(p, Nat.mul(Q, 32n)), Ar.ar_div_lt(Q, p, 32n, {==}), pq)
  +hn = Ar.ard_rt(Nat.is_lt(x, Q), Nat.is_le(1n+x, Q), Ar.ar_lt_succ_le(x, Q), xq)
  Equal.trans(Bool, Nat.is_le(1n+x, Nat.add(I, 3n)), Nat.is_le(1n+x, Q), True{},
    Equal.cong(Nat, Bool, t => Nat.is_le(1n+x, t), Nat.add(I, 3n), Q, Ar.ar_add_comm(I, 3n)), hn)

def pg_split_ge_e(q64, nh, ns, nlo, ns1, ns8):
  +pos = pg_lt0(ns, ns1)
  +C = Ef.cdiv(nh, ns)
  +S = Ef.cdiv(C, 32n)
  +E = Ef.e_len(q64)
  +M = Nat.mul(S, 256n)
  +h1 = pg_cover(nh, ns, pos)
  +h2 = pg_cover(C, 32n, {==})
  +mono = Ar.ar_le_mul_mono(ns, 8n, C, ns8)
  +eq3 = Equal.trans(Bool, Nat.is_le(Nat.mul(C, ns), Nat.mul(C, 8n)), Nat.is_le(Nat.mul(ns, C), Nat.mul(C, 8n)), Nat.is_le(Nat.mul(ns, C), Nat.mul(8n, C)),
    Equal.cong(Nat, Bool, t => Nat.is_le(t, Nat.mul(C, 8n)), Nat.mul(C, ns), Nat.mul(ns, C), Ar.ar_mul_comm(C, ns)),
    Equal.cong(Nat, Bool, t => Nat.is_le(Nat.mul(ns, C), t), Nat.mul(C, 8n), Nat.mul(8n, C), Ar.ar_mul_comm(C, 8n)))
  +h3 = Equal.trans(Bool, Nat.is_le(Nat.mul(C, ns), Nat.mul(C, 8n)), Nat.is_le(Nat.mul(ns, C), Nat.mul(8n, C)), True{}, eq3, mono)
  +h4 = Ar.ar_le_mul_mono(C, Nat.mul(S, 32n), 8n, h2)
  +h4b = Equal.trans(Bool, Nat.is_le(Nat.mul(C, 8n), M), Nat.is_le(Nat.mul(C, 8n), Nat.mul(Nat.mul(S, 32n), 8n)), True{},
    Equal.cong(Nat, Bool, t => Nat.is_le(Nat.mul(C, 8n), t), M, Nat.mul(Nat.mul(S, 32n), 8n),
      Equal.sym(Nat, Nat.mul(Nat.mul(S, 32n), 8n), M, Ar.ar_mul_assoc(S, 32n, 8n))), h4)
  +hn = Ar.ar_le_trans(nh, Nat.mul(C, ns), M, h1, Ar.ar_le_trans(Nat.mul(C, ns), Nat.mul(C, 8n), M, h3, h4b))
  +hq = Ar.ar_lt_le_trans(q64, nh, M, nlo, hn)
  +hq2 = Ar.ard_tr(Nat.is_lt(Nat.add(256n, q64), Nat.add(256n, M)), Nat.is_lt(q64, M), Ar.ar_lt_add_cancel(256n, q64, M), hq)
  +a = Nat.add(q64, 256n)
  +ha = Equal.trans(Bool, Nat.is_lt(a, Nat.mul(1n+S, 256n)), Nat.is_lt(Nat.add(256n, q64), Nat.mul(1n+S, 256n)), True{},
    Equal.cong(Nat, Bool, t => Nat.is_lt(t, Nat.mul(1n+S, 256n)), a, Nat.add(256n, q64), Ar.ar_add_comm(q64, 256n)), hq2)
  +he = Ar.ard_tr(Nat.is_lt(E, 1n+S), Nat.is_lt(a, Nat.mul(1n+S, 256n)), Ar.ar_div_lt(1n+S, a, 256n, {==}), ha)
  Ar.ard_rt(Nat.is_lt(E, 1n+S), Nat.is_le(1n+E, 1n+S), Ar.ar_lt_succ_le(E, 1n+S), he)

def pg_ks_split(n, S, spos, long):
  +pos = pg_lt0(S, spos)
  +K = Ef.cdiv(n, S)
  +h1 = Equal.trans(Bool, Nat.is_lt(Nat.mul(1n, S), n), Nat.is_lt(S, n), True{},
    Equal.cong(Nat, Bool, t => Nat.is_lt(t, n), Nat.mul(1n, S), S, Ar.ar_mul_one_l(S)), long)
  +k1 = pg_live_fwd(1n, n, S, pos, h1)
  (Ar.ard_rt(Nat.is_lt(1n, K), Nat.is_le(2n, K), Ar.ar_lt_succ_le(1n, K), k1), pg_cover(n, S, pos))

def pg_ks_one(n, S, npos, short):
  +sh = short
  +np = npos
  +spos = Ar.ar_le_trans(1n, n, S, np, sh)
  +pos = pg_lt0(S, spos)
  +K = Ef.cdiv(n, S)
  +hs = Equal.trans(Bool, Nat.is_le(n, Nat.mul(1n, S)), Nat.is_le(n, S), True{},
    Equal.cong(Nat, Bool, t => Nat.is_le(n, t), Nat.mul(1n, S), S, Ar.ar_mul_one_l(S)), sh)
  Ar.ar_le_antisym(K, 1n, pg_cd_le(n, S, 1n, pos, hs), pg_cd_pos(n, S, pos, np))

def pg_leaf(n, E, T, epos, tv):
  +tvv = tv
  +pos = pg_lt0(E, epos)
  +k = Nat.div(T, E)
  +r = Nat.mod(T, E)
  +kE = Nat.mul(k, E)
  +dm = Ar.ard_dm_eq(T, E, pos)
  +hk = pg_live_fwd(k, n, E, pos, Ar.ar_le_lt_trans(kE, T, n, Ar.ard_le_mul_div(T, E, pos), tvv))
  +rE = Ar.ard_dm_lt(T, E, pos)
  +sb = Nat.sub(n, kE)
  +rn = Equal.trans(Bool, Nat.is_lt(Nat.add(kE, r), n), Nat.is_lt(T, n), True{},
    Equal.cong(Nat, Bool, t => Nat.is_lt(t, n), Nat.add(kE, r), T, dm), tvv)
  +rs = Ar.ard_tr(Nat.is_lt(r, sb), Nat.is_lt(Nat.add(kE, r), n), Ar.ar_lt_sub_iff(n, kE, r), rn)
  +mn = Nat.min(E, sb)
  +rm = Ar.ard_tr(Nat.is_lt(r, mn), Bool.and(Nat.is_lt(r, E), Nat.is_lt(r, sb)), Ar.ar_min_lt(r, E, sb),
    Ar.ar_and_intro(Nat.is_lt(r, E), Nat.is_lt(r, sb), rE, rs))
  (dm, hk, Ar.ard_rt(Nat.is_lt(r, mn), Nat.is_le(1n+r, mn), Ar.ar_lt_succ_le(r, mn), rm))

def pg_chain_len(n, E, k):
  +sb = Nat.sub(n, Nat.mul(k, E))
  (pg_min_le_l(E, sb), Ar.ar_le_trans(Nat.min(E, sb), sb, n, pg_min_le_r(E, sb), pg_sub_le(n, Nat.mul(k, E))))

# I >= 1 and I <= k E force k >= 1
def pg_k_pos(+k: Nat, +E: Nat, +I: Nat, ipos: {Nat.is_le(1n, I) == True{} : Bool},
    head: {Nat.is_le(I, Nat.mul(k, E)) == True{} : Bool})
  -> {Nat.is_le(1n, k) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, Ar.ar_false_true(Ar.ar_le_trans(1n, I, 0n, ipos, head)))
    case 1n+kp:
      Ar.ar_h_le_zero(kp)

def pg_head_pen(E, n, K, I, k, epos, ipos, head, m3, klo):
  +ep = epos
  +hh = head
  +pos = pg_lt0(E, ep)
  +kE = Nat.mul(k, E)
  +k3 = Nat.add(k, 3n)
  +a1 = pg_add_r_mono(I, kE, 3n, hh)
  +t3 = Equal.trans(Bool, Nat.is_le(3n, Nat.mul(3n, E)), Nat.is_le(3n, Nat.mul(E, 3n)), True{},
    Equal.cong(Nat, Bool, t => Nat.is_le(3n, t), Nat.mul(3n, E), Nat.mul(E, 3n), Ar.ar_mul_comm(3n, E)),
    Ar.ar_le_mul_mono(1n, E, 3n, ep))
  +a2 = Ar.ard_tr(Nat.is_le(Nat.add(kE, 3n), Nat.add(kE, Nat.mul(3n, E))), Nat.is_le(3n, Nat.mul(3n, E)), Ar.ar_le_add_cancel(kE, 3n, Nat.mul(3n, E)), t3)
  +a3 = Equal.trans(Bool, Nat.is_le(Nat.add(kE, 3n), Nat.mul(k3, E)), Nat.is_le(Nat.add(kE, 3n), Nat.add(kE, Nat.mul(3n, E))), True{},
    Equal.cong(Nat, Bool, t => Nat.is_le(Nat.add(kE, 3n), t), Nat.mul(k3, E), Nat.add(kE, Nat.mul(3n, E)), Ar.ar_mul_add_l(k, 3n, E)), a2)
  +hb = Ar.ar_le_trans(n, Nat.add(I, 3n), Nat.mul(k3, E), m3, Ar.ar_le_trans(Nat.add(I, 3n), Nat.add(kE, 3n), Nat.mul(k3, E), a1, a3))
  +j = Nat.sub(K, 1n)
  +hc = Ar.ar_lt_le_trans(Nat.mul(j, E), n, Nat.mul(k3, E), klo, hb)
  +hd = Ar.ard_rt(Nat.is_lt(Nat.mul(j, E), Nat.mul(k3, E)), Nat.is_lt(j, k3), Ar.ar_mul_lt_cancel(j, k3, E, pos), hc)
  +p3 = Equal.trans(Bool, Nat.is_lt(0n, k3), Nat.is_lt(0n, Nat.add(3n, k)), True{},
    Equal.cong(Nat, Bool, t => Nat.is_lt(0n, t), k3, Nat.add(3n, k), Ar.ar_add_comm(k, 3n)), {==})
  (pg_k_pos(k, E, I, ipos, hh), Ar.ard_rt(Nat.is_lt(j, k3), Nat.is_le(K, k3), Ar.p1_sub1_lt(K, k3, p3), hd))

def pg_chunk_invariant(u, i):
  +U = Nat.mul(u, 64n)
  +d = Nat.div(i, 64n)
  +r = Nat.mod(i, 64n)
  +D = Nat.mul(d, 64n)
  +X = Nat.add(U, i)
  +ud = Nat.add(u, d)
  +V = Nat.mul(ud, 64n)
  +e1 = Equal.sym(Nat, Nat.add(D, r), i, Ar.ard_dm_eq(i, 64n, {==}))
  +e2 = Equal.cong(Nat, Nat, t => Nat.add(U, t), i, Nat.add(D, r), e1)
  +e3 = Equal.sym(Nat, Nat.add(Nat.add(U, D), r), Nat.add(U, Nat.add(D, r)), Ar.ar_add_assoc(U, D, r))
  +e4 = Equal.cong(Nat, Nat, t => Nat.add(t, r), Nat.add(U, D), V, Equal.sym(Nat, V, Nat.add(U, D), Ar.ar_mul_add_l(u, d, 64n)))
  +e5 = Ar.ard_fst({Nat.div(Nat.add(V, r), 64n) == ud : Nat}, {Nat.mod(Nat.add(V, r), 64n) == r : Nat},
    Ar.ar_div_unique(ud, r, 64n, Ar.ard_dm_lt(i, 64n, {==})))
  +ex = Equal.trans(Nat, X, Nat.add(Nat.add(U, D), r), Nat.add(V, r), Equal.trans(Nat, X, Nat.add(U, Nat.add(D, r)), Nat.add(Nat.add(U, D), r), e2, e3), e4)
  +dv = Equal.trans(Nat, Nat.div(X, 64n), Nat.div(Nat.add(V, r), 64n), ud, Equal.cong(Nat, Nat, t => Nat.div(t, 64n), X, Nat.add(V, r), ex), e5)
  Equal.trans(Nat, Nat.add(U, D), V, Nat.mul(Nat.div(X, 64n), 64n), Equal.sym(Nat, V, Nat.add(U, D), Ar.ar_mul_add_l(u, d, 64n)),
    Equal.cong(Nat, Nat, t => Nat.mul(t, 64n), ud, Nat.div(X, 64n), Equal.sym(Nat, Nat.div(X, 64n), ud, dv)))
