# Proofs of the ext 2113 discard laws (m16_discard_laws.bend) about the Bend model m16_discard.bend. Structural
# evidence only: no unsafe definitions, axioms, holes or foreign proof code. Address laws are proven for symbolic
# operands with the Nat library of gemm_m16_partition_proof.bend; the column / row decodes reuse its p7 lemmas
# (the same gemm_m16_partition.bend col / row the partition laws cover); finite facts are decided by evaluation.
import Base
import ./m16_discard.bend as Impl
import ./m16_discard_spec.bend as Spec
import ./m16_discard_laws.bend as Laws
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_proof.bend as Ar

# ==== equality plumbing ====

def dc_tr(-a: Nat, -b: Nat, -c: Nat, ab: {a == b : Nat}, bc: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, ab, bc)

def dc_sym(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def dc_add_l(-a: Nat, -a2: Nat, +b: Nat, e: {a == a2 : Nat}) -> {Nat.add(a, b) == Nat.add(a2, b) : Nat}:
  Equal.cong(Nat, Nat, x => Nat.add(x, b), a, a2, e)

def dc_add_r(+a: Nat, -b: Nat, -b2: Nat, e: {b == b2 : Nat}) -> {Nat.add(a, b) == Nat.add(a, b2) : Nat}:
  Equal.cong(Nat, Nat, x => Nat.add(a, x), b, b2, e)

def dc_mul_l(-a: Nat, -a2: Nat, +c: Nat, e: {a == a2 : Nat}) -> {Nat.mul(a, c) == Nat.mul(a2, c) : Nat}:
  Equal.cong(Nat, Nat, x => Nat.mul(x, c), a, a2, e)

def dc_btr(-a: Bool, -b: Bool, -c: Bool, ab: {a == b : Bool}, bc: {b == c : Bool}) -> {a == c : Bool}:
  Equal.trans(Bool, a, b, c, ab, bc)

def dc_bsym(-a: Bool, -b: Bool, e: {a == b : Bool}) -> {b == a : Bool}:
  Equal.sym(Bool, a, b, e)

def dc_fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def dc_snd(-A: Type, -B: Type, p: A & B) -> B:
  (a, b) = p
  b

# (q * b + r) / b == q and (q * b + r) % b == r for r < b
def dc_du_div(+q: Nat, +r: Nat, +b: Nat, small: {Nat.is_lt(r, b) == True{} : Bool})
  -> {Nat.div(Nat.add(Nat.mul(q, b), r), b) == q : Nat}:
  dc_fst({Nat.div(Nat.add(Nat.mul(q, b), r), b) == q : Nat}, {Nat.mod(Nat.add(Nat.mul(q, b), r), b) == r : Nat},
    Ar.ar_div_unique(q, r, b, small))

def dc_du_mod(+q: Nat, +r: Nat, +b: Nat, small: {Nat.is_lt(r, b) == True{} : Bool})
  -> {Nat.mod(Nat.add(Nat.mul(q, b), r), b) == r : Nat}:
  dc_snd({Nat.div(Nat.add(Nat.mul(q, b), r), b) == q : Nat}, {Nat.mod(Nat.add(Nat.mul(q, b), r), b) == r : Nat},
    Ar.ar_div_unique(q, r, b, small))

# q1 * m + r1 == q2 * m + r2 with r1, r2 < m: the quotients and the remainders agree
def dc_dmi_q(+q1: Nat, +r1: Nat, +q2: Nat, +r2: Nat, +m: Nat, s1: {Nat.is_lt(r1, m) == True{} : Bool},
    s2: {Nat.is_lt(r2, m) == True{} : Bool}, same: {Nat.add(Nat.mul(q1, m), r1) == Nat.add(Nat.mul(q2, m), r2) : Nat})
  -> {q1 == q2 : Nat}:
  dc_fst({q1 == q2 : Nat}, {r1 == r2 : Nat}, Ar.ar_divmod_inj(q1, r1, q2, r2, m, s1, s2, same))

def dc_dmi_r(+q1: Nat, +r1: Nat, +q2: Nat, +r2: Nat, +m: Nat, s1: {Nat.is_lt(r1, m) == True{} : Bool},
    s2: {Nat.is_lt(r2, m) == True{} : Bool}, same: {Nat.add(Nat.mul(q1, m), r1) == Nat.add(Nat.mul(q2, m), r2) : Nat})
  -> {r1 == r2 : Nat}:
  dc_snd({q1 == q2 : Nat}, {r1 == r2 : Nat}, Ar.ar_divmod_inj(q1, r1, q2, r2, m, s1, s2, same))

# ==== sum permutations ====

# ((a + c) + d) + (b + e) == (((a + b) + c) + d) + e
def dc_perm_a(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat)
  -> {Nat.add(Nat.add(Nat.add(a, c), d), Nat.add(b, e)) == Nat.add(Nat.add(Nat.add(Nat.add(a, b), c), d), e) : Nat}:
  +M = Nat.add(a, Nat.add(b, Nat.add(c, Nat.add(d, e))))
  +l1 = Ar.ar_add_assoc(Nat.add(a, c), d, Nat.add(b, e))
  +l2 = Ar.ar_add_assoc(a, c, Nat.add(d, Nat.add(b, e)))
  +l3 = dc_add_r(a, Nat.add(c, Nat.add(d, Nat.add(b, e))), Nat.add(c, Nat.add(b, Nat.add(d, e))),
    dc_add_r(c, Nat.add(d, Nat.add(b, e)), Nat.add(b, Nat.add(d, e)), Ar.ar_h_add_swap(d, b, e)))
  +l4 = dc_add_r(a, Nat.add(c, Nat.add(b, Nat.add(d, e))), Nat.add(b, Nat.add(c, Nat.add(d, e))),
    Ar.ar_h_add_swap(c, b, Nat.add(d, e)))
  +left = dc_tr(Nat.add(Nat.add(Nat.add(a, c), d), Nat.add(b, e)), Nat.add(Nat.add(a, c), Nat.add(d, Nat.add(b, e))), M, l1,
    dc_tr(Nat.add(Nat.add(a, c), Nat.add(d, Nat.add(b, e))), Nat.add(a, Nat.add(c, Nat.add(d, Nat.add(b, e)))), M, l2,
      dc_tr(Nat.add(a, Nat.add(c, Nat.add(d, Nat.add(b, e)))), Nat.add(a, Nat.add(c, Nat.add(b, Nat.add(d, e)))), M, l3, l4)))
  +r1 = Ar.ar_add_assoc(Nat.add(Nat.add(a, b), c), d, e)
  +r2 = Ar.ar_add_assoc(Nat.add(a, b), c, Nat.add(d, e))
  +r3 = Ar.ar_add_assoc(a, b, Nat.add(c, Nat.add(d, e)))
  +right = dc_tr(Nat.add(Nat.add(Nat.add(Nat.add(a, b), c), d), e), Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(d, e)), M, r1,
    dc_tr(Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(d, e)), Nat.add(Nat.add(a, b), Nat.add(c, Nat.add(d, e))), M, r2, r3))
  dc_tr(Nat.add(Nat.add(Nat.add(a, c), d), Nat.add(b, e)), M, Nat.add(Nat.add(Nat.add(Nat.add(a, b), c), d), e), left,
    dc_sym(Nat.add(Nat.add(Nat.add(Nat.add(a, b), c), d), e), M, right))

# ((a + c) + d) + (b + ((f + g) + e)) == ((((a + b) + c) + d) + f) + (g + e)
def dc_perm_b(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +f: Nat, +g: Nat, +e: Nat)
  -> {Nat.add(Nat.add(Nat.add(a, c), d), Nat.add(b, Nat.add(Nat.add(f, g), e))) ==
      Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(a, b), c), d), f), Nat.add(g, e)) : Nat}:
  +W = Nat.add(f, Nat.add(g, e))
  +M = Nat.add(a, Nat.add(b, Nat.add(c, Nat.add(d, W))))
  +y1 = dc_add_r(b, Nat.add(Nat.add(f, g), e), W, Ar.ar_add_assoc(f, g, e))
  +l1 = Ar.ar_add_assoc(Nat.add(a, c), d, Nat.add(b, Nat.add(Nat.add(f, g), e)))
  +l2 = Ar.ar_add_assoc(a, c, Nat.add(d, Nat.add(b, Nat.add(Nat.add(f, g), e))))
  +l3 = dc_add_r(a, Nat.add(c, Nat.add(d, Nat.add(b, Nat.add(Nat.add(f, g), e)))), Nat.add(c, Nat.add(d, Nat.add(b, W))),
    dc_add_r(c, Nat.add(d, Nat.add(b, Nat.add(Nat.add(f, g), e))), Nat.add(d, Nat.add(b, W)),
      dc_add_r(d, Nat.add(b, Nat.add(Nat.add(f, g), e)), Nat.add(b, W), y1)))
  +l4 = dc_add_r(a, Nat.add(c, Nat.add(d, Nat.add(b, W))), Nat.add(c, Nat.add(b, Nat.add(d, W))),
    dc_add_r(c, Nat.add(d, Nat.add(b, W)), Nat.add(b, Nat.add(d, W)), Ar.ar_h_add_swap(d, b, W)))
  +l5 = dc_add_r(a, Nat.add(c, Nat.add(b, Nat.add(d, W))), Nat.add(b, Nat.add(c, Nat.add(d, W))),
    Ar.ar_h_add_swap(c, b, Nat.add(d, W)))
  +L0 = Nat.add(Nat.add(Nat.add(a, c), d), Nat.add(b, Nat.add(Nat.add(f, g), e)))
  +L1 = Nat.add(Nat.add(a, c), Nat.add(d, Nat.add(b, Nat.add(Nat.add(f, g), e))))
  +L2 = Nat.add(a, Nat.add(c, Nat.add(d, Nat.add(b, Nat.add(Nat.add(f, g), e)))))
  +L3 = Nat.add(a, Nat.add(c, Nat.add(d, Nat.add(b, W))))
  +L4 = Nat.add(a, Nat.add(c, Nat.add(b, Nat.add(d, W))))
  +left = dc_tr(L0, L1, M, l1, dc_tr(L1, L2, M, l2, dc_tr(L2, L3, M, l3, dc_tr(L3, L4, M, l4, l5))))
  +R0 = Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(a, b), c), d), f), Nat.add(g, e))
  +R1 = Nat.add(Nat.add(Nat.add(Nat.add(a, b), c), d), W)
  +R2 = Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(d, W))
  +R3 = Nat.add(Nat.add(a, b), Nat.add(c, Nat.add(d, W)))
  +r1 = Ar.ar_add_assoc(Nat.add(Nat.add(Nat.add(a, b), c), d), f, Nat.add(g, e))
  +r2 = Ar.ar_add_assoc(Nat.add(Nat.add(a, b), c), d, W)
  +r3 = Ar.ar_add_assoc(Nat.add(a, b), c, Nat.add(d, W))
  +r4 = Ar.ar_add_assoc(a, b, Nat.add(c, Nat.add(d, W)))
  +right = dc_tr(R0, R1, M, r1, dc_tr(R1, R2, M, r2, dc_tr(R2, R3, M, r3, r4)))
  dc_tr(L0, M, R0, left, dc_sym(R0, M, right))

# ==== bounds ====

# x < k and i < n give i * k + x < n * k
def dc_lt_block(+i: Nat, +x: Nat, +k: Nat, +n: Nat, xi: {Nat.is_lt(x, k) == True{} : Bool},
    inn: {Nat.is_lt(i, n) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(i, k), x), Nat.mul(n, k)) == True{} : Bool}:
  +A = Nat.add(Nat.mul(i, k), x)
  +x1 = dc_btr(Nat.is_lt(A, Nat.add(Nat.mul(i, k), k)), Nat.is_lt(x, k), True{}, Ar.ar_lt_add_cancel(Nat.mul(i, k), x, k), xi)
  +cm = Equal.cong(Nat, Bool, z => Nat.is_lt(A, z), Nat.mul(1n+i, k), Nat.add(Nat.mul(i, k), k),
    dc_sym(Nat.add(Nat.mul(i, k), k), Nat.mul(1n+i, k), Ar.ar_add_comm(Nat.mul(i, k), k)))
  +x2 = dc_btr(Nat.is_lt(A, Nat.mul(1n+i, k)), Nat.is_lt(A, Nat.add(Nat.mul(i, k), k)), True{}, cm, x1)
  +le = Ar.ar_le_mul_mono(1n+i, n, k, dc_btr(Nat.is_le(1n+i, n), Nat.is_lt(i, n), True{},
    dc_bsym(Nat.is_lt(i, n), Nat.is_le(1n+i, n), Ar.ar_lt_succ_le(i, n)), inn))
  Ar.ar_lt_le_trans(A, Nat.mul(1n+i, k), Nat.mul(n, k), x2, le)

# ==== the nested layout ====

# (s * 16 + r) * GW == s * SLOT + r * GW
def dc_lz(+s: Nat, +r: Nat)
  -> {Nat.mul(Nat.add(Nat.mul(s, 16n), r), Impl.gw()) == Nat.add(Nat.mul(s, Impl.slot()), Nat.mul(r, Impl.gw())) : Nat}:
  dc_tr(Nat.mul(Nat.add(Nat.mul(s, 16n), r), Impl.gw()),
    Nat.add(Nat.mul(Nat.mul(s, 16n), Impl.gw()), Nat.mul(r, Impl.gw())),
    Nat.add(Nat.mul(s, Impl.slot()), Nat.mul(r, Impl.gw())),
    Ar.ar_mul_add_l(Nat.mul(s, 16n), r, Impl.gw()),
    dc_add_l(Nat.mul(Nat.mul(s, 16n), Impl.gw()), Nat.mul(s, Impl.slot()), Nat.mul(r, Impl.gw()),
      Ar.ar_mul_assoc(s, 16n, Impl.gw())))

# ((s * 16 + r) * 4 + ch) * 128 == (s * SLOT + r * GW) + ch * 128
def dc_ly(+s: Nat, +r: Nat, +ch: Nat)
  -> {Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(s, 16n), r), 4n), ch), 128n) ==
      Nat.add(Nat.add(Nat.mul(s, Impl.slot()), Nat.mul(r, Impl.gw())), Nat.mul(ch, 128n)) : Nat}:
  +Z = Nat.add(Nat.mul(s, 16n), r)
  +X = Nat.add(Nat.mul(s, Impl.slot()), Nat.mul(r, Impl.gw()))
  +z4 = dc_tr(Nat.mul(Nat.mul(Z, 4n), 128n), Nat.mul(Z, Impl.gw()), X, Ar.ar_mul_assoc(Z, 4n, 128n), dc_lz(s, r))
  dc_tr(Nat.mul(Nat.add(Nat.mul(Z, 4n), ch), 128n), Nat.add(Nat.mul(Nat.mul(Z, 4n), 128n), Nat.mul(ch, 128n)),
    Nat.add(X, Nat.mul(ch, 128n)),
    Ar.ar_mul_add_l(Nat.mul(Z, 4n), ch, 128n),
    dc_add_l(Nat.mul(Nat.mul(Z, 4n), 128n), X, Nat.mul(ch, 128n), z4))

# jline(s, r, ch, q) * 32 == ((s * SLOT + r * GW) + ch * 128) + q * 32
def dc_lj(+s: Nat, +r: Nat, +ch: Nat, +q: Nat)
  -> {Nat.mul(Spec.jline(s, r, ch, q), 32n) ==
      Nat.add(Nat.add(Nat.add(Nat.mul(s, Impl.slot()), Nat.mul(r, Impl.gw())), Nat.mul(ch, 128n)), Nat.mul(q, 32n)) : Nat}:
  +Y = Nat.add(Nat.mul(Nat.add(Nat.mul(s, 16n), r), 4n), ch)
  +X = Nat.add(Nat.add(Nat.mul(s, Impl.slot()), Nat.mul(r, Impl.gw())), Nat.mul(ch, 128n))
  +y4 = dc_tr(Nat.mul(Nat.mul(Y, 4n), 32n), Nat.mul(Y, 128n), X, Ar.ar_mul_assoc(Y, 4n, 32n), dc_ly(s, r, ch))
  dc_tr(Nat.mul(Nat.add(Nat.mul(Y, 4n), q), 32n), Nat.add(Nat.mul(Nat.mul(Y, 4n), 32n), Nat.mul(q, 32n)),
    Nat.add(X, Nat.mul(q, 32n)),
    Ar.ar_mul_add_l(Nat.mul(Y, 4n), q, 32n),
    dc_add_l(Nat.mul(Nat.mul(Y, 4n), 32n), X, Nat.mul(q, 32n), y4))

# (g * mc + c) * SLOT == g * mc * SLOT + c * SLOT, under three outer additions
def dc_split3(+G: Nat, +c: Nat, +u: Nat, +v: Nat, +w: Nat)
  -> {Nat.add(Nat.add(Nat.add(Nat.mul(Nat.add(G, c), Impl.slot()), u), v), w) ==
      Nat.add(Nat.add(Nat.add(Nat.add(Nat.mul(G, Impl.slot()), Nat.mul(c, Impl.slot())), u), v), w) : Nat}:
  dc_add_l(Nat.add(Nat.add(Nat.mul(Nat.add(G, c), Impl.slot()), u), v),
    Nat.add(Nat.add(Nat.add(Nat.mul(G, Impl.slot()), Nat.mul(c, Impl.slot())), u), v), w,
    dc_add_l(Nat.add(Nat.mul(Nat.add(G, c), Impl.slot()), u), Nat.add(Nat.add(Nat.mul(G, Impl.slot()), Nat.mul(c, Impl.slot())), u), v,
      dc_add_l(Nat.mul(Nat.add(G, c), Impl.slot()), Nat.add(Nat.mul(G, Impl.slot()), Nat.mul(c, Impl.slot())), u,
        Ar.ar_mul_add_l(G, c, Impl.slot()))))

# ==== (1) discard lines ====

def Laws.disc_lines(g, mc, r, ch, nc, i, act):
  +G = Nat.mul(g, mc)
  +D = Nat.div(i, 4n)
  +Q = Nat.mod(i, 4n)
  +S = Impl.slot()
  +a = Nat.mul(G, S)
  +b = Nat.mul(D, S)
  +c = Nat.mul(r, Impl.gw())
  +d = Nat.mul(ch, 128n)
  +e = Nat.mul(Q, 32n)
  +act4 = dc_btr(Nat.is_lt(i, Nat.mul(nc, 4n)), Nat.is_lt(i, Nat.mul(4n, nc)), True{},
    Equal.cong(Nat, Bool, z => Nat.is_lt(i, z), Nat.mul(nc, 4n), Nat.mul(4n, nc), Ar.ar_mul_comm(nc, 4n)), act)
  +p1 = dc_btr(Nat.is_lt(D, nc), Nat.is_lt(i, Nat.mul(nc, 4n)), True{}, Ar.ar_div_lt(nc, i, 4n, {==}), act4)
  +p2 = Ar.ard_dm_lt(i, 4n, {==})
  +LHS = Nat.add(Nat.add(Nat.add(a, c), d), Nat.add(b, e))
  +R4 = Nat.add(Nat.add(Nat.add(Nat.add(a, b), c), d), e)
  +J = Nat.add(Nat.add(Nat.add(Nat.mul(Nat.add(G, D), S), c), d), e)
  +p3 = dc_tr(LHS, R4, Nat.mul(Spec.jline(Nat.add(G, D), r, ch, Q), 32n), dc_perm_a(a, b, c, d, e),
    dc_tr(R4, J, Nat.mul(Spec.jline(Nat.add(G, D), r, ch, Q), 32n),
      dc_sym(J, R4, dc_split3(G, D, c, d, e)),
      dc_sym(Nat.mul(Spec.jline(Nat.add(G, D), r, ch, Q), 32n), J, dc_lj(Nat.add(G, D), r, ch, Q))))
  (p1, p2, p3)

# ==== (1) coverage of the discard loop ====

def Laws.disc_covers(nc, c, q, cn, q4):
  +qb = q4
  +i = Nat.add(Nat.mul(c, 4n), q)
  +L = Nat.mod(i, 32n)
  +K = Nat.div(i, 32n)
  +p1 = dc_tr(Nat.add(L, Nat.mul(32n, K)), Nat.add(L, Nat.mul(K, 32n)), i,
    dc_add_r(L, Nat.mul(32n, K), Nat.mul(K, 32n), Ar.ar_mul_comm(32n, K)),
    dc_tr(Nat.add(L, Nat.mul(K, 32n)), Nat.add(Nat.mul(K, 32n), L), i, Ar.ar_add_comm(L, Nat.mul(K, 32n)),
      Ar.ard_dm_eq(i, 32n, {==})))
  +p2 = Ar.ard_dm_lt(i, 32n, {==})
  +blk = dc_lt_block(c, q, 4n, nc, qb, cn)
  +p3 = dc_btr(Nat.is_lt(i, Nat.mul(4n, nc)), Nat.is_lt(i, Nat.mul(nc, 4n)), True{},
    Equal.cong(Nat, Bool, z => Nat.is_lt(i, z), Nat.mul(4n, nc), Nat.mul(nc, 4n), Ar.ar_mul_comm(4n, nc)), blk)
  (p1, p2, p3, Ar.ar_div_unique(c, q, 4n, qb))

def dc_swap_lane(+l: Nat, +k: Nat) -> {Nat.add(Nat.mul(k, 32n), l) == Impl.disc_i(l, k) : Nat}:
  dc_tr(Nat.add(Nat.mul(k, 32n), l), Nat.add(l, Nat.mul(k, 32n)), Nat.add(l, Nat.mul(32n, k)),
    Ar.ar_add_comm(Nat.mul(k, 32n), l), dc_add_r(l, Nat.mul(k, 32n), Nat.mul(32n, k), Ar.ar_mul_comm(k, 32n)))

def Laws.disc_lanes_once(l1, k1, l2, k2, s1, s2, same):
  +eq = dc_tr(Nat.add(Nat.mul(k1, 32n), l1), Impl.disc_i(l1, k1), Nat.add(Nat.mul(k2, 32n), l2), dc_swap_lane(l1, k1),
    dc_tr(Impl.disc_i(l1, k1), Impl.disc_i(l2, k2), Nat.add(Nat.mul(k2, 32n), l2), same,
      dc_sym(Nat.add(Nat.mul(k2, 32n), l2), Impl.disc_i(l2, k2), dc_swap_lane(l2, k2))))
  Ar.ar_divmod_inj(k1, l1, k2, l2, 32n, s1, s2, eq)

# ==== (2) loads ====

def Laws.read_lines(g, mc, r, ch, c, lane, e, l32, e4):
  +L8 = Nat.div(lane, 8n)
  +M8 = Nat.mod(lane, 8n)
  +G = Nat.mul(g, mc)
  +S = Impl.slot()
  +a = Nat.mul(G, S)
  +b = Nat.mul(c, S)
  +cc = Nat.mul(r, Impl.gw())
  +d = Nat.mul(ch, 128n)
  +f = Nat.mul(L8, 32n)
  +gg = Nat.mul(M8, 4n)
  +p1 = dc_btr(Nat.is_lt(L8, 4n), Nat.is_lt(lane, Nat.mul(4n, 8n)), True{}, Ar.ar_div_lt(4n, lane, 8n, {==}), l32)
  # lane * 4 == L8 * 32 + M8 * 4
  +ln = dc_sym(Nat.add(Nat.mul(L8, 8n), M8), lane, Ar.ard_dm_eq(lane, 8n, {==}))
  +l4 = dc_tr(Nat.mul(lane, 4n), Nat.mul(Nat.add(Nat.mul(L8, 8n), M8), 4n), Nat.add(f, gg),
    dc_mul_l(lane, Nat.add(Nat.mul(L8, 8n), M8), 4n, ln),
    dc_tr(Nat.mul(Nat.add(Nat.mul(L8, 8n), M8), 4n), Nat.add(Nat.mul(Nat.mul(L8, 8n), 4n), gg), Nat.add(f, gg),
      Ar.ar_mul_add_l(Nat.mul(L8, 8n), M8, 4n),
      dc_add_l(Nat.mul(Nat.mul(L8, 8n), 4n), f, gg, Ar.ar_mul_assoc(L8, 8n, 4n))))
  +X0 = Nat.add(Nat.add(Nat.add(a, cc), d), Nat.add(b, Nat.add(Nat.mul(lane, 4n), e)))
  +X1 = Nat.add(Nat.add(Nat.add(a, cc), d), Nat.add(b, Nat.add(Nat.add(f, gg), e)))
  +x01 = dc_add_r(Nat.add(Nat.add(a, cc), d), Nat.add(b, Nat.add(Nat.mul(lane, 4n), e)), Nat.add(b, Nat.add(Nat.add(f, gg), e)),
    dc_add_r(b, Nat.add(Nat.mul(lane, 4n), e), Nat.add(Nat.add(f, gg), e), dc_add_l(Nat.mul(lane, 4n), Nat.add(f, gg), e, l4)))
  +X2 = Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(a, b), cc), d), f), Nat.add(gg, e))
  +J = Spec.jline(Nat.add(G, c), r, ch, L8)
  +J32 = Nat.add(Nat.add(Nat.add(Nat.mul(Nat.add(G, c), S), cc), d), f)
  +x23 = dc_add_l(Nat.add(Nat.add(Nat.add(Nat.add(a, b), cc), d), f), J32, Nat.add(gg, e),
    dc_sym(J32, Nat.add(Nat.add(Nat.add(Nat.add(a, b), cc), d), f), dc_split3(G, c, cc, d, f)))
  +x34 = dc_add_l(J32, Nat.mul(J, 32n), Nat.add(gg, e), dc_sym(Nat.mul(J, 32n), J32, dc_lj(Nat.add(G, c), r, ch, L8)))
  +eqL = dc_tr(X0, X1, Nat.add(Nat.mul(J, 32n), Nat.add(gg, e)), x01,
    dc_tr(X1, X2, Nat.add(Nat.mul(J, 32n), Nat.add(gg, e)), dc_perm_b(a, b, cc, d, f, gg, e),
      dc_tr(X2, Nat.add(J32, Nat.add(gg, e)), Nat.add(Nat.mul(J, 32n), Nat.add(gg, e)), x23, x34)))
  +m8 = Ar.ard_dm_lt(lane, 8n, {==})
  +rem = dc_lt_block(M8, e, 4n, 8n, e4, m8)
  +dv = dc_du_div(J, Nat.add(gg, e), 32n, rem)
  +p2 = dc_tr(Nat.div(X0, 32n), Nat.div(Nat.add(Nat.mul(J, 32n), Nat.add(gg, e)), 32n), J,
    Equal.cong(Nat, Nat, z => Nat.div(z, 32n), X0, Nat.add(Nat.mul(J, 32n), Nat.add(gg, e)), eqL), dv)
  (p1, p2)

# ==== (3) disjointness ====

def Laws.jline_injective(s1, r1, ch1, q1, s2, r2, ch2, q2, rr1, rr2, cc1, cc2, qq1, qq2, same):
  +Y1 = Nat.add(Nat.mul(Nat.add(Nat.mul(s1, 16n), r1), 4n), ch1)
  +Y2 = Nat.add(Nat.mul(Nat.add(Nat.mul(s2, 16n), r2), 4n), ch2)
  +Z1 = Nat.add(Nat.mul(s1, 16n), r1)
  +Z2 = Nat.add(Nat.mul(s2, 16n), r2)
  +sm = same
  +a1 = qq1
  +a2 = qq2
  +b1 = cc1
  +b2 = cc2
  +d1 = rr1
  +d2 = rr2
  +ye = dc_dmi_q(Y1, q1, Y2, q2, 4n, a1, a2, sm)
  +qe = dc_dmi_r(Y1, q1, Y2, q2, 4n, a1, a2, sm)
  +ze = dc_dmi_q(Z1, ch1, Z2, ch2, 4n, b1, b2, ye)
  +ce = dc_dmi_r(Z1, ch1, Z2, ch2, 4n, b1, b2, ye)
  (dc_dmi_q(s1, r1, s2, r2, 16n, d1, d2, ze), dc_dmi_r(s1, r1, s2, r2, 16n, d1, d2, ze), ce, qe)

def Laws.slot_of_injective(g1, c1, g2, c2, mc, cm1, cm2, same):
  Ar.ar_divmod_inj(g1, c1, g2, c2, mc, cm1, cm2, same)

def Laws.region_bound(g, c, G, mc, gG, cm):
  dc_lt_block(g, c, mc, G, cm, gG)

def Laws.region_apart(x, A, y, xa):
  Ar.ar_eq_false(x, Nat.add(A, y), eq =>
    +h = dc_btr(Nat.is_lt(Nat.add(A, y), A), Nat.is_lt(x, A), True{},
      Equal.cong(Nat, Bool, z => Nat.is_lt(z, A), Nat.add(A, y), x, dc_sym(x, Nat.add(A, y), eq)), xa)
    +f = dc_btr(Nat.is_lt(Nat.add(A, y), A), Bool.not(Nat.is_le(A, Nat.add(A, y))), False{}, Ar.ar_lt_not_le(Nat.add(A, y), A),
      Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_le(A, Nat.add(A, y)), True{}, Ar.ar_le_add_r(A, y)))
    Ar.ar_false_true(dc_btr(False{}, Nat.is_lt(Nat.add(A, y), A), True{}, dc_bsym(Nat.is_lt(Nat.add(A, y), A), False{}, f), h)))

# ==== (4) stores ====

def Laws.slot_base_forms(g, mc, c):
  dc_sym(Impl.slot_base(g, mc, c), Impl.slot_base_mlp(g, mc, c), Ar.ar_mul_add_l(Nat.mul(g, mc), c, Impl.slot()))

def Laws.cells_written(g, mc, c, r, col, MT, colw, rows):
  +s = Nat.add(Nat.mul(g, mc), c)
  +B = Impl.slot_base(g, mc, c)
  +row = Part.row(Nat.div(r, 8n), Nat.div(Nat.mod(r, 8n), 2n), Nat.mod(r, 2n))
  +cl = Part.col(Nat.div(col, 64n), Nat.div(Nat.mod(col, 64n), 16n), Nat.div(Nat.mod(col, 16n), 8n), Nat.mod(col, 8n))
  +RG = Nat.add(Nat.mul(s, Impl.slot()), Nat.mul(r, Impl.gw()))
  +w1 = dc_add_l(Nat.add(B, Nat.mul(row, Impl.gw())), RG, cl,
    dc_add_r(B, Nat.mul(row, Impl.gw()), Nat.mul(r, Impl.gw()), dc_mul_l(row, r, Impl.gw(), Ar.p7_rows_cover1(r))))
  +w2 = dc_add_r(RG, cl, col, Ar.p7_cover_col(col))
  +cz = dc_add_l(Nat.mul(Nat.add(Nat.mul(s, 16n), r), Impl.gw()), RG, col, dc_lz(s, r))
  +p0 = dc_tr(Impl.write_addr(g, mc, c, Nat.div(col, 64n), Nat.div(Nat.mod(col, 64n), 16n), Nat.div(Nat.mod(col, 16n), 8n),
      Nat.mod(col, 8n), Nat.div(r, 8n), Nat.div(Nat.mod(r, 8n), 2n), Nat.mod(r, 2n)),
    Nat.add(RG, cl), Spec.cell(s, r, col), w1,
    dc_tr(Nat.add(RG, cl), Nat.add(RG, col), Spec.cell(s, r, col), w2, dc_sym(Spec.cell(s, r, col), Nat.add(RG, col), cz)))
  +bw = dc_btr(Nat.is_lt(Nat.div(col, 64n), 8n), Nat.is_lt(col, Nat.mul(8n, 64n)), True{}, Ar.ar_div_lt(8n, col, 64n, {==}), colw)
  +bt = dc_btr(Nat.is_lt(Nat.div(Nat.mod(col, 64n), 16n), 4n), Nat.is_lt(Nat.mod(col, 64n), Nat.mul(4n, 16n)), True{},
    Ar.ar_div_lt(4n, Nat.mod(col, 64n), 16n, {==}), Ar.ard_dm_lt(col, 64n, {==}))
  +bh = dc_btr(Nat.is_lt(Nat.div(Nat.mod(col, 16n), 8n), 2n), Nat.is_lt(Nat.mod(col, 16n), Nat.mul(2n, 8n)), True{},
    Ar.ar_div_lt(2n, Nat.mod(col, 16n), 8n, {==}), Ar.ard_dm_lt(col, 16n, {==}))
  +bq = Ar.ard_dm_lt(col, 8n, {==})
  +bm = dc_btr(Nat.is_lt(Nat.div(r, 8n), MT), Nat.is_lt(r, Nat.mul(MT, 8n)), True{}, Ar.ar_div_lt(MT, r, 8n, {==}), rows)
  +ba = dc_btr(Nat.is_lt(Nat.div(Nat.mod(r, 8n), 2n), 4n), Nat.is_lt(Nat.mod(r, 8n), Nat.mul(4n, 2n)), True{},
    Ar.ar_div_lt(4n, Nat.mod(r, 8n), 2n, {==}), Ar.ard_dm_lt(r, 8n, {==}))
  +bc = Ar.ard_dm_lt(r, 2n, {==})
  (p0, bw, bt, bh, bq, bm, ba, bc)

def Laws.line_cells(s, r, ch, q, j, c4, q4, j32):
  +X = Nat.add(Nat.mul(s, Impl.slot()), Nat.mul(r, Impl.gw()))
  +c = Nat.mul(ch, 128n)
  +u = Nat.mul(q, 32n)
  +col = Nat.add(Nat.add(c, u), j)
  +T = Nat.add(X, Nat.add(c, Nat.add(u, j)))
  +left = dc_tr(Nat.add(Nat.mul(Spec.jline(s, r, ch, q), 32n), j), Nat.add(Nat.add(Nat.add(X, c), u), j), T,
    dc_add_l(Nat.mul(Spec.jline(s, r, ch, q), 32n), Nat.add(Nat.add(X, c), u), j, dc_lj(s, r, ch, q)),
    dc_tr(Nat.add(Nat.add(Nat.add(X, c), u), j), Nat.add(Nat.add(X, c), Nat.add(u, j)), T,
      Ar.ar_add_assoc(Nat.add(X, c), u, j), Ar.ar_add_assoc(X, c, Nat.add(u, j))))
  +right = dc_tr(Spec.cell(s, r, col), Nat.add(X, col), T,
    dc_add_l(Nat.mul(Nat.add(Nat.mul(s, 16n), r), Impl.gw()), X, col, dc_lz(s, r)),
    dc_add_r(X, col, Nat.add(c, Nat.add(u, j)), Ar.ar_add_assoc(c, u, j)))
  +p1 = dc_tr(Nat.add(Nat.mul(Spec.jline(s, r, ch, q), 32n), j), T, Spec.cell(s, r, col), left, dc_sym(Spec.cell(s, r, col), T, right))
  +in1 = dc_lt_block(q, j, 32n, 4n, j32, q4)
  +in2 = dc_lt_block(ch, Nat.add(u, j), 128n, 4n, in1, c4)
  +p2 = dc_btr(Nat.is_lt(col, 512n), Nat.is_lt(Nat.add(c, Nat.add(u, j)), 512n), True{},
    Equal.cong(Nat, Bool, z => Nat.is_lt(z, 512n), col, Nat.add(c, Nat.add(u, j)), Ar.ar_add_assoc(c, u, j)), in2)
  (p1, p2)

# ==== (5) order and observed values ====

def Laws.reads_before_discard():
  ({==}, {==}, {==})

def dc_ev_at(+on: Bool, +zero: Bool, +n: Nat, +k: Nat, +k8: {Nat.is_lt(k, 8n) == True{} : Bool})
  -> {Impl.ev_at(on, zero, Nat.add(Nat.mul(n, 8n), k)) == Impl.ev_step(on, zero, n, k) : Impl.Ev}:
  %dc_du_div(n, k, 8n, k8) : {Impl.ev_at(on, zero, Nat.add(Nat.mul(n, 8n), k)) == Impl.ev_step(on, zero, _, k) : Impl.Ev}
  %dc_du_mod(n, k, 8n, k8) : {Impl.ev_at(on, zero, Nat.add(Nat.mul(n, 8n), k)) ==
    Impl.ev_step(on, zero, Nat.div(Nat.add(Nat.mul(n, 8n), k), 8n), _) : Impl.Ev}
  {==}

def dc_last_step(+on: Bool, +zero: Bool, +n: Nat, +k: Nat, k8: {Nat.is_lt(k, 8n) == True{} : Bool})
  -> {Impl.keep(Impl.ev_step(on, zero, n, k), Impl.last(on, zero, Nat.add(Nat.mul(n, 8n), k))) ==
      Impl.last(on, zero, Nat.add(Nat.mul(n, 8n), 1n+k)) : Impl.Ev}:
  %dc_sym(Nat.add(Nat.mul(n, 8n), 1n+k), 1n+Nat.add(Nat.mul(n, 8n), k), Ar.ar_add_succ_r(Nat.mul(n, 8n), k)) :
    {Impl.keep(Impl.ev_step(on, zero, n, k), Impl.last(on, zero, Nat.add(Nat.mul(n, 8n), k))) == Impl.last(on, zero, _) : Impl.Ev}
  %dc_ev_at(on, zero, n, k, k8) :
    {Impl.keep(_, Impl.last(on, zero, Nat.add(Nat.mul(n, 8n), k))) == Impl.last(on, zero, 1n+Nat.add(Nat.mul(n, 8n), k)) : Impl.Ev}
  {==}

def dc_adj3(zero: Bool, +n: Nat) -> {Impl.keep(Impl.sum0_if(zero, n), Impl.Wr{n}) == Spec.want_pick(False{}, zero, n) : Impl.Ev}:
  match zero:
    case True{}:
      {==}
    case False{}:
      {==}

def dc_adj(+on: Bool, +zero: Bool, +n: Nat, +k: Nat, k6: {Nat.is_lt(k, 6n) == True{} : Bool})
  -> {Impl.keep(Impl.ev_step(on, zero, n, 1n+k), Spec.want(zero, n, 1n+k)) == Spec.want(zero, n, 1n+1n+k) : Impl.Ev}:
  match k:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              dc_adj3(zero, n)
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  match d:
                    case 0n:
                      {==}
                    case 1n+e:
                      match e:
                        case 0n:
                          {==}
                        case 1n+x:
                          Empty.absurd({Impl.keep(Impl.ev_step(on, zero, n, 1n+1n+1n+1n+1n+1n+1n+x),
                              Spec.want(zero, n, 1n+1n+1n+1n+1n+1n+1n+x)) ==
                              Spec.want(zero, n, 1n+1n+1n+1n+1n+1n+1n+1n+x) : Impl.Ev},
                            Ar.ar_false_true(dc_btr(False{}, Nat.is_lt(x, 0n), True{},
                              dc_bsym(Nat.is_lt(x, 0n), False{}, Ar.ar_h_lt_zero(x)), k6)))

def dc_ls(+on: Bool, +zero: Bool, +n: Nat, +k: Nat, lt: {Nat.is_lt(k, 7n) == True{} : Bool})
  -> {Impl.last(on, zero, Nat.add(Nat.mul(n, 8n), 1n+k)) == Spec.want(zero, n, 1n+k) : Impl.Ev}:
  match k:
    case 0n:
      %dc_last_step(on, zero, n, 0n, {==}) : {_ == Spec.want(zero, n, 1n) : Impl.Ev}
      {==}
    case 1n+p:
      +lt6 = lt
      +ih = dc_ls(on, zero, n, p, Ar.ar_lt_trans(p, 6n, 7n, lt6, {==}))
      +step = dc_last_step(on, zero, n, 1n+p, Ar.ar_lt_trans(1n+p, 7n, 8n, lt6, {==}))
      +LAST = Impl.last(on, zero, Nat.add(Nat.mul(n, 8n), 1n+p))
      +EV = Impl.ev_step(on, zero, n, 1n+p)
      Equal.trans(Impl.Ev, Impl.last(on, zero, Nat.add(Nat.mul(n, 8n), 1n+1n+p)), Impl.keep(EV, LAST),
        Spec.want(zero, n, 1n+1n+p),
        Equal.sym(Impl.Ev, Impl.keep(EV, LAST), Impl.last(on, zero, Nat.add(Nat.mul(n, 8n), 1n+1n+p)), step),
        Equal.trans(Impl.Ev, Impl.keep(EV, LAST), Impl.keep(EV, Spec.want(zero, n, 1n+p)), Spec.want(zero, n, 1n+1n+p),
          Equal.cong(Impl.Ev, Impl.Ev, x => Impl.keep(EV, x), LAST, Spec.want(zero, n, 1n+p), ih),
          dc_adj(on, zero, n, p, lt6)))

def Laws.load_sees_launch(on, zero, n, k, k7):
  dc_ls(on, zero, n, k, k7)

# ==== (6) the switch ====

def Laws.discard_knob(c1):
  ({==}, {==}, {==}, {==}, {==}, {==}, {==})

def dc_kr_pick(b3: Bool, +v: Nat, vle: {Nat.is_le(v, 1n) == True{} : Bool})
  -> {Spec.knob_ok(Impl.pick_knob(b3, v)) == True{} : Bool}:
  match b3:
    case True{}:
      vle
    case False{}:
      {==}

def dc_kr(b1: Bool, b2: Bool, b3: Bool, +x: Nat, e1: {Nat.is_eq(x, 48n) == b1 : Bool}, e2: {Nat.is_eq(x, 49n) == b2 : Bool})
  -> {Spec.knob_ok(Impl.pick_knob(Bool.and(Bool.or(b1, b2), b3), Nat.sub(x, 48n))) == True{} : Bool}:
  match b1:
    case True{}:
      %dc_sym(x, 48n, Ar.ar_eq_true(x, 48n, e1)) :
        {Spec.knob_ok(Impl.pick_knob(Bool.and(Bool.or(True{}, b2), b3), Nat.sub(_, 48n))) == True{} : Bool}
      dc_kr_pick(b3, 0n, {==})
    case False{}:
      match b2:
        case True{}:
          %dc_sym(x, 49n, Ar.ar_eq_true(x, 49n, e2)) :
            {Spec.knob_ok(Impl.pick_knob(Bool.and(Bool.or(False{}, True{}), b3), Nat.sub(_, 48n))) == True{} : Bool}
          dc_kr_pick(b3, 1n, {==})
        case False{}:
          {==}

def Laws.discard_knob_range(c0, c1):
  match c0:
    case 0n:
      {==}
    case 1n+p:
      dc_kr(Nat.is_eq(1n+p, 48n), Nat.is_eq(1n+p, 49n), Nat.is_eq(c1, 0n), 1n+p, {==}, {==})

def dc_setle(+m: Nat, v: Nat) -> {Nat.is_le(Impl.set_mode(m, Impl.Set{v}), 1n) == True{} : Bool}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Laws.discard_mode(m, v):
  (dc_setle(m, v), {==}, {==}, {==})
