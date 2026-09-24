# WIP proofs (part 2): contributors_contiguous, slot_in_range, slot_injective.
# Merged into gemm_m16_partition_proof.bend (imports, STUB blocks and `Arith.` prefixes
# stripped). Every local def is prefixed p2_.
import Base
import ./gemm_m16_partition.bend as Impl
import ./gemm_m16_partition_spec.bend as Spec
import ./gemm_m16_partition_laws.bend as Laws
import ./gemm_m16_partition_wip_arith.bend as Arith

# STUB-BEGIN (proven in wip_p1)
def p1_owner_le(+x: Nat, +b: Nat, +I: Nat, +G: Nat,
    ipos: {Nat.is_lt(0n, I) == True{} : Bool},
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_le(Impl.owner(x, I, G), b) == Nat.is_lt(x, Impl.start(1n+b, I, G)) : Bool}:
  ?TODO

def p1_le_owner(+b: Nat, +y: Nat, +I: Nat, +G: Nat,
    ipos: {Nat.is_lt(0n, I) == True{} : Bool},
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_le(b, Impl.owner(y, I, G)) == Nat.is_le(Impl.start(b, I, G), y) : Bool}:
  ?TODO

def p1_owner_lt(+x: Nat, +I: Nat, +G: Nat,
    gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    inside: {Nat.is_lt(x, I) == True{} : Bool})
  -> {Nat.is_lt(Impl.owner(x, I, G), G) == True{} : Bool}:
  ?TODO

def p1_touches_range(+b: Nat, +g: Nat, +KT: Nat, +I: Nat, +G: Nat,
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Spec.touches(b, g, KT, I, G) ==
    Bool.and(Nat.is_lt(Impl.start(b, I, G), Impl.start(1n+b, I, G)),
      Bool.and(Nat.is_lt(Impl.start(b, I, G), Nat.mul(1n+g, KT)),
        Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+b, I, G)))) : Bool}:
  ?TODO
# STUB-END

# ---- Bool helpers ----

# Transport truth forwards / backwards along a Bool equation.
def p2_rt(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {a == True{} : Bool})
  -> {b == True{} : Bool}:
  Equal.trans(Bool, b, a, True{}, Equal.sym(Bool, a, b, e), h)

def p2_tr(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {b == True{} : Bool})
  -> {a == True{} : Bool}:
  Equal.trans(Bool, a, b, True{}, e, h)

def p2_and_true_l(a: Bool, -b: Bool, h: {a == True{} : Bool})
  -> {Bool.and(a, b) == b : Bool}:
  match a:
    case False{}:
      Empty.absurd({False{} == b : Bool}, Arith.ar_false_true(h))
    case True{}:
      {==}

def p2_and_comm(a: Bool, b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def p2_not_false(x: Bool, h: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Arith.ar_true_false(h))

# ---- Nat helpers ----

def p2_lt_succ(a: Nat) -> {Nat.is_lt(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      p2_lt_succ(p)

# KT = k / 16 >= 8 > 0 for k >= 128.
def p2_kt_pos(+k: Nat, shaped: {Nat.is_le(128n, k) == True{} : Bool})
  -> {Nat.is_lt(0n, Impl.kt(k)) == True{} : Bool}:
  Arith.ar_lt_le_trans(0n, 8n, Impl.kt(k), {==},
    p2_rt(Nat.is_le(Nat.mul(8n, 16n), k), Nat.is_le(8n, Nat.div(k, 16n)),
      Arith.ar_div_le(8n, k, 16n, {==}), shaped))

def p2_m_pos(+g: Nat, +KT: Nat, kpos: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> {Nat.is_le(1n, Nat.mul(1n+g, KT)) == True{} : Bool}:
  Arith.ar_le_trans(1n, KT, Nat.mul(1n+g, KT),
    p2_rt(Nat.is_lt(0n, KT), Nat.is_le(1n, KT), Arith.ar_lt_succ_le(0n, KT), kpos),
    Arith.ar_le_add_r(KT, Nat.mul(g, KT)))

# g < Gr gives (g + 1) * m <= Gr * m.
def p2_m_le(+g: Nat, +Gr: Nat, +KT: Nat, group: {Nat.is_lt(g, Gr) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(1n+g, KT), Nat.mul(Gr, KT)) == True{} : Bool}:
  Arith.ar_le_mul_mono(1n+g, Gr, KT,
    p2_rt(Nat.is_lt(g, Gr), Nat.is_le(1n+g, Gr), Arith.ar_lt_succ_le(g, Gr), group))

# s <= m - 1 iff s < m, for m >= 1.
def p2_le_pred(+s: Nat, +m: Nat, pos: {Nat.is_le(1n, m) == True{} : Bool})
  -> {Nat.is_le(s, Nat.sub(m, 1n)) == Nat.is_lt(s, m) : Bool}:
  %Arith.ar_sub_add(m, 1n, pos) : {Nat.is_le(s, Nat.sub(m, 1n)) == Nat.is_lt(s, _) : Bool}
  Equal.sym(Bool, Nat.is_lt(s, 1n+Nat.sub(m, 1n)), Nat.is_le(1n+s, 1n+Nat.sub(m, 1n)),
    Arith.ar_lt_succ_le(s, 1n+Nat.sub(m, 1n)))

def p2_gk_lt_m(+g: Nat, +KT: Nat, kpos: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> {Nat.is_lt(Nat.mul(g, KT), Nat.mul(1n+g, KT)) == True{} : Bool}:
  p2_tr(Nat.is_lt(Nat.mul(g, KT), Nat.mul(1n+g, KT)), Nat.is_lt(g, 1n+g),
    Arith.ar_mul_lt_cancel(g, 1n+g, KT, kpos), p2_lt_succ(g))

def p2_gk_le_xhi(+g: Nat, +KT: Nat, +kpos: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> {Nat.is_le(Nat.mul(g, KT), Nat.sub(Nat.mul(1n+g, KT), 1n)) == True{} : Bool}:
  p2_tr(Nat.is_le(Nat.mul(g, KT), Nat.sub(Nat.mul(1n+g, KT), 1n)),
    Nat.is_lt(Nat.mul(g, KT), Nat.mul(1n+g, KT)),
    p2_le_pred(Nat.mul(g, KT), Nat.mul(1n+g, KT), p2_m_pos(g, KT, kpos)),
    p2_gk_lt_m(g, KT, kpos))

# (g + 1) * KT - 1 < I when (g + 1) * KT <= I.
def p2_xhi_lt(+g: Nat, +KT: Nat, +I: Nat, kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    mle: {Nat.is_le(Nat.mul(1n+g, KT), I) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(Nat.mul(1n+g, KT), 1n), I) == True{} : Bool}:
  Arith.ar_lt_le_trans(Nat.sub(Nat.mul(1n+g, KT), 1n), Nat.mul(1n+g, KT), I,
    p2_tr(Nat.is_lt(Nat.sub(Nat.mul(1n+g, KT), 1n), Nat.mul(1n+g, KT)),
      Nat.is_le(Nat.sub(Nat.mul(1n+g, KT), 1n), Nat.sub(Nat.mul(1n+g, KT), 1n)),
      Equal.sym(Bool,
        Nat.is_le(Nat.sub(Nat.mul(1n+g, KT), 1n), Nat.sub(Nat.mul(1n+g, KT), 1n)),
        Nat.is_lt(Nat.sub(Nat.mul(1n+g, KT), 1n), Nat.mul(1n+g, KT)),
        p2_le_pred(Nat.sub(Nat.mul(1n+g, KT), 1n), Nat.mul(1n+g, KT), p2_m_pos(g, KT, kpos))),
      Arith.ar_le_refl(Nat.sub(Nat.mul(1n+g, KT), 1n))),
    mle)

# b * I + G <= (b + 1) * I when G <= I.
def p2_ne_step(+b: Nat, +I: Nat, +G: Nat, fits: {Nat.is_le(G, I) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Nat.mul(b, I), G), Nat.mul(1n+b, I)) == True{} : Bool}:
  %Arith.ar_add_comm(Nat.mul(b, I), I) : {Nat.is_le(Nat.add(Nat.mul(b, I), G), _) == True{} : Bool}
  p2_rt(Nat.is_le(G, I), Nat.is_le(Nat.add(Nat.mul(b, I), G), Nat.add(Nat.mul(b, I), I)),
    Equal.sym(Bool, Nat.is_le(Nat.add(Nat.mul(b, I), G), Nat.add(Nat.mul(b, I), I)),
      Nat.is_le(G, I), Arith.ar_le_add_cancel(Nat.mul(b, I), G, I)),
    fits)

# Under G <= I every block range is non-empty: start(b) < start(b + 1).
def p2_nonempty(+b: Nat, +I: Nat, +G: Nat, +gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    fits: {Nat.is_le(G, I) == True{} : Bool})
  -> {Nat.is_lt(Impl.start(b, I, G), Impl.start(1n+b, I, G)) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(Impl.start(b, I, G), Impl.start(1n+b, I, G)), Nat.is_le(1n+Impl.start(b, I, G), Impl.start(1n+b, I, G)), Arith.ar_lt_succ_le(Impl.start(b, I, G), Impl.start(1n+b, I, G))) : {_ == True{} : Bool}
  %Arith.ar_div_add_self(Nat.mul(b, I), G, gpos) : {Nat.is_le(_, Impl.start(1n+b, I, G)) == True{} : Bool}
  Arith.ar_div_mono(Nat.add(Nat.mul(b, I), G), Nat.mul(1n+b, I), G, gpos,
    p2_ne_step(b, I, G, fits))

# ---- contributors_contiguous, generic in KT, I, G ----

def p2_contig1(+b: Nat, +g: Nat, +KT: Nat, +I: Nat, +G: Nat,
    +gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    +fits: {Nat.is_le(G, I) == True{} : Bool},
    kpos: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> {Spec.touches(b, g, KT, I, G) ==
    Bool.and(Nat.is_le(Impl.owner(Nat.mul(g, KT), I, G), b),
      Nat.is_le(b, Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G))) : Bool}:
  +ipos = Arith.ar_lt_le_trans(0n, G, I, gpos, fits)
  %Equal.sym(Bool, Nat.is_le(Impl.owner(Nat.mul(g, KT), I, G), b), Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+b, I, G)), p1_owner_le(Nat.mul(g, KT), b, I, G, ipos, gpos)) : {Spec.touches(b, g, KT, I, G) == Bool.and(_, Nat.is_le(b, Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G))) : Bool}
  %Equal.trans(Bool, Nat.is_lt(Impl.start(b, I, G), Nat.mul(1n+g, KT)), Nat.is_le(Impl.start(b, I, G), Nat.sub(Nat.mul(1n+g, KT), 1n)), Nat.is_le(b, Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G)), Equal.sym(Bool, Nat.is_le(Impl.start(b, I, G), Nat.sub(Nat.mul(1n+g, KT), 1n)), Nat.is_lt(Impl.start(b, I, G), Nat.mul(1n+g, KT)), p2_le_pred(Impl.start(b, I, G), Nat.mul(1n+g, KT), p2_m_pos(g, KT, kpos))), Equal.sym(Bool, Nat.is_le(b, Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G)), Nat.is_le(Impl.start(b, I, G), Nat.sub(Nat.mul(1n+g, KT), 1n)), p1_le_owner(b, Nat.sub(Nat.mul(1n+g, KT), 1n), I, G, ipos, gpos))) : {Spec.touches(b, g, KT, I, G) == Bool.and(Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+b, I, G)), _) : Bool}
  %p2_and_comm(Nat.is_lt(Impl.start(b, I, G), Nat.mul(1n+g, KT)), Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+b, I, G))) : {Spec.touches(b, g, KT, I, G) == _ : Bool}
  Equal.trans(Bool, Spec.touches(b, g, KT, I, G),
    Bool.and(Nat.is_lt(Impl.start(b, I, G), Impl.start(1n+b, I, G)),
      Bool.and(Nat.is_lt(Impl.start(b, I, G), Nat.mul(1n+g, KT)),
        Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+b, I, G)))),
    Bool.and(Nat.is_lt(Impl.start(b, I, G), Nat.mul(1n+g, KT)),
      Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+b, I, G))),
    p1_touches_range(b, g, KT, I, G, gpos),
    p2_and_true_l(Nat.is_lt(Impl.start(b, I, G), Impl.start(1n+b, I, G)),
      Bool.and(Nat.is_lt(Impl.start(b, I, G), Nat.mul(1n+g, KT)),
        Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+b, I, G))),
      p2_nonempty(b, I, G, gpos, fits)))

def p2_lo_le_hi(+g: Nat, +KT: Nat, +I: Nat, +G: Nat,
    +gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    fits: {Nat.is_le(G, I) == True{} : Bool},
    kpos: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> {Nat.is_le(Impl.owner(Nat.mul(g, KT), I, G),
    Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G)) == True{} : Bool}:
  +ipos = Arith.ar_lt_le_trans(0n, G, I, gpos, fits)
  p2_rt(Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G), I, G)),
    Nat.is_le(Impl.owner(Nat.mul(g, KT), I, G), Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G)),
    Equal.sym(Bool,
      Nat.is_le(Impl.owner(Nat.mul(g, KT), I, G), Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G)),
      Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G), I, G)),
      p1_owner_le(Nat.mul(g, KT), Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G), I, G, ipos, gpos)),
    Arith.ar_le_lt_trans(Nat.mul(g, KT), Nat.sub(Nat.mul(1n+g, KT), 1n),
      Impl.start(1n+Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G), I, G),
      p2_gk_le_xhi(g, KT, kpos),
      p2_rt(Nat.is_le(Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G), Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G)),
        Nat.is_lt(Nat.sub(Nat.mul(1n+g, KT), 1n), Impl.start(1n+Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G), I, G)),
        p1_owner_le(Nat.sub(Nat.mul(1n+g, KT), 1n), Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G), I, G, ipos, gpos),
        Arith.ar_le_refl(Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G)))))

def p2_hi_lt(+g: Nat, +KT: Nat, +I: Nat, +G: Nat,
    gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    mle: {Nat.is_le(Nat.mul(1n+g, KT), I) == True{} : Bool})
  -> {Nat.is_lt(Impl.owner(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G), G) == True{} : Bool}:
  p1_owner_lt(Nat.sub(Nat.mul(1n+g, KT), 1n), I, G, gpos, p2_xhi_lt(g, KT, I, kpos, mle))

def Laws.contributors_contiguous(mats, n, k, G, g, b, grid, shaped, fits, group):
  +gp = grid
  +fp = fits
  +kp = p2_kt_pos(k, shaped)
  (p2_contig1(b, g, Impl.kt(k), Impl.total(mats, n, k), G, gp, fp, kp),
    (p2_lo_le_hi(g, Impl.kt(k), Impl.total(mats, n, k), G, gp, fp, kp),
      p2_hi_lt(g, Impl.kt(k), Impl.total(mats, n, k), G, gp, kp,
        p2_m_le(g, Impl.groups(mats, n), Impl.kt(k), group))))
