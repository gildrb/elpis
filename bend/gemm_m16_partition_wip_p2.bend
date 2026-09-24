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

# ---- slot_in_range / slot_injective, generic in KT, I, G ----

# x <= y gives x < y + 1.
def p2_lt_add1(+x: Nat, +y: Nat, h: {Nat.is_le(x, y) == True{} : Bool})
  -> {Nat.is_lt(x, Nat.add(y, 1n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(y, 1n), Nat.add(1n, y), Arith.ar_add_comm(y, 1n)) : {Nat.is_lt(x, _) == True{} : Bool}
  p2_tr(Nat.is_lt(x, 1n+y), Nat.is_le(1n+x, 1n+y), Arith.ar_lt_succ_le(x, 1n+y), h)

def p2_le_hi(+b: Nat, +lo: Nat, +hi: Nat, lohi: {Nat.is_le(lo, hi) == True{} : Bool},
    bhi: {Nat.is_le(b, hi) == True{} : Bool})
  -> {Nat.is_le(b, Nat.add(lo, Nat.sub(hi, lo))) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(lo, Nat.sub(hi, lo)), hi, Arith.ar_sub_add(hi, lo, lohi)) : {Nat.is_le(b, _) == True{} : Bool}
  bhi

# lo <= b <= hi gives b - lo <= hi - lo.
def p2_off_le(+b: Nat, +lo: Nat, +hi: Nat, lob: {Nat.is_le(lo, b) == True{} : Bool},
    +bhi: {Nat.is_le(b, hi) == True{} : Bool})
  -> {Nat.is_le(Nat.sub(b, lo), Nat.sub(hi, lo)) == True{} : Bool}:
  p2_tr(Nat.is_le(Nat.sub(b, lo), Nat.sub(hi, lo)), Nat.is_le(b, Nat.add(lo, Nat.sub(hi, lo))),
    Arith.ar_le_sub_iff(b, lo, Nat.sub(hi, lo)),
    p2_le_hi(b, lo, hi, Arith.ar_le_trans(lo, b, hi, lob, bhi), bhi))

# A contributor's slot b - b_lo is below nc.
def p2_off_lt_nc(+b: Nat, +g: Nat, +KT: Nat, +I: Nat, +G: Nat,
    lob: {Nat.is_le(Impl.b_lo(g, KT, I, G), b) == True{} : Bool},
    bhi: {Nat.is_le(b, Impl.b_hi(g, KT, I, G)) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(b, Impl.b_lo(g, KT, I, G)), Impl.nc(g, KT, I, G)) == True{} : Bool}:
  p2_lt_add1(Nat.sub(b, Impl.b_lo(g, KT, I, G)), Nat.sub(Impl.b_hi(g, KT, I, G), Impl.b_lo(g, KT, I, G)),
    p2_off_le(b, Impl.b_lo(g, KT, I, G), Impl.b_hi(g, KT, I, G), lob, bhi))

# max_contrib.pick keeps the larger of n and mc.
def p2_pick_n_go(bigger: Bool, +n: Nat, +mc: Nat, e: {Nat.is_gt(n, mc) == bigger : Bool})
  -> {Nat.is_le(n, Impl.max_contrib.pick(bigger, n, mc)) == True{} : Bool}:
  match bigger:
    case True{}:
      Arith.ar_le_refl(n)
    case False{}:
      p2_not_false(Nat.is_le(n, mc),
        Equal.trans(Bool, Bool.not(Nat.is_le(n, mc)), Nat.is_gt(n, mc), False{},
          Equal.sym(Bool, Nat.is_gt(n, mc), Bool.not(Nat.is_le(n, mc)),
            Equal.trans(Bool, Nat.is_gt(n, mc), Nat.is_lt(mc, n), Bool.not(Nat.is_le(n, mc)),
              Arith.ar_gt_flip(n, mc), Arith.ar_lt_not_le(mc, n))),
          e))

def p2_pick_mc_go(bigger: Bool, +n: Nat, +mc: Nat, e: {Nat.is_gt(n, mc) == bigger : Bool})
  -> {Nat.is_le(mc, Impl.max_contrib.pick(bigger, n, mc)) == True{} : Bool}:
  match bigger:
    case True{}:
      Arith.ar_lt_le(mc, n,
        Equal.trans(Bool, Nat.is_lt(mc, n), Nat.is_gt(n, mc), True{},
          Equal.sym(Bool, Nat.is_gt(n, mc), Nat.is_lt(mc, n), Arith.ar_gt_flip(n, mc)), e))
    case False{}:
      Arith.ar_le_refl(mc)

# The running maximum never drops below its accumulator.
def p2_mc_go_mc(+left: Nat, +g0: Nat, +KT: Nat, +I: Nat, +G: Nat, +mc: Nat)
  -> {Nat.is_le(mc, Impl.max_contrib.go(left, g0, KT, I, G, mc)) == True{} : Bool}:
  match left:
    case 0n:
      Arith.ar_le_refl(mc)
    case 1n+rest:
      Arith.ar_le_trans(mc, Impl.max_contrib.pick(Nat.is_gt(Impl.nc(g0, KT, I, G), mc), Impl.nc(g0, KT, I, G), mc),
        Impl.max_contrib.go(rest, 1n+g0, KT, I, G, Impl.max_contrib.pick(Nat.is_gt(Impl.nc(g0, KT, I, G), mc), Impl.nc(g0, KT, I, G), mc)),
        p2_pick_mc_go(Nat.is_gt(Impl.nc(g0, KT, I, G), mc), Impl.nc(g0, KT, I, G), mc, {==}),
        p2_mc_go_mc(rest, 1n+g0, KT, I, G, Impl.max_contrib.pick(Nat.is_gt(Impl.nc(g0, KT, I, G), mc), Impl.nc(g0, KT, I, G), mc)))

# The running maximum over groups [g0, g0 + left) bounds nc(d + g0) for every d < left.
def p2_mc_go_nc(+d: Nat, +left: Nat, +g0: Nat, +KT: Nat, +I: Nat, +G: Nat, +mc: Nat,
    small: {Nat.is_lt(d, left) == True{} : Bool})
  -> {Nat.is_le(Impl.nc(Nat.add(d, g0), KT, I, G), Impl.max_contrib.go(left, g0, KT, I, G, mc))
    == True{} : Bool}:
  match d left:
    case 0n 0n:
      Empty.absurd({Nat.is_le(Impl.nc(g0, KT, I, G), mc) == True{} : Bool}, Arith.ar_false_true(small))
    case 1n+dp 0n:
      Empty.absurd({Nat.is_le(Impl.nc(1n+Nat.add(dp, g0), KT, I, G), mc) == True{} : Bool},
        Arith.ar_false_true(small))
    case 0n 1n+rest:
      Arith.ar_le_trans(Impl.nc(g0, KT, I, G), Impl.max_contrib.pick(Nat.is_gt(Impl.nc(g0, KT, I, G), mc), Impl.nc(g0, KT, I, G), mc),
        Impl.max_contrib.go(rest, 1n+g0, KT, I, G, Impl.max_contrib.pick(Nat.is_gt(Impl.nc(g0, KT, I, G), mc), Impl.nc(g0, KT, I, G), mc)),
        p2_pick_n_go(Nat.is_gt(Impl.nc(g0, KT, I, G), mc), Impl.nc(g0, KT, I, G), mc, {==}),
        p2_mc_go_mc(rest, 1n+g0, KT, I, G, Impl.max_contrib.pick(Nat.is_gt(Impl.nc(g0, KT, I, G), mc), Impl.nc(g0, KT, I, G), mc)))
    case 1n+dp 1n+rest:
      %Arith.ar_add_succ_r(dp, g0) : {Nat.is_le(Impl.nc(_, KT, I, G), Impl.max_contrib.go(rest, 1n+g0, KT, I, G, Impl.max_contrib.pick(Nat.is_gt(Impl.nc(g0, KT, I, G), mc), Impl.nc(g0, KT, I, G), mc))) == True{} : Bool}
      p2_mc_go_nc(dp, rest, 1n+g0, KT, I, G, Impl.max_contrib.pick(Nat.is_gt(Impl.nc(g0, KT, I, G), mc), Impl.nc(g0, KT, I, G), mc), small)

# nc(g) <= max_contrib for every group g < Gr.
def p2_nc_le_mc(+g: Nat, +Gr: Nat, +KT: Nat, +I: Nat, +G: Nat,
    group: {Nat.is_lt(g, Gr) == True{} : Bool})
  -> {Nat.is_le(Impl.nc(g, KT, I, G), Impl.max_contrib(Gr, KT, I, G)) == True{} : Bool}:
  %Arith.ar_add_zero_r(g) : {Nat.is_le(Impl.nc(_, KT, I, G), Impl.max_contrib(Gr, KT, I, G)) == True{} : Bool}
  p2_mc_go_nc(g, Gr, 0n, KT, I, G, 1n, group)

# g * mc + r < (g + 1) * mc when r < mc.
def p2_addr_step(+g: Nat, +mc: Nat, +r: Nat, rlt: {Nat.is_lt(r, mc) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(g, mc), r), Nat.mul(1n+g, mc)) == True{} : Bool}:
  %Arith.ar_add_comm(Nat.mul(g, mc), mc) : {Nat.is_lt(Nat.add(Nat.mul(g, mc), r), _) == True{} : Bool}
  p2_rt(Nat.is_lt(r, mc), Nat.is_lt(Nat.add(Nat.mul(g, mc), r), Nat.add(Nat.mul(g, mc), mc)),
    Equal.sym(Bool, Nat.is_lt(Nat.add(Nat.mul(g, mc), r), Nat.add(Nat.mul(g, mc), mc)),
      Nat.is_lt(r, mc), Arith.ar_lt_add_cancel(Nat.mul(g, mc), r, mc)),
    rlt)

def p2_addr_lt(+g: Nat, +Gr: Nat, +mc: Nat, +r: Nat, rlt: {Nat.is_lt(r, mc) == True{} : Bool},
    group: {Nat.is_lt(g, Gr) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(g, mc), r), Nat.mul(Gr, mc)) == True{} : Bool}:
  Arith.ar_lt_le_trans(Nat.add(Nat.mul(g, mc), r), Nat.mul(1n+g, mc), Nat.mul(Gr, mc),
    p2_addr_step(g, mc, r, rlt), p2_m_le(g, Gr, mc, group))

# A touching block lies in [b_lo(g), b_hi(g)].
def p2_touch_and(+b: Nat, +g: Nat, +KT: Nat, +I: Nat, +G: Nat,
    +gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    +fits: {Nat.is_le(G, I) == True{} : Bool},
    kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    touch: {Spec.touches(b, g, KT, I, G) == True{} : Bool})
  -> {Bool.and(Nat.is_le(Impl.b_lo(g, KT, I, G), b), Nat.is_le(b, Impl.b_hi(g, KT, I, G))) == True{} : Bool}:
  p2_rt(Spec.touches(b, g, KT, I, G),
    Bool.and(Nat.is_le(Impl.b_lo(g, KT, I, G), b), Nat.is_le(b, Impl.b_hi(g, KT, I, G))),
    p2_contig1(b, g, KT, I, G, gpos, fits, kpos), touch)

def p2_lo_le_b(+b: Nat, +g: Nat, +KT: Nat, +I: Nat, +G: Nat,
    +gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    +fits: {Nat.is_le(G, I) == True{} : Bool},
    kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    touch: {Spec.touches(b, g, KT, I, G) == True{} : Bool})
  -> {Nat.is_le(Impl.b_lo(g, KT, I, G), b) == True{} : Bool}:
  Arith.ar_and_l(Nat.is_le(Impl.b_lo(g, KT, I, G), b), Nat.is_le(b, Impl.b_hi(g, KT, I, G)),
    p2_touch_and(b, g, KT, I, G, gpos, fits, kpos, touch))

def p2_b_le_hi(+b: Nat, +g: Nat, +KT: Nat, +I: Nat, +G: Nat,
    +gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    +fits: {Nat.is_le(G, I) == True{} : Bool},
    kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    touch: {Spec.touches(b, g, KT, I, G) == True{} : Bool})
  -> {Nat.is_le(b, Impl.b_hi(g, KT, I, G)) == True{} : Bool}:
  Arith.ar_and_r(Nat.is_le(Impl.b_lo(g, KT, I, G), b), Nat.is_le(b, Impl.b_hi(g, KT, I, G)),
    p2_touch_and(b, g, KT, I, G, gpos, fits, kpos, touch))

# A contributor's slot b - b_lo(g) is below max_contrib.
def p2_off_lt_mc(+b: Nat, +g: Nat, +Gr: Nat, +KT: Nat, +I: Nat, +G: Nat,
    +gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    +fits: {Nat.is_le(G, I) == True{} : Bool},
    +kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    +touch: {Spec.touches(b, g, KT, I, G) == True{} : Bool},
    group: {Nat.is_lt(g, Gr) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(b, Impl.b_lo(g, KT, I, G)), Impl.max_contrib(Gr, KT, I, G)) == True{} : Bool}:
  Arith.ar_lt_le_trans(Nat.sub(b, Impl.b_lo(g, KT, I, G)), Impl.nc(g, KT, I, G), Impl.max_contrib(Gr, KT, I, G),
    p2_off_lt_nc(b, g, KT, I, G, p2_lo_le_b(b, g, KT, I, G, gpos, fits, kpos, touch),
      p2_b_le_hi(b, g, KT, I, G, gpos, fits, kpos, touch)),
    p2_nc_le_mc(g, Gr, KT, I, G, group))

# Equal slots, both above their b_lo, name the same block.
def p2_same_block(+b: Nat, +c: Nat, +g: Nat, +h: Nat, +KT: Nat, +I: Nat, +G: Nat,
    gh: {g == h : Nat},
    rr: {Nat.sub(b, Impl.b_lo(g, KT, I, G)) == Nat.sub(c, Impl.b_lo(h, KT, I, G)) : Nat},
    lob: {Nat.is_le(Impl.b_lo(g, KT, I, G), b) == True{} : Bool},
    loc: {Nat.is_le(Impl.b_lo(h, KT, I, G), c) == True{} : Bool})
  -> {b == c : Nat}:
  %Arith.ar_sub_add(b, Impl.b_lo(g, KT, I, G), lob) : {_ == c : Nat}
  %Equal.sym(Nat, Nat.sub(b, Impl.b_lo(g, KT, I, G)), Nat.sub(c, Impl.b_lo(h, KT, I, G)), rr) : {Nat.add(Impl.b_lo(g, KT, I, G), _) == c : Nat}
  %Equal.sym(Nat, g, h, gh) : {Nat.add(Impl.b_lo(_, KT, I, G), Nat.sub(c, Impl.b_lo(h, KT, I, G))) == c : Nat}
  Arith.ar_sub_add(c, Impl.b_lo(h, KT, I, G), loc)

def p2_inj_finish(+b: Nat, +c: Nat, +g: Nat, +h: Nat, +KT: Nat, +I: Nat, +G: Nat,
    both: {g == h : Nat} & {Nat.sub(b, Impl.b_lo(g, KT, I, G)) == Nat.sub(c, Impl.b_lo(h, KT, I, G)) : Nat},
    lob: {Nat.is_le(Impl.b_lo(g, KT, I, G), b) == True{} : Bool},
    loc: {Nat.is_le(Impl.b_lo(h, KT, I, G), c) == True{} : Bool})
  -> {g == h : Nat} & {b == c : Nat}:
  (gh, rr) = both
  +ghp = gh
  (ghp, p2_same_block(b, c, g, h, KT, I, G, ghp, rr, lob, loc))

def Laws.slot_in_range(mats, n, k, G, g, b, grid, shaped, fits, group, contributor):
  +gp = grid
  +fp = fits
  +gr = group
  +tc = contributor
  +kp = p2_kt_pos(k, shaped)
  +off = p2_off_lt_nc(b, g, Impl.kt(k), Impl.total(mats, n, k), G,
    p2_lo_le_b(b, g, Impl.kt(k), Impl.total(mats, n, k), G, gp, fp, kp, tc),
    p2_b_le_hi(b, g, Impl.kt(k), Impl.total(mats, n, k), G, gp, fp, kp, tc))
  +ncle = p2_nc_le_mc(g, Impl.groups(mats, n), Impl.kt(k), Impl.total(mats, n, k), G, gr)
  (off, (ncle, p2_addr_lt(g, Impl.groups(mats, n), Impl.max_contrib(Impl.groups(mats, n), Impl.kt(k), Impl.total(mats, n, k), G), Nat.sub(b, Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G)),
    Arith.ar_lt_le_trans(Nat.sub(b, Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G)), Impl.nc(g, Impl.kt(k), Impl.total(mats, n, k), G), Impl.max_contrib(Impl.groups(mats, n), Impl.kt(k), Impl.total(mats, n, k), G), off, ncle), gr)))

def Laws.slot_injective(mats, n, k, G, g, b, h, c, grid, shaped, fits, group_g, group_h,
    touch_b, touch_c, same):
  +gp = grid
  +fp = fits
  +tb = touch_b
  +tc = touch_c
  +kp = p2_kt_pos(k, shaped)
  p2_inj_finish(b, c, g, h, Impl.kt(k), Impl.total(mats, n, k), G,
    Arith.ar_divmod_inj(g, Nat.sub(b, Impl.b_lo(g, Impl.kt(k), Impl.total(mats, n, k), G)), h, Nat.sub(c, Impl.b_lo(h, Impl.kt(k), Impl.total(mats, n, k), G)), Impl.max_contrib(Impl.groups(mats, n), Impl.kt(k), Impl.total(mats, n, k), G),
      p2_off_lt_mc(b, g, Impl.groups(mats, n), Impl.kt(k), Impl.total(mats, n, k), G, gp, fp, kp, tb, group_g),
      p2_off_lt_mc(c, h, Impl.groups(mats, n), Impl.kt(k), Impl.total(mats, n, k), G, gp, fp, kp, tc, group_h),
      same),
    p2_lo_le_b(b, g, Impl.kt(k), Impl.total(mats, n, k), G, gp, fp, kp, tb),
    p2_lo_le_b(c, h, Impl.kt(k), Impl.total(mats, n, k), G, gp, fp, kp, tc))
