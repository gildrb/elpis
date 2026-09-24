# WIP proofs: law flush_once_iff_touches. Laws.mainloop_trace (wip_p5) may be called.
# Merged into gemm_m16_partition_proof.bend (imports, STUB blocks and `Arith.` prefixes
# stripped). Every new local def is prefixed p6_.
import Base
import ./gemm_m16_partition.bend as Impl
import ./gemm_m16_partition_spec.bend as Spec
import ./gemm_m16_partition_laws.bend as Laws
import ./gemm_m16_partition_wip_arith.bend as Arith

# STUB-BEGIN (proven in wip_p1 / wip_p1t)
# owns(b, x) iff start(b) <= x < start(b + 1)   (G >= 1; any I)
def p1_owns_range(+b: Nat, +x: Nat, +I: Nat, +G: Nat,
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Spec.owns(b, x, I, G) == Bool.and(Nat.is_le(Impl.start(b, I, G), x),
    Nat.is_lt(x, Impl.start(1n+b, I, G))) : Bool}:
  ?TODO

# owner(x) <= b iff x < start(b + 1)   (I, G >= 1)
def p1_owner_le(+x: Nat, +b: Nat, +I: Nat, +G: Nat,
    ipos: {Nat.is_lt(0n, I) == True{} : Bool},
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_le(Impl.owner(x, I, G), b) == Nat.is_lt(x, Impl.start(1n+b, I, G)) : Bool}:
  ?TODO

# b <= owner(y) iff start(b) <= y   (I, G >= 1)
def p1_le_owner(+b: Nat, +y: Nat, +I: Nat, +G: Nat,
    ipos: {Nat.is_lt(0n, I) == True{} : Bool},
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_le(b, Impl.owner(y, I, G)) == Nat.is_le(Impl.start(b, I, G), y) : Bool}:
  ?TODO

# owner(x) is in the grid for x < I   (G >= 1)
def p1_owner_lt(+x: Nat, +I: Nat, +G: Nat,
    gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    inside: {Nat.is_lt(x, I) == True{} : Bool})
  -> {Nat.is_lt(Impl.owner(x, I, G), G) == True{} : Bool}:
  ?TODO

# Block b touches group g iff its range [start(b), start(b + 1)) is non-empty and meets
# [g * KT, (g + 1) * KT)   (G >= 1; any KT, I)
def p1_touches_range(+b: Nat, +g: Nat, +KT: Nat, +I: Nat, +G: Nat,
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Spec.touches(b, g, KT, I, G) ==
    Bool.and(Nat.is_lt(Impl.start(b, I, G), Impl.start(1n+b, I, G)),
      Bool.and(Nat.is_lt(Impl.start(b, I, G), Nat.mul(1n+g, KT)),
        Nat.is_lt(Nat.mul(g, KT), Impl.start(1n+b, I, G)))) : Bool}:
  ?TODO
# STUB-END

# ---- Bool / Nat helpers ----

def p6_rt(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {a == True{} : Bool})
  -> {b == True{} : Bool}:
  Equal.trans(Bool, b, a, True{}, Equal.sym(Bool, a, b, e), h)

def p6_rf(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {a == False{} : Bool})
  -> {b == False{} : Bool}:
  Equal.trans(Bool, b, a, False{}, Equal.sym(Bool, a, b, e), h)

def p6_snd(-A: Type, -B: Type, p: A & B) -> B:
  match p:
    case (a, b):
      b

def p6_and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def p6_and_true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def p6_or_false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def p6_or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# and(a, b) == b when b implies a.
def p6_and_imp(+a: Bool, b: Bool, imp: {b == True{} : Bool} -> {a == True{} : Bool})
  -> {Bool.and(a, b) == b : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, a, True{}, imp({==})) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case False{}:
      p6_and_false(a)

def p6_lt_succ(a: Nat) -> {Nat.is_lt(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      p6_lt_succ(p)

def p6_lt_zero(a: Nat) -> {Nat.is_lt(a, 0n) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def p6_lt_ne(a: Nat, b: Nat, lt: {Nat.is_lt(a, b) == True{} : Bool})
  -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, Arith.ar_false_true(lt))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      p6_lt_ne(p, q, lt)

def p6_gt_ne(a: Nat, b: Nat, h: {Nat.is_le(1n+b, a) == True{} : Bool})
  -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n _:
      Empty.absurd({Nat.is_eq(0n, b) == False{} : Bool}, Arith.ar_false_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      p6_gt_ne(p, q, h)

def p6_nlt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool})
  -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, Arith.ar_true_false(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      p6_nlt_le(p, q, h)

def p6_le_nlt(a: Nat, b: Nat, h: {Nat.is_le(b, a) == True{} : Bool})
  -> {Nat.is_lt(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_lt(0n, 1n+q) == False{} : Bool}, Arith.ar_false_true(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      p6_le_nlt(p, q, h)

# b <= a < b + 1 forces a == b.
def p6_eq_of_le_lt(a: Nat, b: Nat, le: {Nat.is_le(b, a) == True{} : Bool},
    lt: {Nat.is_lt(a, 1n+b) == True{} : Bool})
  -> {Nat.is_eq(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_eq(0n, 1n+q) == True{} : Bool}, Arith.ar_false_true(le))
    case 1n+p 0n:
      Empty.absurd({Nat.is_eq(1n+p, 0n) == True{} : Bool},
        Arith.ar_false_ne(Nat.is_lt(p, 0n), p6_lt_zero(p), lt))
    case 1n+p 1n+q:
      p6_eq_of_le_lt(p, q, le, lt)

# For a <= b exactly one of a == b, a < b holds.
def p6_eq_or_lt(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool})
  -> {Nat.add(Spec.bit(Nat.is_eq(a, b)), Spec.bit(Nat.is_lt(a, b))) == 1n : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.add(Spec.bit(Nat.is_eq(1n+p, 0n)), Spec.bit(Nat.is_lt(1n+p, 0n))) ==
        1n : Nat}, Arith.ar_false_true(h))
    case 1n+p 1n+q:
      p6_eq_or_lt(p, q, h)

# ---- group arithmetic (A = g * KT, B = (g + 1) * KT) ----

# KT = k / 16 >= 8 > 0 for k >= 128.
def p6_kt_pos(+k: Nat, shaped: {Nat.is_le(128n, k) == True{} : Bool})
  -> {Nat.is_lt(0n, Impl.kt(k)) == True{} : Bool}:
  Arith.ar_lt_le_trans(0n, 8n, Impl.kt(k), {==},
    p6_rt(Nat.is_le(Nat.mul(8n, 16n), k), Nat.is_le(8n, Nat.div(k, 16n)),
      Arith.ar_div_le(8n, k, 16n, {==}), shaped))

def p6_A_lt_B(+g: Nat, +KT: Nat, kpos: {Nat.is_lt(0n, KT) == True{} : Bool})
  -> {Nat.is_lt(Nat.mul(g, KT), Nat.mul(1n+g, KT)) == True{} : Bool}:
  p6_rt(Nat.is_lt(g, 1n+g), Nat.is_lt(Nat.mul(g, KT), Nat.mul(1n+g, KT)),
    Equal.sym(Bool, Nat.is_lt(Nat.mul(g, KT), Nat.mul(1n+g, KT)), Nat.is_lt(g, 1n+g),
      Arith.ar_mul_lt_cancel(g, 1n+g, KT, kpos)),
    p6_lt_succ(g))

# it < A: it is not in group g.
def p6_div_ne_lo(+it: Nat, +KT: Nat, +g: Nat, kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    hx: {Nat.is_lt(it, Nat.mul(g, KT)) == True{} : Bool})
  -> {Nat.is_eq(Nat.div(it, KT), g) == False{} : Bool}:
  p6_lt_ne(Nat.div(it, KT), g,
    p6_rt(Nat.is_lt(it, Nat.mul(g, KT)), Nat.is_lt(Nat.div(it, KT), g),
      Equal.sym(Bool, Nat.is_lt(Nat.div(it, KT), g), Nat.is_lt(it, Nat.mul(g, KT)),
        Arith.ar_div_lt(g, it, KT, kpos)),
      hx))

# B <= it: it is not in group g.
def p6_div_ne_hi(+it: Nat, +KT: Nat, +g: Nat, kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    hy: {Nat.is_lt(it, Nat.mul(1n+g, KT)) == False{} : Bool})
  -> {Nat.is_eq(Nat.div(it, KT), g) == False{} : Bool}:
  p6_gt_ne(Nat.div(it, KT), g,
    p6_nlt_le(Nat.div(it, KT), 1n+g,
      p6_rf(Nat.is_lt(it, Nat.mul(1n+g, KT)), Nat.is_lt(Nat.div(it, KT), 1n+g),
        Equal.sym(Bool, Nat.is_lt(Nat.div(it, KT), 1n+g), Nat.is_lt(it, Nat.mul(1n+g, KT)),
          Arith.ar_div_lt(1n+g, it, KT, kpos)),
        hy)))

# A <= it < B: it is in group g.
def p6_div_eq_mid(+it: Nat, +KT: Nat, +g: Nat, +kpos: {Nat.is_lt(0n, KT) == True{} : Bool},
    leA: {Nat.is_le(Nat.mul(g, KT), it) == True{} : Bool},
    hy: {Nat.is_lt(it, Nat.mul(1n+g, KT)) == True{} : Bool})
  -> {Nat.is_eq(Nat.div(it, KT), g) == True{} : Bool}:
  p6_eq_of_le_lt(Nat.div(it, KT), g,
    p6_rt(Nat.is_le(Nat.mul(g, KT), it), Nat.is_le(g, Nat.div(it, KT)),
      Arith.ar_div_le(g, it, KT, kpos), leA),
    p6_rt(Nat.is_lt(it, Nat.mul(1n+g, KT)), Nat.is_lt(Nat.div(it, KT), 1n+g),
      Equal.sym(Bool, Nat.is_lt(Nat.div(it, KT), 1n+g), Nat.is_lt(it, Nat.mul(1n+g, KT)),
        Arith.ar_div_lt(1n+g, it, KT, kpos)),
      hy))

# (A + d + 1) % KT == d + 1 != 0 when d + 1 < KT.
def p6_mod_ne_go(+d: Nat, +KT: Nat, +g: Nat,
    small: {Nat.is_lt(1n+d, KT) == True{} : Bool})
  -> {Nat.is_eq(Nat.mod(1n+Nat.add(Nat.mul(g, KT), d), KT), 0n) == False{} : Bool}:
  %Arith.ar_add_succ_r(Nat.mul(g, KT), d) : {Nat.is_eq(Nat.mod(_, KT), 0n) == False{} : Bool}
  %Equal.sym(Nat, Nat.mod(Nat.add(Nat.mul(g, KT), 1n+d), KT), 1n+d, p6_snd({Nat.div(Nat.add(Nat.mul(g, KT), 1n+d), KT) == g : Nat}, {Nat.mod(Nat.add(Nat.mul(g, KT), 1n+d), KT) == 1n+d : Nat}, Arith.ar_div_unique(g, 1n+d, KT, small))) : {Nat.is_eq(_, 0n) == False{} : Bool}
  {==}

# A <= it and it + 1 < B give (it - A) + 1 < KT.
def p6_mod_small(+it: Nat, +KT: Nat, +g: Nat,
    +leA: {Nat.is_le(Nat.mul(g, KT), it) == True{} : Bool},
    hw: {Nat.is_lt(1n+it, Nat.mul(1n+g, KT)) == True{} : Bool})
  -> {Nat.is_lt(1n+Nat.sub(it, Nat.mul(g, KT)), KT) == True{} : Bool}:
  +A = Nat.mul(g, KT)
  +d = Nat.sub(it, A)
  %Arith.ar_lt_add_cancel(A, 1n+d, KT) : {_ == True{} : Bool}
  %Equal.sym(Nat, Nat.add(A, 1n+d), 1n+Nat.add(A, d), Arith.ar_add_succ_r(A, d)) : {Nat.is_lt(_, Nat.add(A, KT)) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(A, d), it, Arith.ar_sub_add(it, A, leA)) : {Nat.is_lt(1n+_, Nat.add(A, KT)) == True{} : Bool}
  %Arith.ar_add_comm(KT, A) : {Nat.is_lt(1n+it, _) == True{} : Bool}
  hw

# A <= it and it + 1 < B: iteration it + 1 does not start a group.
def p6_mod_ne(+it: Nat, +KT: Nat, +g: Nat,
    +leA: {Nat.is_le(Nat.mul(g, KT), it) == True{} : Bool},
    hw: {Nat.is_lt(1n+it, Nat.mul(1n+g, KT)) == True{} : Bool})
  -> {Nat.is_eq(Nat.mod(1n+it, KT), 0n) == False{} : Bool}:
  +A = Nat.mul(g, KT)
  +d = Nat.sub(it, A)
  +small = p6_mod_small(it, KT, g, leA, hw)
  %Arith.ar_sub_add(it, A, leA) : {Nat.is_eq(Nat.mod(1n+_, KT), 0n) == False{} : Bool}
  p6_mod_ne_go(d, KT, g, small)
