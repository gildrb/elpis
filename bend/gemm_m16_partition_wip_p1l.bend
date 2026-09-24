# WIP proofs: laws owners_exactly_one, range_is_owned, owner_owns (runs_iff_touches retired
# with kernel v1).
# Merged into gemm_m16_partition_proof.bend (imports, STUB blocks and `Arith.` prefixes
# stripped). Every new local def is prefixed p1l_.
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

def p1l_rt(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {a == True{} : Bool})
  -> {b == True{} : Bool}:
  Equal.trans(Bool, b, a, True{}, Equal.sym(Bool, a, b, e), h)

def p1l_fst(-A: Type, -B: Type, p: A & B) -> A:
  match p:
    case (a, b):
      a

def p1l_zero_le(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def p1l_lt_zero(x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def p1l_not_true(x: Bool, h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Arith.ar_false_true(h))
    case False{}:
      {==}

def p1l_not_false(x: Bool, h: {Bool.not(x) == False{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Arith.ar_true_false(h))

# ---- range_is_owned ----

def Laws.range_is_owned(mats, n, k, G, b, x, grid):
  Equal.sym(Bool, Spec.owns(b, x, Impl.total(mats, n, k), G),
    Bool.and(Nat.is_le(Impl.start(b, Impl.total(mats, n, k), G), x),
      Nat.is_lt(x, Impl.start(1n+b, Impl.total(mats, n, k), G))),
    p1_owns_range(b, x, Impl.total(mats, n, k), G, grid))

# ---- owner_owns ----

def p1l_owner_owns(+x: Nat, +I: Nat, +G: Nat,
    +gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    +inside: {Nat.is_lt(x, I) == True{} : Bool})
  -> {Spec.owns(Impl.owner(x, I, G), x, I, G) == True{} : Bool}:
  +ipos = Arith.ar_le_lt_trans(0n, x, I, p1l_zero_le(x), inside)
  +o = Impl.owner(x, I, G)
  %Equal.sym(Bool, Spec.owns(o, x, I, G), Bool.and(Nat.is_le(Impl.start(o, I, G), x), Nat.is_lt(x, Impl.start(1n+o, I, G))), p1_owns_range(o, x, I, G, gpos)) : {_ == True{} : Bool}
  Arith.ar_and_intro(Nat.is_le(Impl.start(o, I, G), x), Nat.is_lt(x, Impl.start(1n+o, I, G)),
    p1l_rt(Nat.is_le(o, o), Nat.is_le(Impl.start(o, I, G), x),
      p1_le_owner(o, x, I, G, ipos, gpos), Arith.ar_le_refl(o)),
    p1l_rt(Nat.is_le(o, o), Nat.is_lt(x, Impl.start(1n+o, I, G)),
      p1_owner_le(x, o, I, G, ipos, gpos), Arith.ar_le_refl(o)))

def Laws.owner_owns(mats, n, k, G, x, grid, inside):
  +gp = grid
  +ins = inside
  (p1l_owner_owns(x, Impl.total(mats, n, k), G, gp, ins),
    p1_owner_lt(x, Impl.total(mats, n, k), G, gp, ins))

# ---- owners_exactly_one ----

# One telescoping step: [x < s0] + [s0 <= x < s1] == [x < s1] when s0 <= s1.
def p1l_bit_step_go(a: Bool, +x: Nat, +s0: Nat, +s1: Nat,
    mono: {Nat.is_le(s0, s1) == True{} : Bool},
    +e: {Nat.is_lt(x, s0) == a : Bool})
  -> {Nat.add(Spec.bit(a), Spec.bit(Bool.and(Nat.is_le(s0, x), Nat.is_lt(x, s1)))) ==
    Spec.bit(Nat.is_lt(x, s1)) : Nat}:
  match a:
    case True{}:
      +nle = p1l_not_true(Nat.is_le(s0, x),
        p1l_rt(Nat.is_lt(x, s0), Bool.not(Nat.is_le(s0, x)), Arith.ar_lt_not_le(x, s0), e))
      +lt1 = Arith.ar_lt_le_trans(x, s0, s1, e, mono)
      %Equal.sym(Bool, Nat.is_le(s0, x), False{}, nle) : {Nat.add(1n, Spec.bit(Bool.and(_, Nat.is_lt(x, s1)))) == Spec.bit(Nat.is_lt(x, s1)) : Nat}
      %Equal.sym(Bool, Nat.is_lt(x, s1), True{}, lt1) : {Nat.add(1n, Spec.bit(Bool.and(False{}, Nat.is_lt(x, s1)))) == Spec.bit(_) : Nat}
      {==}
    case False{}:
      +le = p1l_not_false(Nat.is_le(s0, x),
        Equal.trans(Bool, Bool.not(Nat.is_le(s0, x)), Nat.is_lt(x, s0), False{},
          Equal.sym(Bool, Nat.is_lt(x, s0), Bool.not(Nat.is_le(s0, x)),
            Arith.ar_lt_not_le(x, s0)),
          e))
      %Equal.sym(Bool, Nat.is_le(s0, x), True{}, le) : {Nat.add(0n, Spec.bit(Bool.and(_, Nat.is_lt(x, s1)))) == Spec.bit(Nat.is_lt(x, s1)) : Nat}
      {==}

# owners(c, x) == [x < start(c)] for every c (G >= 1; any I).
def p1l_owners_start(+c: Nat, +x: Nat, +I: Nat, +G: Nat,
    +gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Spec.owners(c, x, I, G) == Spec.bit(Nat.is_lt(x, Impl.start(c, I, G))) : Nat}:
  match c:
    case 0n:
      %Equal.sym(Nat, Nat.div(0n, G), 0n, p1l_fst({Nat.div(0n, G) == 0n : Nat}, {Nat.mod(0n, G) == 0n : Nat}, Arith.ar_div_unique(0n, 0n, G, gpos))) : {0n == Spec.bit(Nat.is_lt(x, _)) : Nat}
      %Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, p1l_lt_zero(x)) : {0n == Spec.bit(_) : Nat}
      {==}
    case 1n+b:
      %Equal.sym(Nat, Spec.owners(b, x, I, G), Spec.bit(Nat.is_lt(x, Impl.start(b, I, G))), p1l_owners_start(b, x, I, G, gpos)) : {Nat.add(_, Spec.bit(Spec.owns(b, x, I, G))) == Spec.bit(Nat.is_lt(x, Impl.start(1n+b, I, G))) : Nat}
      %Equal.sym(Bool, Spec.owns(b, x, I, G), Bool.and(Nat.is_le(Impl.start(b, I, G), x), Nat.is_lt(x, Impl.start(1n+b, I, G))), p1_owns_range(b, x, I, G, gpos)) : {Nat.add(Spec.bit(Nat.is_lt(x, Impl.start(b, I, G))), Spec.bit(_)) == Spec.bit(Nat.is_lt(x, Impl.start(1n+b, I, G))) : Nat}
      p1l_bit_step_go(Nat.is_lt(x, Impl.start(b, I, G)), x, Impl.start(b, I, G),
        Impl.start(1n+b, I, G),
        Arith.ar_div_mono(Nat.mul(b, I), Nat.mul(1n+b, I), G, gpos,
          Arith.ar_le_add_l(I, Nat.mul(b, I))),
        {==})

# start(G) = G * I / G = I.
def p1l_start_full(+I: Nat, +G: Nat, gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Impl.start(G, I, G) == I : Nat}:
  %Arith.ar_mul_comm(I, G) : {Nat.div(_, G) == I : Nat}
  %Arith.ar_add_zero_r(Nat.mul(I, G)) : {Nat.div(_, G) == I : Nat}
  p1l_fst({Nat.div(Nat.add(Nat.mul(I, G), 0n), G) == I : Nat},
    {Nat.mod(Nat.add(Nat.mul(I, G), 0n), G) == 0n : Nat},
    Arith.ar_div_unique(I, 0n, G, gpos))

def Laws.owners_exactly_one(mats, n, k, G, x, grid, inside):
  +gp = grid
  %Equal.sym(Nat, Spec.owners(G, x, Impl.total(mats, n, k), G), Spec.bit(Nat.is_lt(x, Impl.start(G, Impl.total(mats, n, k), G))), p1l_owners_start(G, x, Impl.total(mats, n, k), G, gp)) : {_ == 1n : Nat}
  %Equal.sym(Nat, Impl.start(G, Impl.total(mats, n, k), G), Impl.total(mats, n, k), p1l_start_full(Impl.total(mats, n, k), G, gp)) : {Spec.bit(Nat.is_lt(x, _)) == 1n : Nat}
  %Equal.sym(Bool, Nat.is_lt(x, Impl.total(mats, n, k)), True{}, inside) : {Spec.bit(_) == 1n : Nat}
  {==}

# ---- shared helpers (used by later parts) ----

# KT = k / 16 >= 8 > 0 for k >= 128.
def p1l_kt_pos(+k: Nat, shaped: {Nat.is_le(128n, k) == True{} : Bool})
  -> {Nat.is_lt(0n, Impl.kt(k)) == True{} : Bool}:
  Arith.ar_lt_le_trans(0n, 8n, Impl.kt(k), {==},
    p1l_rt(Nat.is_le(Nat.mul(8n, 16n), k), Nat.is_le(8n, Nat.div(k, 16n)),
      Arith.ar_div_le(8n, k, 16n, {==}), shaped))

# s <= m - 1 iff s < m, for m >= 1.
def p1l_le_pred(+s: Nat, +m: Nat, pos: {Nat.is_le(1n, m) == True{} : Bool})
  -> {Nat.is_le(s, Nat.sub(m, 1n)) == Nat.is_lt(s, m) : Bool}:
  %Arith.ar_sub_add(m, 1n, pos) : {Nat.is_le(s, Nat.sub(m, 1n)) == Nat.is_lt(s, _) : Bool}
  Equal.sym(Bool, Nat.is_lt(s, 1n+Nat.sub(m, 1n)), Nat.is_le(1n+s, 1n+Nat.sub(m, 1n)),
    Arith.ar_lt_succ_le(s, 1n+Nat.sub(m, 1n)))

