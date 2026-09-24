# WIP proofs (part 1): partition laws owners_exactly_one, range_is_owned, owner_owns,
# runs_iff_touches, plus the core owner/start/touches lemmas (contract below) that the p2
# and p4 WIP files use. Merged into gemm_m16_partition_proof.bend (imports and `Arith.`
# prefixes stripped). Prefix every new local def with p1_.
import Base
import ./gemm_m16_partition.bend as Impl
import ./gemm_m16_partition_spec.bend as Spec
import ./gemm_m16_partition_laws.bend as Laws
import ./gemm_m16_partition_wip_arith.bend as Arith

# ---- local helpers ----

def p1_rt(-a: Bool, -b: Bool, e: {a == b : Bool}, h: {a == True{} : Bool})
  -> {b == True{} : Bool}:
  Equal.trans(Bool, b, a, True{}, Equal.sym(Bool, a, b, e), h)

def p1_not_not(z: Bool) -> {Bool.not(Bool.not(z)) == z : Bool}:
  match z:
    case False{}:
      {==}
    case True{}:
      {==}

# s <= x iff s < x + 1.
def p1_le_lt_succ(+s: Nat, +x: Nat) -> {Nat.is_le(s, x) == Nat.is_lt(s, 1n+x) : Bool}:
  Equal.sym(Bool, Nat.is_lt(s, 1n+x), Nat.is_le(1n+s, 1n+x), Arith.ar_lt_succ_le(s, 1n+x))

# s <= m - 1 iff s < m, for m >= 1.
def p1_le_pred(+s: Nat, +m: Nat, pos: {Nat.is_le(1n, m) == True{} : Bool})
  -> {Nat.is_le(s, Nat.sub(m, 1n)) == Nat.is_lt(s, m) : Bool}:
  %Arith.ar_sub_add(m, 1n, pos) : {Nat.is_le(s, Nat.sub(m, 1n)) == Nat.is_lt(s, _) : Bool}
  Equal.sym(Bool, Nat.is_lt(s, 1n+Nat.sub(m, 1n)), Nat.is_le(1n+s, 1n+Nat.sub(m, 1n)),
    Arith.ar_lt_succ_le(s, 1n+Nat.sub(m, 1n)))

# 0 < (y + 1) * G for G >= 1.
def p1_mul_pos(+y: Nat, +G: Nat, gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.mul(1n+y, G)) == True{} : Bool}:
  Arith.ar_lt_le_trans(0n, G, Nat.mul(1n+y, G), gpos, Arith.ar_le_add_r(G, Nat.mul(y, G)))

# start(b) <= y iff b * I < (y + 1) * G.
def p1_start_le(+b: Nat, +y: Nat, +I: Nat, +G: Nat, gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_le(Impl.start(b, I, G), y) == Nat.is_lt(Nat.mul(b, I), Nat.mul(1n+y, G)) : Bool}:
  Equal.trans(Bool, Nat.is_le(Impl.start(b, I, G), y), Nat.is_lt(Impl.start(b, I, G), 1n+y),
    Nat.is_lt(Nat.mul(b, I), Nat.mul(1n+y, G)),
    p1_le_lt_succ(Impl.start(b, I, G), y),
    Arith.ar_div_lt(1n+y, Nat.mul(b, I), G, gpos))

# x < start(b) iff (x + 1) * G <= b * I.
def p1_lt_start(+x: Nat, +b: Nat, +I: Nat, +G: Nat, gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_lt(x, Impl.start(b, I, G)) == Nat.is_le(Nat.mul(1n+x, G), Nat.mul(b, I)) : Bool}:
  Equal.trans(Bool, Nat.is_lt(x, Impl.start(b, I, G)), Nat.is_le(1n+x, Impl.start(b, I, G)),
    Nat.is_le(Nat.mul(1n+x, G), Nat.mul(b, I)),
    Arith.ar_lt_succ_le(x, Impl.start(b, I, G)),
    Equal.sym(Bool, Nat.is_le(Nat.mul(1n+x, G), Nat.mul(b, I)),
      Nat.is_le(1n+x, Impl.start(b, I, G)),
      Arith.ar_div_le(1n+x, Nat.mul(b, I), G, gpos)))

# D - 1 <= b iff D < b + 2.
def p1_core_a(+D: Nat, +b: Nat)
  -> {Nat.is_le(Nat.sub(D, 1n), b) == Nat.is_lt(D, 2n+b) : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.sub(D, 1n), b), Nat.is_le(D, 1n+b), Nat.is_lt(D, 2n+b),
    Arith.ar_le_sub_iff(D, 1n, b), p1_le_lt_succ(D, 1n+b))

# A - 1 < M iff A <= M, for M >= 1.
def p1_sub1_lt(+A: Nat, +M: Nat, mpos: {Nat.is_lt(0n, M) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(A, 1n), M) == Nat.is_le(A, M) : Bool}:
  Equal.trans(Bool, Nat.is_lt(Nat.sub(A, 1n), M), Nat.is_lt(A, 1n+M), Nat.is_le(A, M),
    Arith.ar_sub_lt_iff(A, 1n, M, mpos),
    Equal.sym(Bool, Nat.is_le(A, M), Nat.is_lt(A, 1n+M), p1_le_lt_succ(A, M)))

# N + I <= I + P iff N <= P.
def p1_core_c(+N: Nat, +I: Nat, +P: Nat)
  -> {Nat.is_le(Nat.add(N, I), Nat.add(I, P)) == Nat.is_le(N, P) : Bool}:
  %Arith.ar_add_comm(I, N) : {Nat.is_le(_, Nat.add(I, P)) == Nat.is_le(N, P) : Bool}
  Arith.ar_le_add_cancel(I, N, P)

# ((N + I - 1) / I) - 1 <= b iff N <= (b + 1) * I   (I >= 1).
def p1_owner_core(+N: Nat, +I: Nat, +b: Nat, +ipos: {Nat.is_lt(0n, I) == True{} : Bool})
  -> {Nat.is_le(Nat.sub(Nat.div(Nat.sub(Nat.add(N, I), 1n), I), 1n), b) ==
    Nat.is_le(N, Nat.mul(1n+b, I)) : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.sub(Nat.div(Nat.sub(Nat.add(N, I), 1n), I), 1n), b),
    Nat.is_lt(Nat.div(Nat.sub(Nat.add(N, I), 1n), I), 2n+b),
    Nat.is_le(N, Nat.mul(1n+b, I)),
    p1_core_a(Nat.div(Nat.sub(Nat.add(N, I), 1n), I), b),
    Equal.trans(Bool, Nat.is_lt(Nat.div(Nat.sub(Nat.add(N, I), 1n), I), 2n+b),
      Nat.is_lt(Nat.sub(Nat.add(N, I), 1n), Nat.mul(2n+b, I)),
      Nat.is_le(N, Nat.mul(1n+b, I)),
      Arith.ar_div_lt(2n+b, Nat.sub(Nat.add(N, I), 1n), I, ipos),
      Equal.trans(Bool, Nat.is_lt(Nat.sub(Nat.add(N, I), 1n), Nat.mul(2n+b, I)),
        Nat.is_le(Nat.add(N, I), Nat.mul(2n+b, I)),
        Nat.is_le(N, Nat.mul(1n+b, I)),
        p1_sub1_lt(Nat.add(N, I), Nat.mul(2n+b, I), p1_mul_pos(1n+b, I, ipos)),
        p1_core_c(N, I, Nat.mul(1n+b, I)))))

# ---- core lemmas: FIXED CONTRACT (p2/p4 stub these exact signatures) ----

# owns(b, x) iff start(b) <= x < start(b + 1)   (G >= 1; any I)
def p1_owns_range(+b: Nat, +x: Nat, +I: Nat, +G: Nat,
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Spec.owns(b, x, I, G) == Bool.and(Nat.is_le(Impl.start(b, I, G), x),
    Nat.is_lt(x, Impl.start(1n+b, I, G))) : Bool}:
  +gp = gpos
  %Equal.sym(Bool, Nat.is_le(Impl.start(b, I, G), x), Nat.is_lt(Nat.mul(b, I), Nat.mul(1n+x, G)), p1_start_le(b, x, I, G, gp)) : {Spec.owns(b, x, I, G) == Bool.and(_, Nat.is_lt(x, Impl.start(1n+b, I, G))) : Bool}
  %Equal.sym(Bool, Nat.is_lt(x, Impl.start(1n+b, I, G)), Nat.is_le(Nat.mul(1n+x, G), Nat.mul(1n+b, I)), p1_lt_start(x, 1n+b, I, G, gp)) : {Spec.owns(b, x, I, G) == Bool.and(Nat.is_lt(Nat.mul(b, I), Nat.mul(1n+x, G)), _) : Bool}
  {==}

# owner(x) <= b iff x < start(b + 1)   (I, G >= 1)
def p1_owner_le(+x: Nat, +b: Nat, +I: Nat, +G: Nat,
    ipos: {Nat.is_lt(0n, I) == True{} : Bool},
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_le(Impl.owner(x, I, G), b) == Nat.is_lt(x, Impl.start(1n+b, I, G)) : Bool}:
  Equal.trans(Bool, Nat.is_le(Impl.owner(x, I, G), b),
    Nat.is_le(Nat.mul(1n+x, G), Nat.mul(1n+b, I)),
    Nat.is_lt(x, Impl.start(1n+b, I, G)),
    p1_owner_core(Nat.mul(1n+x, G), I, b, ipos),
    Equal.sym(Bool, Nat.is_lt(x, Impl.start(1n+b, I, G)),
      Nat.is_le(Nat.mul(1n+x, G), Nat.mul(1n+b, I)),
      p1_lt_start(x, 1n+b, I, G, gpos)))

# c + 1 <= owner(y) iff start(c + 1) <= y   (I, G >= 1)
def p1_le_owner_succ(+c: Nat, +y: Nat, +I: Nat, +G: Nat,
    ipos: {Nat.is_lt(0n, I) == True{} : Bool},
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_le(1n+c, Impl.owner(y, I, G)) == Nat.is_le(Impl.start(1n+c, I, G), y) : Bool}:
  %Arith.ar_lt_succ_le(c, Impl.owner(y, I, G)) : {_ == Nat.is_le(Impl.start(1n+c, I, G), y) : Bool}
  %Equal.sym(Bool, Nat.is_lt(c, Impl.owner(y, I, G)), Bool.not(Nat.is_le(Impl.owner(y, I, G), c)), Arith.ar_lt_not_le(c, Impl.owner(y, I, G))) : {_ == Nat.is_le(Impl.start(1n+c, I, G), y) : Bool}
  %Equal.sym(Bool, Nat.is_le(Impl.owner(y, I, G), c), Nat.is_lt(y, Impl.start(1n+c, I, G)), p1_owner_le(y, c, I, G, ipos, gpos)) : {Bool.not(_) == Nat.is_le(Impl.start(1n+c, I, G), y) : Bool}
  %Equal.sym(Bool, Nat.is_lt(y, Impl.start(1n+c, I, G)), Bool.not(Nat.is_le(Impl.start(1n+c, I, G), y)), Arith.ar_lt_not_le(y, Impl.start(1n+c, I, G))) : {Bool.not(_) == Nat.is_le(Impl.start(1n+c, I, G), y) : Bool}
  p1_not_not(Nat.is_le(Impl.start(1n+c, I, G), y))

# 0 <= owner(y) and start(0) <= y   (G >= 1)
def p1_le_owner_zero(+y: Nat, +I: Nat, +G: Nat, +gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_le(0n, Impl.owner(y, I, G)) == Nat.is_le(Impl.start(0n, I, G), y) : Bool}:
  Equal.trans(Bool, Nat.is_le(0n, Impl.owner(y, I, G)), True{},
    Nat.is_le(Impl.start(0n, I, G), y),
    Arith.ar_le_add_r(0n, Impl.owner(y, I, G)),
    Equal.sym(Bool, Nat.is_le(Impl.start(0n, I, G), y), True{},
      Equal.trans(Bool, Nat.is_le(Impl.start(0n, I, G), y),
        Nat.is_lt(Nat.mul(0n, I), Nat.mul(1n+y, G)), True{},
        p1_start_le(0n, y, I, G, gpos), p1_mul_pos(y, G, gpos))))

def p1_le_owner_go(b: Nat, +y: Nat, +I: Nat, +G: Nat,
    ipos: {Nat.is_lt(0n, I) == True{} : Bool},
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_le(b, Impl.owner(y, I, G)) == Nat.is_le(Impl.start(b, I, G), y) : Bool}:
  match b:
    case 0n:
      p1_le_owner_zero(y, I, G, gpos)
    case 1n+c:
      p1_le_owner_succ(c, y, I, G, ipos, gpos)

# b <= owner(y) iff start(b) <= y   (I, G >= 1)
def p1_le_owner(+b: Nat, +y: Nat, +I: Nat, +G: Nat,
    ipos: {Nat.is_lt(0n, I) == True{} : Bool},
    gpos: {Nat.is_lt(0n, G) == True{} : Bool})
  -> {Nat.is_le(b, Impl.owner(y, I, G)) == Nat.is_le(Impl.start(b, I, G), y) : Bool}:
  p1_le_owner_go(b, y, I, G, ipos, gpos)

# owner(x) is in the grid for x < I   (G >= 1)
def p1_owner_lt(+x: Nat, +I: Nat, +G: Nat,
    gpos: {Nat.is_lt(0n, G) == True{} : Bool},
    inside: {Nat.is_lt(x, I) == True{} : Bool})
  -> {Nat.is_lt(Impl.owner(x, I, G), G) == True{} : Bool}:
  +gp = gpos
  +lt1 = p1_rt(Nat.is_lt(x, I), Nat.is_le(1n+x, I), Arith.ar_lt_succ_le(x, I), inside)
  +g1 = p1_rt(Nat.is_lt(0n, G), Nat.is_le(1n, G), Arith.ar_lt_succ_le(0n, G), gp)
  +ipos = Arith.ar_lt_le_trans(0n, 1n+x, I, {==}, lt1)
  %p1_le_pred(Impl.owner(x, I, G), G, g1) : {_ == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(Impl.owner(x, I, G), Nat.sub(G, 1n)), Nat.is_lt(x, Impl.start(1n+Nat.sub(G, 1n), I, G)), p1_owner_le(x, Nat.sub(G, 1n), I, G, ipos, gp)) : {_ == True{} : Bool}
  %Equal.sym(Nat, Nat.add(1n, Nat.sub(G, 1n)), G, Arith.ar_sub_add(G, 1n, g1)) : {Nat.is_lt(x, Nat.div(Nat.mul(_, I), G)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(x, Nat.div(Nat.mul(G, I), G)), Nat.is_le(Nat.mul(1n+x, G), Nat.mul(G, I)), p1_lt_start(x, G, I, G, gp)) : {_ == True{} : Bool}
  %Arith.ar_mul_comm(I, G) : {Nat.is_le(Nat.mul(1n+x, G), _) == True{} : Bool}
  Arith.ar_le_mul_mono(1n+x, I, G, lt1)

# STUB-BEGIN (proven in wip_p1t)
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

# ---- laws ----
