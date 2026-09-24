# WIP shared Nat/Bool lemmas for the m16 partition proofs (merged into
# gemm_m16_partition_proof.bend at the end). Statements are a FIXED CONTRACT used by the
# p1..p4 WIP files: never change a statement; replace each `?TODO` body with a proof.
import Base

def ar_Truth(value: Bool) -> Type:
  match value:
    case False{}:
      Empty
    case True{}:
      Unit

# False == True is absurd.
def ar_false_true(equal: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, equal) : ar_Truth(_)
  Unit{}

law ar_add_zero_r:
  for +a: Nat
  {Nat.add(a, 0n) == a : Nat}

def ar_add_zero_r(a):
  ?TODO

law ar_add_succ_r:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def ar_add_succ_r(a, b):
  ?TODO

law ar_add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def ar_add_comm(a, b):
  ?TODO

law ar_add_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def ar_add_assoc(a, b, c):
  ?TODO

law ar_mul_zero_r:
  for +a: Nat
  {Nat.mul(a, 0n) == 0n : Nat}

def ar_mul_zero_r(a):
  ?TODO

law ar_mul_succ_r:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}

def ar_mul_succ_r(a, b):
  ?TODO

law ar_mul_comm:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, b) == Nat.mul(b, a) : Nat}

def ar_mul_comm(a, b):
  ?TODO

law ar_mul_add_l:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}

def ar_mul_add_l(a, b, c):
  ?TODO

law ar_mul_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}

def ar_mul_assoc(a, b, c):
  ?TODO

law ar_le_refl:
  for +a: Nat
  {Nat.is_le(a, a) == True{} : Bool}

def ar_le_refl(a):
  ?TODO

law ar_lt_not_le:
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(a, b) == Bool.not(Nat.is_le(b, a)) : Bool}

def ar_lt_not_le(a, b):
  ?TODO

law ar_gt_flip:
  for +a: Nat
  for +b: Nat
  {Nat.is_gt(a, b) == Nat.is_lt(b, a) : Bool}

def ar_gt_flip(a, b):
  ?TODO

law ar_ge_flip:
  for +a: Nat
  for +b: Nat
  {Nat.is_ge(a, b) == Nat.is_le(b, a) : Bool}

def ar_ge_flip(a, b):
  ?TODO

law ar_lt_succ_le:
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}

def ar_lt_succ_le(a, b):
  ?TODO

law ar_le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

def ar_le_trans(a, b, c, ab, bc):
  ?TODO

law ar_le_antisym:
  for +a: Nat
  for +b: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for ba: {Nat.is_le(b, a) == True{} : Bool}
  {a == b : Nat}

def ar_le_antisym(a, b, ab, ba):
  ?TODO

law ar_le_add_cancel:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == Nat.is_le(a, b) : Bool}

def ar_le_add_cancel(c, a, b):
  ?TODO

law ar_lt_add_cancel:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == Nat.is_lt(a, b) : Bool}

def ar_lt_add_cancel(c, a, b):
  ?TODO

law ar_le_add_r:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}

def ar_le_add_r(a, b):
  ?TODO

law ar_sub_add:
  for +a: Nat
  for +b: Nat
  for ba: {Nat.is_le(b, a) == True{} : Bool}
  {Nat.add(b, Nat.sub(a, b)) == a : Nat}

def ar_sub_add(a, b, ba):
  ?TODO

law ar_add_sub:
  for +a: Nat
  for +b: Nat
  {Nat.sub(Nat.add(a, b), a) == b : Nat}

def ar_add_sub(a, b):
  ?TODO

law ar_le_mul_mono:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}

def ar_le_mul_mono(a, b, c, ab):
  ?TODO

# Galois connection of floor division: q * b <= a iff q <= a / b (b >= 1).
law ar_div_le:
  for +q: Nat
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.is_le(Nat.mul(q, b), a) == Nat.is_le(q, Nat.div(a, b)) : Bool}

def ar_div_le(q, a, b, pos):
  ?TODO

law ar_divmod:
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat} &
  {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}

def ar_divmod(a, b, pos):
  ?TODO

law ar_div_unique:
  for +q: Nat
  for +r: Nat
  for +b: Nat
  for small: {Nat.is_lt(r, b) == True{} : Bool}
  {Nat.div(Nat.add(Nat.mul(q, b), r), b) == q : Nat} &
  {Nat.mod(Nat.add(Nat.mul(q, b), r), b) == r : Nat}

def ar_div_unique(q, r, b, small):
  ?TODO

# ---- extra shared statements (contract) ----

def ar_true_false(equal: {True{} == False{} : Bool}) -> Empty:
  ?TODO

def ar_zero_succ(-n: Nat, equal: {0n == 1n+n : Nat}) -> Empty:
  ?TODO

def ar_succ_inj(-a: Nat, -b: Nat, equal: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  ?TODO

# Boolean extensionality from both implications.
def ar_bool_ext(a: Bool, b: Bool) -> ({a == True{} : Bool} -> {b == True{} : Bool}) ->
    ({b == True{} : Bool} -> {a == True{} : Bool}) -> {a == b : Bool}:
  ?TODO

def ar_and_l(a: Bool, -b: Bool, both: {Bool.and(a, b) == True{} : Bool})
  -> {a == True{} : Bool}:
  ?TODO

def ar_and_r(a: Bool, b: Bool, both: {Bool.and(a, b) == True{} : Bool})
  -> {b == True{} : Bool}:
  ?TODO

def ar_and_intro(-a: Bool, -b: Bool, left: {a == True{} : Bool}, right: {b == True{} : Bool})
  -> {Bool.and(a, b) == True{} : Bool}:
  ?TODO

def ar_false_ne(-a: Bool, no: {a == False{} : Bool}, yes: {a == True{} : Bool}) -> Empty:
  ?TODO

# A Bool that is not True is False.
def ar_not_true(a: Bool, no: {a == True{} : Bool} -> Empty) -> {a == False{} : Bool}:
  ?TODO

law ar_sub_zero_r:
  for +a: Nat
  {Nat.sub(a, 0n) == a : Nat}

def ar_sub_zero_r(a):
  ?TODO

law ar_mul_one_l:
  for +a: Nat
  {Nat.mul(1n, a) == a : Nat}

def ar_mul_one_l(a):
  ?TODO

law ar_lt_irrefl:
  for +a: Nat
  {Nat.is_lt(a, a) == False{} : Bool}

def ar_lt_irrefl(a):
  ?TODO

law ar_eq_true:
  for +a: Nat
  for +b: Nat
  for equal: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

def ar_eq_true(a, b, equal):
  ?TODO

law ar_eq_refl:
  for +a: Nat
  {Nat.is_eq(a, a) == True{} : Bool}

def ar_eq_refl(a):
  ?TODO

# is_eq is False exactly when the values differ.
law ar_eq_false:
  for +a: Nat
  for +b: Nat
  for differ: {a == b : Nat} -> Empty
  {Nat.is_eq(a, b) == False{} : Bool}

def ar_eq_false(a, b, differ):
  ?TODO

law ar_lt_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for bc: {Nat.is_lt(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def ar_lt_trans(a, b, c, ab, bc):
  ?TODO

law ar_le_lt_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_lt(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def ar_le_lt_trans(a, b, c, ab, bc):
  ?TODO

law ar_lt_le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def ar_lt_le_trans(a, b, c, ab, bc):
  ?TODO

law ar_lt_le:
  for +a: Nat
  for +b: Nat
  for ab: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

def ar_lt_le(a, b, ab):
  ?TODO

law ar_le_add_l:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}

def ar_le_add_l(a, b):
  ?TODO

# a - b < c iff a < b + c (no side condition on Nat).
law ar_sub_lt_iff:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.is_lt(Nat.sub(a, b), c) == Nat.is_lt(a, Nat.add(b, c)) : Bool}

def ar_sub_lt_iff(a, b, c):
  ?TODO

# c < a - b iff b + c < a (no side condition on Nat).
law ar_lt_sub_iff:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.is_lt(c, Nat.sub(a, b)) == Nat.is_lt(Nat.add(b, c), a) : Bool}

def ar_lt_sub_iff(a, b, c):
  ?TODO

law ar_le_sub_iff:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.is_le(Nat.sub(a, b), c) == Nat.is_le(a, Nat.add(b, c)) : Bool}

def ar_le_sub_iff(a, b, c):
  ?TODO

law ar_mul_le_cancel:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for pos: {Nat.is_lt(0n, c) == True{} : Bool}
  {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == Nat.is_le(a, b) : Bool}

def ar_mul_le_cancel(a, b, c, pos):
  ?TODO

law ar_mul_lt_cancel:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for pos: {Nat.is_lt(0n, c) == True{} : Bool}
  {Nat.is_lt(Nat.mul(a, c), Nat.mul(b, c)) == Nat.is_lt(a, b) : Bool}

def ar_mul_lt_cancel(a, b, c, pos):
  ?TODO

# Dual Galois connection of floor division: a / b < q iff a < q * b (b >= 1).
law ar_div_lt:
  for +q: Nat
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.is_lt(Nat.div(a, b), q) == Nat.is_lt(a, Nat.mul(q, b)) : Bool}

def ar_div_lt(q, a, b, pos):
  ?TODO

law ar_div_add_self:
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.div(Nat.add(a, b), b) == 1n+Nat.div(a, b) : Nat}

def ar_div_add_self(a, b, pos):
  ?TODO

law ar_div_mono:
  for +a: Nat
  for +c: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  for ac: {Nat.is_le(a, c) == True{} : Bool}
  {Nat.is_le(Nat.div(a, b), Nat.div(c, b)) == True{} : Bool}

def ar_div_mono(a, c, b, pos, ac):
  ?TODO

# q1 * m + r1 == q2 * m + r2 with r1, r2 < m forces q1 == q2 and r1 == r2.
law ar_divmod_inj:
  for +q1: Nat
  for +r1: Nat
  for +q2: Nat
  for +r2: Nat
  for +m: Nat
  for small1: {Nat.is_lt(r1, m) == True{} : Bool}
  for small2: {Nat.is_lt(r2, m) == True{} : Bool}
  for same: {Nat.add(Nat.mul(q1, m), r1) == Nat.add(Nat.mul(q2, m), r2) : Nat}
  {q1 == q2 : Nat} & {r1 == r2 : Nat}

def ar_divmod_inj(q1, r1, q2, r2, m, small1, small2, same):
  ?TODO

law ar_min_lt:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(c, Nat.min(a, b)) == Bool.and(Nat.is_lt(c, a), Nat.is_lt(c, b)) : Bool}

def ar_min_lt(c, a, b):
  ?TODO

law ar_min_left:
  for +a: Nat
  for +b: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.min(a, b) == a : Nat}

def ar_min_left(a, b, ab):
  ?TODO
