# WIP shared Nat arithmetic lemmas for the m16 partition proofs (merged into
# gemm_m16_partition_proof.bend at the end). Statements fixed; proofs filled below each law.
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

law ar_add_succ_r:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

law ar_add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

law ar_add_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

law ar_mul_zero_r:
  for +a: Nat
  {Nat.mul(a, 0n) == 0n : Nat}

law ar_mul_succ_r:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}

law ar_mul_comm:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, b) == Nat.mul(b, a) : Nat}

law ar_mul_add_l:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}

law ar_mul_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}

law ar_le_refl:
  for +a: Nat
  {Nat.is_le(a, a) == True{} : Bool}

law ar_lt_not_le:
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(a, b) == Bool.not(Nat.is_le(b, a)) : Bool}

law ar_gt_flip:
  for +a: Nat
  for +b: Nat
  {Nat.is_gt(a, b) == Nat.is_lt(b, a) : Bool}

law ar_ge_flip:
  for +a: Nat
  for +b: Nat
  {Nat.is_ge(a, b) == Nat.is_le(b, a) : Bool}

law ar_lt_succ_le:
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}

law ar_le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

law ar_le_antisym:
  for +a: Nat
  for +b: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for ba: {Nat.is_le(b, a) == True{} : Bool}
  {a == b : Nat}

law ar_le_add_cancel:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == Nat.is_le(a, b) : Bool}

law ar_lt_add_cancel:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == Nat.is_lt(a, b) : Bool}

law ar_le_add_r:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}

law ar_sub_add:
  for +a: Nat
  for +b: Nat
  for ba: {Nat.is_le(b, a) == True{} : Bool}
  {Nat.add(b, Nat.sub(a, b)) == a : Nat}

law ar_add_sub:
  for +a: Nat
  for +b: Nat
  {Nat.sub(Nat.add(a, b), a) == b : Nat}

law ar_le_mul_mono:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}

# Galois connection of floor division: q * b <= a iff q <= a / b (b >= 1).
law ar_div_le:
  for +q: Nat
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.is_le(Nat.mul(q, b), a) == Nat.is_le(q, Nat.div(a, b)) : Bool}

law ar_divmod:
  for +a: Nat
  for +b: Nat
  for pos: {Nat.is_lt(0n, b) == True{} : Bool}
  {Nat.add(Nat.mul(Nat.div(a, b), b), Nat.mod(a, b)) == a : Nat} &
  {Nat.is_lt(Nat.mod(a, b), b) == True{} : Bool}

law ar_div_unique:
  for +q: Nat
  for +r: Nat
  for +b: Nat
  for small: {Nat.is_lt(r, b) == True{} : Bool}
  {Nat.div(Nat.add(Nat.mul(q, b), r), b) == q : Nat} &
  {Nat.mod(Nat.add(Nat.mul(q, b), r), b) == r : Nat}
