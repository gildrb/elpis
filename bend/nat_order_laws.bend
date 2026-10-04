# Generic Nat order / arithmetic laws (API documented in bend/nat_order.bend), proven in
# bend/nat_order_proof.bend by structural induction.
import Base

# ==== Bool ====

# False == True is absurd.
law false_true:
  for e: {False{} == True{} : Bool}
  Empty

law and_l:
  for +a: Bool
  for +b: Bool
  for h: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

law and_r:
  for +a: Bool
  for +b: Bool
  for h: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

law and_intro:
  for +a: Bool
  for +b: Bool
  for ha: {a == True{} : Bool}
  for hb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

# ==== addition ====

law add_zero_r:
  for +a: Nat
  {Nat.add(a, 0n) == a : Nat}

law add_succ_r:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

law add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

law add_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

law add_swap:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

law add_swap4:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}

# ==== multiplication ====

law mul_zero_r:
  for +a: Nat
  {Nat.mul(a, 0n) == 0n : Nat}

law mul_succ_r:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}

law mul_comm:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, b) == Nat.mul(b, a) : Nat}

law mul_add_l:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}

law mul_add_r:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}

law mul_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}

# ==== truncated subtraction ====

law sub_self:
  for +a: Nat
  {Nat.sub(a, a) == 0n : Nat}

law sub_add:
  for +a: Nat
  for +b: Nat
  for ba: {Nat.is_le(b, a) == True{} : Bool}
  {Nat.add(b, Nat.sub(a, b)) == a : Nat}

law add_sub:
  for +a: Nat
  for +b: Nat
  {Nat.sub(Nat.add(a, b), a) == b : Nat}

law sub_add_add:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for ca: {Nat.is_le(c, a) == True{} : Bool}
  for db: {Nat.is_le(d, b) == True{} : Bool}
  {Nat.sub(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.sub(a, c), Nat.sub(b, d)) : Nat}

law sub_chain:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.sub(c, a) == Nat.add(Nat.sub(c, b), Nat.sub(b, a)) : Nat}

# ==== order ====

law le_zero:
  for +n: Nat
  {Nat.is_le(0n, n) == True{} : Bool}

law le_succ:
  for +n: Nat
  {Nat.is_le(n, 1n+n) == True{} : Bool}

law le_refl:
  for +a: Nat
  {Nat.is_le(a, a) == True{} : Bool}

law le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

law le_of_eq:
  for +a: Nat
  for +b: Nat
  for e: {a == b : Nat}
  {Nat.is_le(a, b) == True{} : Bool}

law le_add_r:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}

law le_add_l:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}

law le_add_cancel:
  for +c: Nat
  for +a: Nat
  for +b: Nat
  {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == Nat.is_le(a, b) : Bool}

law le_add_mono:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for cd: {Nat.is_le(c, d) == True{} : Bool}
  {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}

law le_mul_mono_l:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}

law le_mul_mono_r:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Nat.mul(c, a), Nat.mul(c, b)) == True{} : Bool}
