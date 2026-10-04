# Shared Nat order / arithmetic lemma vocabulary for proof modules.
#
# Use: `import ./nat_order_laws.bend as NO` plus `import ./nat_order_proof.bend as NOP` (the proof
# module must be in scope for the laws to count as proven), then call e.g. NO.le_trans(a, b, c, ab, bc).
# All laws are over Base's unary Nat (Nat.add / Nat.mul / Nat.sub truncated / Nat.is_le) and Bool.and;
# every one is proven generically by structural induction in nat_order_proof.bend (no @unsafe, no axioms).
# A "le(a, b)" below abbreviates the proposition {Nat.is_le(a, b) == True{} : Bool}.
#
#   Bool:     false_true (False == True gives Empty), and_l, and_r, and_intro
#   add:      add_zero_r, add_succ_r, add_comm, add_assoc ((a+b)+c == a+(b+c)),
#             add_swap (a+(b+c) == b+(a+c)), add_swap4 ((a+b)+(c+d) == (a+c)+(b+d))
#   mul:      mul_zero_r, mul_succ_r, mul_comm, mul_assoc ((a*b)*c == a*(b*c)),
#             mul_add_l ((a+b)*c == a*c+b*c), mul_add_r (a*(b+c) == a*b+a*c)
#   sub:      sub_self (a-a == 0), sub_add (b <= a: b+(a-b) == a), add_sub ((a+b)-a == b),
#             sub_add_add (c <= a, d <= b: (a+b)-(c+d) == (a-c)+(b-d)),
#             sub_chain (a <= b <= c: c-a == (c-b)+(b-a))
#   order:    le_zero (0 <= n), le_succ (n <= 1+n), le_refl, le_trans, le_of_eq (a == b: le(a, b)),
#             le_add_r (a <= a+b), le_add_l (b <= a+b), le_add_cancel (is_le(c+a, c+b) == is_le(a, b)),
#             le_add_mono (a <= b, c <= d: a+c <= b+d), le_mul_mono_l (a <= b: a*c <= b*c),
#             le_mul_mono_r (a <= b: c*a <= c*b)
import Base

# The proposition "b holds": Unit for True, Empty for False (motive for refuting False == True).
def Truth(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit
