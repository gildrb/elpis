# Independent reference for the strided absolute-tile verify-attention partition (attn_stride.bend).
# A verify round appends q_len rows after `depth` cached positions; query row qpos < q_len sits at
# absolute position a = depth + qpos and must attend to exactly the kv positions p <= a (causal,
# positions of the same round included up to itself), each exactly once. For row invariance the
# kv positions are cut into absolute 64-token tiles [64 i, 64 i + 64) and tile i belongs to slot
# i mod S of a grid of S slots: everything the row's result is built from is a function of (S, a)
# alone, never of depth or q_len separately.
import Base

# Causal visibility of kv position p for the verify row at absolute position depth + qpos.
def sees(+p: Nat, +depth: Nat, +qpos: Nat) -> Bool:
  Nat.is_le(p, Nat.add(depth, qpos))

# Multiplicity a position must have in the softmax: once if visible, never otherwise.
def once(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

# Position p lies in absolute tile x + it S (the 64 positions from 64 (x + it S)) and the row at
# absolute position a sees it.
def abs_visit(+S: Nat, +x: Nat, +it: Nat, +p: Nat, +a: Nat) -> Bool:
  Bool.and(Nat.is_le(Nat.mul(Nat.add(x, Nat.mul(it, S)), 64n), p),
    Bool.and(Nat.is_lt(p, Nat.add(Nat.mul(Nat.add(x, Nat.mul(it, S)), 64n), 64n)), Nat.is_le(p, a)))

# Position p's tile p / 64 belongs to slot x (tile index mod S) and the row at absolute position a
# sees p.
def abs_in_slot(+S: Nat, +x: Nat, +p: Nat, +a: Nat) -> Bool:
  Bool.and(Nat.is_eq(Nat.mod(Nat.div(p, 64n), S), x), Nat.is_le(p, a))

# [s, s + 1, .., s + n - 1]
def range.go(n: Nat, +s: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+r:
      s <> range.go(r, 1n+s)

# The slots holding a position the row at absolute position a sees, in increasing order:
# 0 .. min(S - 1, a / 64).
def abs_slots(+S: Nat, +a: Nat) -> List<&2, Nat>:
  range.go(Nat.min(S, 1n+Nat.div(a, 64n)), 0n)

# Occurrences of j in xs
def count(+j: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      Nat.add(once(Nat.is_eq(x, j)), count(j, rest))

# Every j < n occurs exactly once in xs
def all_once(+n: Nat, +xs: List<&2, Nat>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+j:
      Bool.and(all_once(j, xs), Nat.is_eq(count(j, xs), 1n))
