# Independent reference for the verify-attention split/combine partition (attn_split.bend).
# A verify round appends q_len rows after `depth` cached positions; query row qpos < q_len sits at
# absolute position depth + qpos and must attend to exactly the kv positions p <= depth + qpos
# (causal, positions of the same round included up to itself), each exactly once.
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
