# Independent sequential semantics for greedy speculative execution.
# Counts distinguish accepted proposals, materialized inputs, and the bonus.
# CUDA comparisons, table addressing, model logits, and physical speed require
# separate refinement/numerical/measurement evidence; they are not this proof.
import Base

type Decision is Data:
  Decision{accepted: Nat, committed: Nat, bonus: Nat, advance: Nat}

# Stop at the first mismatch, even if later proposed tokens match again.
def prefix(flags: List<&2, Bool>) -> Nat:
  match flags:
    case Nil{}:
      0n
    case False{} <> rest:
      0n
    case True{} <> rest:
      1n+prefix(rest)

# The anchor and accepted proposals are materialized. The target bonus is
# emitted at slot a, but is not materialized as an input in this step.
def decision(+accepted: Nat) -> Decision:
  Decision{accepted, 1n+accepted, accepted, 1n+accepted}

def decide(flags: List<&2, Bool>) -> Decision:
  decision(prefix(flags))

# Independent arithmetic decoding, unlike the implementation's binary tree.
# The low bit denotes candidate[1] == target_top1[0].
def flags(width: Nat, +mask: Nat) -> List<&2, Bool>:
  match width:
    case 0n:
      Nil{}
    case 1n+p:
      Nat.is_ne(Nat.mod(mask, 2n), 0n) <> flags(p, Nat.div(mask, 2n))

def render(value: Decision) -> String:
  match value:
    case Decision{accepted, committed, bonus, advance}:
      Nat.show(accepted) ++ "\n" ++ Nat.show(committed) ++ "\n" ++
        Nat.show(bonus) ++ "\n" ++ Nat.show(advance) ++ "\n"

# Simple forward enumeration defines the external row order independently
# of the optimized, balanced parallel table generator.
def rows(count: Nat, +index: Nat) -> String:
  match count:
    case 0n:
      ""
    case 1n+p:
      render(decide(flags(7n, index))) ++ rows(p, 1n+index)

def protocol() -> String:
  "QWEN_DFLASH_GREEDY_V1\n8\n128\n4\n" ++ rows(128n, 0n) ++
    "END_QWEN_DFLASH_GREEDY"
