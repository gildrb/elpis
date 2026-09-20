# Greedy DFLASH decisions are computed, not stored as an answer table. The
# structurally decreasing list leads the accumulator so every call terminates.
import Base
import ./speculation_spec.bend as Spec

# Count only the uninterrupted initial matches. A false discards the suffix;
# later matches can never resurrect a rejected proposal.
def scan(flags: List<&2, Bool>, accepted: Nat) -> Nat:
  match flags:
    case Nil{}:
      accepted
    case False{} <> rest:
      accepted
    case True{} <> rest:
      scan(rest, 1n+accepted)

# The anchor is committed with accepted proposals. The bonus is an output
# token, not an additional committed input: both counts advance by a + 1.
def decision(+accepted: Nat) -> Spec.Decision:
  Spec.Decision{accepted, 1n+accepted, accepted, 1n+accepted}

def decide(flags: List<&2, Bool>) -> Spec.Decision:
  decision(scan(flags, 0n))

# Each level chooses the next most significant bit. Prepending reverses that
# choice order, so each leaf receives the comparison flags least significant
# bit first. False-before-true traversal emits ascending masks. Both forks have
# exactly 2^p leaves, and decisions are evaluated inside those parallel calls.
def table(+depth: Nat, +suffix: List<&2, Bool>) -> List<&2, Spec.Decision>:
  match depth:
    case 0n:
      [decide(suffix)]
    case 1n+p:
      left right = table(p, False{} <> suffix) table(p, True{} <> suffix)
      List.append(&2, Spec.Decision, left, right)

def decisions() -> List<&2, Spec.Decision>:
  table(7n, Nil{})
