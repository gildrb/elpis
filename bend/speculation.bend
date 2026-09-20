# Greedy DFLASH decisions are computed, not stored as an answer table. The
# native leaf consumes seven scalar comparisons without a heap collection.
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

# Ordered comparisons candidate[j+1] == target_top1[j]. Each mismatch
# discards the remaining scalar flags; only the uninterrupted prefix counts.
# Reuse the checked constructor so all four fields retain the same meaning.
def decide7(m0: Bool, m1: Bool, m2: Bool, m3: Bool, m4: Bool, m5: Bool,
    m6: Bool) -> Spec.Decision:
  match m0:
    case False{}:
      decision(0n)
    case True{}:
      match m1:
        case False{}:
          decision(1n)
        case True{}:
          match m2:
            case False{}:
              decision(2n)
            case True{}:
              match m3:
                case False{}:
                  decision(3n)
                case True{}:
                  match m4:
                    case False{}:
                      decision(4n)
                    case True{}:
                      match m5:
                        case False{}:
                          decision(5n)
                        case True{}:
                          match m6:
                            case False{}:
                              decision(6n)
                            case True{}:
                              decision(7n)

# Choose the most significant bit first, shifting it through seven scalar
# registers. False-before-true traversal emits ascending masks; the leaf's
# first argument is the least significant bit. Both parallel forks retain
# exactly 2^p leaves. Only the CPU wire output itself is a list.
def table(+depth: Nat, +m0: Bool, +m1: Bool, +m2: Bool, +m3: Bool,
    +m4: Bool, +m5: Bool, +m6: Bool) -> List<&2, Spec.Decision>:
  match depth:
    case 0n:
      [decide7(m0, m1, m2, m3, m4, m5, m6)]
    case 1n+p:
      left right = table(p, False{}, m0, m1, m2, m3, m4, m5) table(p, True{}, m0, m1, m2, m3, m4, m5)
      List.append(&2, Spec.Decision, left, right)

def decisions() -> List<&2, Spec.Decision>:
  table(7n, False{}, False{}, False{}, False{}, False{}, False{}, False{})
