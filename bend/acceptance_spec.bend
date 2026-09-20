# Independent left-to-right first-mismatch semantics. Acceptance supplies only
# the shared Tree datatype; none of its executable decision functions is used.
import Base
import ./acceptance.bend as Acceptance

# Continuation is counted only when every comparison matched. The production
# reference uses zero; generalizing it enables the structural concatenation law.
def scan(bits: List<&2, Bool>, continuation: Nat) -> Nat:
  match bits:
    case Nil{}:
      continuation
    case False{} <> rest:
      0n
    case True{} <> rest:
      1n+scan(rest, continuation)

def prefix(bits: List<&2, Bool>) -> Nat:
  scan(bits, 0n)

def flatten(tree: Acceptance.Tree) -> List<&2, Bool>:
  match tree:
    case Acceptance.Empty{}:
      Nil{}
    case Acceptance.Bit{equal}:
      [equal]
    case Acceptance.Fork{left, right}:
      List.append(&2, Bool, flatten(left), flatten(right))

# Low bit first, independently decoded by a sequential divide-by-two loop.
def bits(n: Nat, +mask: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Nat.is_eq(Nat.mod(mask, 2n), 1n) <> bits(p, Nat.div(mask, 2n))

def table(n: Nat, +start: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      prefix(bits(7n, start)) <> table(p, 1n+start)

def rows(values: List<&2, Nat>) -> String:
  match values:
    case Nil{}:
      ""
    case value <> rest:
      Nat.show(value) ++ "\n" ++ rows(rest)

def protocol() -> String:
  "QWEN_DFLASH_ACCEPT_V1\n7\n128\n" ++ rows(table(128n, 0n)) ++
    "END_QWEN_DFLASH_ACCEPT"
