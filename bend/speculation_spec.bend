# Independent sequential semantics for greedy speculative execution.
# Counts distinguish accepted proposals, materialized inputs, and the bonus.
# CUDA comparisons, table addressing, model logits, and physical speed require
# separate refinement/numerical/measurement evidence; they are not this proof.
import Base

type Decision is Data:
  Decision{accepted: Nat, committed: Nat, bonus: Nat, advance: Nat}

# Provenance distinguishes an emitted target bonus from a materialized input,
# even when their token IDs happen to be equal.
type Source is Data:
  Input{slot: Nat}
  Bonus{target_slot: Nat}

def proposals(count: Nat, +start: Nat) -> List<&2, Source>:
  match count:
    case 0n:
      Nil{}
    case 1n+p:
      Input{start} <> proposals(p, 1n+start)

def length(xs: List<&2, Source>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      1n+length(t)

def committed(accepted: Nat) -> List<&2, Source>:
  Input{0n} <> proposals(accepted, 1n)

def emitted(+accepted: Nat) -> List<&2, Source>:
  List.append(&2, Source, proposals(accepted, 1n), [Bonus{accepted}])

def inputs_only(xs: List<&2, Source>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      match h:
        case Input{slot}:
          inputs_only(t)
        case Bonus{target_slot}:
          False{}

def take(count: Nat, xs: List<&2, Source>) -> List<&2, Source>:
  match count:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case h <> t:
          h <> take(p, t)

def materialized(+accepted: Nat, rejected: List<&2, Source>) -> List<&2, Source>:
  Input{0n} <> List.append(&2, Source, proposals(accepted, 1n), rejected)

def accepted_count(value: Decision) -> Nat:
  Decision{naccepted, ncommitted, nbonus, nadvance} = value
  naccepted

def commit_count(value: Decision) -> Nat:
  Decision{naccepted, ncommitted, nbonus, nadvance} = value
  ncommitted

def bonus_index(value: Decision) -> Nat:
  Decision{naccepted, ncommitted, nbonus, nadvance} = value
  nbonus

def advance_count(value: Decision) -> Nat:
  Decision{naccepted, ncommitted, nbonus, nadvance} = value
  nadvance

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
  Decision{accepted, length(committed(accepted)),
    length(proposals(accepted, 1n)), length(emitted(accepted))}

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
    case Decision{naccepted, ncommitted, nbonus, nadvance}:
      Nat.show(naccepted) ++ "\n" ++ Nat.show(ncommitted) ++ "\n" ++
        Nat.show(nbonus) ++ "\n" ++ Nat.show(nadvance) ++ "\n"

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
