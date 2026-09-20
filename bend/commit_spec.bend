# Reference semantics uses provenance, not token equality: an emitted bonus
# could equal an input numerically and still has no materialized KV slot.
# This specifies index decisions only, not GPU arithmetic or recurrent state.
import Base
import ./commit.bend as Commit

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

# A full verified input buffer has the anchor, the accepted proposal prefix,
# and an arbitrary rejected suffix. It never contains the future bonus.
def materialized(+accepted: Nat, rejected: List<&2, Source>) -> List<&2, Source>:
  Input{0n} <> List.append(&2, Source, proposals(accepted, 1n), rejected)

# Independently count the input sequence to commit and the output prefix
# before the bonus. Neither field copies the implementation's arithmetic.
def row(+accepted: Nat) -> Commit.Plan:
  Commit.Plan{length(committed(accepted)), length(proposals(accepted, 1n))}

def choose(valid: Bool, value: Commit.Plan) -> Maybe<&2, Commit.Plan>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{value}

def plan(+accepted: Nat) -> Maybe<&2, Commit.Plan>:
  choose(Nat.is_le(accepted, 7n), row(accepted))
