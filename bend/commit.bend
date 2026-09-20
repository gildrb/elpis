# Pure DFLASH block8 planning: one materialized anchor and seven proposals.
# The bonus is emitted, but has not yet been materialized in KV.
import Base
import ./range.bend as Range

type Plan is Data:
  Plan{commit_length: Nat, bonus_index: Nat}

def row(+accepted: Nat) -> Plan:
  Plan{1n+accepted, accepted}

def choose(valid: Bool, value: Plan) -> Maybe<&2, Plan>:
  match valid:
    case False{}:
      None{}
    case True{}:
      Some{value}

def plan(+accepted: Nat) -> Maybe<&2, Plan>:
  choose(Nat.is_le(accepted, 7n), row(accepted))

def commit_length(value: Plan) -> Nat:
  Plan{length, bonus} = value
  length

def bonus_index(value: Plan) -> Nat:
  Plan{length, bonus} = value
  bonus

def singleton(value: Maybe<&2, Plan>) -> Maybe<&2, List<&2, Plan>>:
  match value:
    case None{}:
      None{}
    case Some{p}:
      Some{[p]}

def join(left: Maybe<&2, List<&2, Plan>>, right: Maybe<&2, List<&2, Plan>>) -> Maybe<&2, List<&2, Plan>>:
  match left:
    case None{}:
      None{}
    case Some{xs}:
      match right:
        case None{}:
          None{}
        case Some{ys}:
          Some{List.append(&2, Plan, xs, ys)}

# Each child owns exactly half the rows, and every leaf calls the checked
# decision function. An invalid range fails, rather than dropping a row.
def tree(depth: Nat, +start: Nat) -> Maybe<&2, List<&2, Plan>>:
  match depth:
    case 0n:
      singleton(plan(start))
    case 1n++p:
      left right = tree(p, start) tree(p, Nat.add(Range.width(p), start))
      join(left, right)

def table() -> Maybe<&2, List<&2, Plan>>:
  tree(3n, 0n)
