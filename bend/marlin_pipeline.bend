# Compiled startup policy only; native supplies the three observed predicates.
# The table action is the sole stage override selector: 0 keeps the validated
# four-stage kernel; 1 selects the identical geometry with eight copy stages.
# No copy-ring/list trace/proof model is reachable from this production module.
import Base

def policy(eligible: Bool, safe: Bool, deterministic: Bool) -> Nat:
  match eligible:
    case False{}:
      0n
    case True{}:
      match safe:
        case False{}:
          0n
        case True{}:
          match deterministic:
            case False{}:
              0n
            case True{}:
              1n

# Existing balanced finite-control enumeration. At depth three, row i observes
# eligible=(i&1), safe=(i&2), deterministic=(i&4), in ascending index order.
# The eight short rows are consumed sequentially by startup serialization only.
def table(+depth: Nat, +a: Bool, +b: Bool, +c: Bool) -> List<&2, Nat>:
  match depth:
    case 0n:
      [policy(a, b, c)]
    case 1n+p:
      left right = table(p, False{}, a, b) table(p, True{}, a, b)
      List.append(&2, Nat, left, right)
