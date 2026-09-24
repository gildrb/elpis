# Startup-only finite selector. Native observes the existing D/ROWS constexpr
# predicates; no attention expression/proof model enters this runtime graph.
import Base

def late_value(head256: Bool, rows32: Bool) -> Nat:
  match head256:
    case False{}:
      0n
    case True{}:
      match rows32:
        case False{}:
          0n
        case True{}:
          1n

# Same balanced finite enumeration as the other shipped startup controls.
# At depth two, head256 is bit 0 and rows32 bit 1: rows [0,0,0,1].
def table(+depth: Nat, +a: Bool, +b: Bool) -> List<&2, Nat>:
  match depth:
    case 0n:
      [late_value(a, b)]
    case 1n+p:
      left right = table(p, False{}, a) table(p, True{}, a)
      List.append(&2, Nat, left, right)
