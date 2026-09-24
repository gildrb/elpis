# Startup-only permission for inverse partner transport. This is deliberately
# independent of late_value, even while their current truth tables coincide.
import Base

def inverse_partner(head256: Bool, rows32: Bool) -> Nat:
  match head256:
    case False{}:
      0n
    case True{}:
      match rows32:
        case False{}:
          0n
        case True{}:
          1n

# Native index is (D == 256) + 2 * (ROWS == 32).
def table(+depth: Nat, +a: Bool, +b: Bool) -> List<&2, Nat>:
  match depth:
    case 0n:
      [inverse_partner(a, b)]
    case 1n+p:
      left right = table(p, False{}, a) table(p, True{}, a)
      List.append(&2, Nat, left, right)
