# Startup-only forward transport stage count, independent of inverse permission.
import Base

def forward_partner_stages(head256: Bool, rows32: Bool) -> Nat:
  match head256:
    case False{}:
      0n
    case True{}:
      match rows32:
        case False{}:
          0n
        case True{}:
          3n

# Native index is (D == 256) + 2 * (ROWS == 32).
def table(+depth: Nat, +a: Bool, +b: Bool) -> List<&2, Nat>:
  match depth:
    case 0n:
      [forward_partner_stages(a, b)]
    case 1n+p:
      left right = table(p, False{}, a) table(p, True{}, a)
      List.append(&2, Nat, left, right)
