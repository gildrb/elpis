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

# Shared-to-register refresh, NOT the global-to-shared copy policy. The selected
# K64/group128 specialization has two tiles per scale group and an even ring.
# This finite startup table is serialized once; no model enters the GPU hot path.
def scale_refresh(phase: Nat) -> Nat:
  Nat.sub(1n, Nat.mod(phase, 2n))

def scale_refresh_table(count: Nat, +phase: Nat) -> List<&2, Nat>:
  match count:
    case 0n:
      Nil{}
    case 1n+p:
      scale_refresh(phase) <> scale_refresh_table(p, 1n+phase)

# Selected M8/N128/K64, 128-thread, eight-stage BF16/U4B8 class only.
# The actual intra-CTA reduction reaches448 int4s, not nominal sh_red_size272;
# B dominates that temporal overlay. Keep the original >=51200 selector guard.
# This startup scalar changes reservation only, never geometry or copy traffic.
def selected_shared_bytes() -> Nat:
  b = Nat.mul(Nat.mul(8n, 256n), 16n)
  reduction = Nat.mul(448n, 16n)
  scales = Nat.mul(Nat.mul(8n, 16n), 16n)
  a = Nat.mul(Nat.mul(8n, 64n), 16n)
  Nat.add(Nat.max(b, reduction), Nat.add(scales, a))
