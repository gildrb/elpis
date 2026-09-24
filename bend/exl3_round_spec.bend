# Independent reference for what one verify round commits, stated on the
# committed token prefix rather than on the advance kernel's arithmetic.
# The round's verdict comes from the EXL3 acceptance reference
# (exl3_accept_spec.bend), which is reused, not restated.
import Base
import ./exl3_accept_spec.bend as Accept

# Tokens the host emits for this round: the first count verify ids, or
# nothing once the job has stopped (eos, error) in an earlier round.
def committed(targets: List<&2, U32>, count: Nat, stopped: Bool)
  -> List<&2, U32>:
  match stopped:
    case True{}:
      Nil{}
    case False{}:
      List.take(&2, U32, targets, count)

# Verified ids the round did not commit (the rejected draft suffix).
def uncommitted(targets: List<&2, U32>, count: Nat) -> List<&2, U32>:
  List.drop(&2, U32, targets, count)

# The engine's decode-branch recurrent checkpoint boundary
# (job.is_checkpoint_boundary, job.py:1577) at K/V position p.
def boundary(p: Nat, +base: Nat, +interval: Nat) -> Bool:
  Nat.is_eq(Nat.mod(Nat.sub(p, base), interval), 0n)

# Some position position + 1 .. position + m is a boundary.
def within(+m: Nat, +position: Nat, +base: Nat, +interval: Nat) -> Bool:
  match m:
    case 0n:
      False{}
    case 1n+rest:
      Bool.or(boundary(Nat.add(position, 1n+rest), base, interval),
        within(rest, position, base, interval))

# Committing count tokens from position crosses a boundary when one lies
# strictly inside (position, position + count): the round would have
# passed a checkpoint without stopping on it. Ending on one is allowed.
def crosses(count: Nat, +position: Nat, +base: Nat, +interval: Nat) -> Bool:
  within(Nat.sub(count, 1n), position, base, interval)

def found(hit: Bool, j: Nat, rest: Nat) -> Nat:
  match hit:
    case True{}:
      j
    case False{}:
      rest

# The first j in start .. start + fuel - 1 with a boundary at position + j,
# else 0.
def first(fuel: Nat, +start: Nat, +position: Nat, +base: Nat,
    +interval: Nat) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+more:
      found(boundary(Nat.add(position, start), base, interval), start,
        first(more, 1n+start, position, base, interval))

# _greedy_checkpoint's contract (generator.py:991-995): the committed count
# in 1..window after which the position first is a boundary, or 0.
def checkpoint(+position: Nat, +base: Nat, +interval: Nat, window: Nat)
  -> Nat:
  first(window, 1n, position, base, interval)
