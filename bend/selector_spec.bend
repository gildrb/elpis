# Independent reference for the selector-order and window lessons. Walks
# scores in plain index order with an explicit strict-greater comparison and
# never shares code with the balanced implementation.
import Base

type Ref is Data:
  Ref{+index: Nat, +value: Nat}

# The candidate replaces the incumbent only on a strictly greater value; an
# equal value keeps the earlier index (first max on ties).
def pick_bool(flag: Bool, +head: Ref, +best: Ref) -> Ref:
  match flag:
    case True{}:
      head
    case False{}:
      best

def pick2(+head: Ref, +best: Ref) -> Ref:
  Ref{bi, bv} = head
  Ref{ai, av} = best
  pick_bool(Nat.is_lt(av, bv), head, best)

def scan(xs: List<&2, Ref>, +best: Ref) -> Ref:
  match xs:
    case Nil{}:
      best
    case head <> rest:
      scan(rest, pick2(head, best))

# The reference accepts any proposal count; alignment is checked separately.
def emitted(+proposals: Nat) -> Nat:
  Nat.add(proposals, 1n)
