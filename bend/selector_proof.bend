# Proofs for the selector-order, window-alignment and acceptance laws.
import Base
import ./selector.bend as Selector
import ./selector_spec.bend as Spec
import ./selector_laws.bend as Laws

# A value is never strictly less than itself; structural induction strips
# matching successors.
def lt_self(+v: Nat) -> {Nat.is_lt(v, v) == False{} : Bool}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      lt_self(p)

def Laws.first_max_tie(i, j, v):
  step = Equal.cong(
    Bool,
    Selector.Score,
    flag => Selector.better_pick(flag, Selector.Score{i, v}, Selector.Score{j, v}),
    Nat.is_lt(v, v),
    False{},
    lt_self(v),
  )
  Equal.trans(
    Selector.Score,
    Selector.better_pick(Nat.is_lt(v, v), Selector.Score{i, v}, Selector.Score{j, v}),
    Selector.better_pick(False{}, Selector.Score{i, v}, Selector.Score{j, v}),
    Selector.Score{i, v},
    step,
    {==},
  )

def Laws.fold_order():
  ({==}, {==})

def Laws.round_arithmetic():
  ({==}, ({==}, {==}))

def Laws.rounds_definition():
  ({==}, {==})
