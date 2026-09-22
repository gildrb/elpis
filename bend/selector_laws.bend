# Laws for the selector-order, window-alignment and acceptance-round
# lessons imported from the validated native DFlash2 stack.
import Base
import ./selector.bend as Selector
import ./selector_spec.bend as Spec

# First max on ties: equal values keep the first argument, whatever the
# indices. The CUDA walk resolves ties to the earliest lane.
law first_max_tie:
  for +i: Nat
  for +j: Nat
  for +v: Nat
  {Selector.better(Selector.Score{i, v}, Selector.Score{j, v}) == Selector.Score{i, v} : Selector.Score}

# The balanced parallel fold keeps left-first tie order, agreeing with the
# sequential walk on the two-leaf tree and on the left-fold order of three.
law fold_order:
  {Selector.reduce(Selector.build(1n, 0n)) == Selector.Score{1n, 1n} : Selector.Score}
  & {Selector.walk_seq([Selector.Score{1n, 1n}], Selector.Score{0n, 0n})
    == Selector.Score{1n, 1n} : Selector.Score}

# Every verify round emits the accepted proposals plus exactly one target
# token, and block 8 proposes exactly seven drafts with an eight-row window.
law round_arithmetic:
  {Selector.proposals() == 7n : Nat}
  & {Selector.window_rows() == 8n : Nat}
  & {Spec.emitted(7n) == 8n : Nat}

# Acceptance bookkeeping: rounds = new_tokens - accepted when at least one
# round happened, undefined when none did.
law rounds_definition:
  {Selector.rounds(5n, 2n) == Some{3n} : Maybe<&2, Nat>}
  & {Selector.rounds(5n, 5n) == None{} : Maybe<&2, Nat>}
