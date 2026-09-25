# Multi-round extension of the GDN verify / commit-replay model (bend/gdn_replay.bend): a job runs
# any number of greedy speculative rounds, each a history-free verify of its window + 1 inputs from
# the committed state followed by the commit (batched_state_replay of the accepted count, conv
# tail write and rewind) of Impl.round. The rounds may cut the committed token stream anywhere and
# their rejected inputs are arbitrary. Same opaque step / out / state / input types as
# gdn_replay.bend. Reference: gdn_rounds_spec.bend; laws: gdn_rounds_laws.bend.
import Base
import ./gdn_replay.bend as GR
import ./exl3_accept_spec.bend as Accept

# One non-eos round: its window, rule inputs xs and conv inputs ys (window + 1 each, drafts
# included) and the accepted count of the greedy acceptance leaf.
type Round<-X: Data, -Y: Data> is Data:
  Round{window: Nat, xs: List<&2, X>, ys: List<&2, Y>, count: Nat}

# The rounds in commit order, each on the outcome the previous one committed.
def run(~S: Data, ~X: Data, ~Y: Data, ~step: S -> X -> S, +K: Nat, +H: Nat,
    rounds: List<&2, Round<X, Y>>, o: GR.Outcome<S, Y>) -> GR.Outcome<S, Y>:
  match rounds:
    case Nil{}:
      o
    case Round{window, xs, ys, count} <> rest:
      run(~S, ~X, ~Y, ~step, K, H, rest, GR.round_after(~S, ~X, ~Y, ~step, K, H, o, window, xs, ys,
        Accept.Verdict{count, False{}}))

# The outputs the host keeps: the first count verify rows of every round, each verify started
# from the row 0 state the previous rounds committed.
def emitted(~S: Data, ~X: Data, ~Y: Data, ~O: Data, ~step: S -> X -> S, ~out: S -> X -> O,
    +K: Nat, +H: Nat, rounds: List<&2, Round<X, Y>>, +o: GR.Outcome<S, Y>) -> List<&2, O>:
  match rounds:
    case Nil{}:
      Nil{}
    case Round{+window, +xs, +ys, +count} <> rest:
      List.append(&2, O, List.take(&2, O, GR.verify(~S, ~X, ~O, ~step, ~out, xs, GR.row0_of(~S, ~Y, o)), count),
        emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rest,
          GR.round_after(~S, ~X, ~Y, ~step, K, H, o, window, xs, ys, Accept.Verdict{count, False{}})))

# The engine's shape and range facts for one round (gdn_replay_laws domains): window + 1 rule and
# conv inputs, 1 <= window <= max_history, 1 <= count <= window + 1.
def round_ok(~X: Data, ~Y: Data, +H: Nat, r: Round<X, Y>) -> Bool:
  match r:
    case Round{+window, xs, ys, +count}:
      Bool.and(Nat.is_eq(List.length(&2, X, xs), 1n+window),
        Bool.and(Nat.is_eq(List.length(&2, Y, ys), 1n+window),
          Bool.and(Nat.is_le(1n, window),
            Bool.and(Nat.is_le(window, H),
              Bool.and(Nat.is_le(1n, count), Nat.is_le(count, 1n+window))))))

def rounds_ok(~X: Data, ~Y: Data, +H: Nat, rounds: List<&2, Round<X, Y>>) -> Bool:
  match rounds:
    case Nil{}:
      True{}
    case r <> rest:
      Bool.and(round_ok(~X, ~Y, H, r), rounds_ok(~X, ~Y, H, rest))

# ---- Mutation model (NOT the engine). A commit replay whose per-token update differs from the
# verify kernel's: every replayed token applies `step` twice, the same change as the literal
# mutation of GR.replay recorded for gdn_rounds_laws.replay_step_mismatch_differs. Only that law
# uses it; run / emitted and every other law use GR.replay.
def replay_mut(~S: Data, ~X: Data, ~step: S -> X -> S, steps: Nat, xs: List<&2, X>, s: S) -> S:
  match steps:
    case 0n:
      s
    case 1n+more:
      match xs:
        case Nil{}:
          s
        case +x <> rest:
          replay_mut(~S, ~X, ~step, more, rest, step(step(s, x), x))

# Concrete per-token update and readout for that witness: S = X = O = Nat, the state is the
# running sum and each row reads out the state.
def wit_step(s: Nat, x: Nat) -> Nat:
  Nat.add(s, x)

def wit_out(s: Nat, x: Nat) -> Nat:
  s
