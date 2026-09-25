# Round-level model of greedy speculative decoding in the EXL3 + DFlash2 serving loop, for the
# speculation-invariance theorem (laws: spec_inv_laws.bend, reference: spec_inv_spec.bend).
#
# The target is abstracted to its per-row output: row(p, r) is the argmax token the verify
# forward produces for a row whose absolute prefix (prompt, committed tokens and the round's
# drafts up to and including the row's own input) is p, when that row is row r of its round.
# A round verifies window + 1 rows: row 0's input is the last committed token (the anchor), row
# j >= 1's input is draft d_j, so row j's prefix is the committed sequence followed by d_1 .. d_j.
# The verdict is the EXL3 acceptance reference (exl3_accept_spec.bend, proven equal to the
# executed leaf by Exl3AcceptLaws.leaf_refinement) on those targets, the drafts, the stop ids,
# the job's remaining budget and the device checkpoint; the device state then advances by the
# advance kernel of exl3_round.bend, and the host emits the first count verify ids
# (Exl3RoundSpec.committed). The drafts of every round are an arbitrary list: every drafter,
# adaptive or adversarial, produces some such list per round, so a law quantified over all of
# them covers every drafter. This is a proof model (lists), not a shipped artifact.
import Base
import ./exl3_accept_spec.bend as Accept
import ./exl3_round.bend as Round
import ./exl3_round_spec.bend as RoundSpec

# Rows 1 .. k of a round: row j sees the prefix extended by d_1 .. d_j.
def rows_after(~row: List<&2, U32> -> Nat -> U32, ds: List<&2, U32>, +seq: List<&2, U32>,
    +r: Nat) -> List<&2, U32>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> rest:
      +next = List.append(&2, U32, seq, [d])
      row(next, 1n+r) <> rows_after(~row, rest, next, 1n+r)

# The verify ids of a round from committed sequence seq with drafts ds: k + 1 targets, row 0 first
# (r is the row index of the first row; a round starts at row 0).
def targets(~row: List<&2, U32> -> Nat -> U32, ds: List<&2, U32>, +seq: List<&2, U32>,
    +r: Nat) -> List<&2, U32>:
  row(seq, r) <> rows_after(~row, ds, seq, r)

# The job: device round state (exl3_round.bend) and the tokens emitted so far.
type Run is Data:
  Run{st: Round.State, out: List<&2, U32>}

def out(r: Run) -> List<&2, U32>:
  match r:
    case Run{st, o}:
      o

def stopped(r: Run) -> Bool:
  match r:
    case Run{st, o}:
      Round.stopped(st)

def budget(r: Run) -> Nat:
  match r:
    case Run{st, o}:
      Round.budget(st)

# One round: verify, accept, advance the device state (window = number of drafts), emit the
# committed prefix of the verify ids (nothing once the job has stopped).
def round(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>,
    +base: Nat, +interval: Nat, +ds: List<&2, U32>, r: Run) -> Run:
  match r:
    case Run{+st, +o}:
      +ts = targets(~row, ds, List.append(&2, U32, prompt, o), 0n)
      +v = Accept.accept(ts, ds, stops, Round.budget(st), Round.checkpoint_of(st))
      Run{Round.advance(Accept.count(v), Accept.eos(v), List.length(&2, U32, ds), base, interval, st),
        List.append(&2, U32, o, RoundSpec.committed(ts, Accept.count(v), Round.stopped(st)))}

# The rounds in order, one draft list per round.
def run(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>,
    +base: Nat, +interval: Nat, drafts: List<&2, List<&2, U32>>, r: Run) -> Run:
  match drafts:
    case Nil{}:
      r
    case +ds <> rest:
      run(~row, prompt, stops, base, interval, rest, round(~row, prompt, stops, base, interval, ds, r))

# A job: a running device state (any position, anchor and checkpoint input, the output budget)
# with nothing emitted yet, then the rounds.
def job(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>,
    +base: Nat, +interval: Nat, drafts: List<&2, List<&2, U32>>, +position: Nat, +budget: Nat,
    +anchor: Nat, +checkpoint: Nat) -> Run:
  run(~row, prompt, stops, base, interval, drafts,
    Run{Round.State{position, budget, anchor, checkpoint, False{}}, Nil{}})

# Mutation model (not the engine): a target whose row output leaks the row index (row 0 answers
# 0, every later row answers 1), i.e. a per-row result that depends on where the row sits in
# its round instead of on its absolute prefix. Used only by the witness law row_index_leak_differs.
def leak(p: List<&2, U32>, r: Nat) -> U32:
  match r:
    case 0n:
      0
    case 1n+s:
      1
