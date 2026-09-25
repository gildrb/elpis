# Laws of the multi-round GDN model (bend/gdn_rounds.bend) against the uninterrupted-scan
# reference (bend/gdn_rounds_spec.bend over bend/gdn_replay_spec.bend). `step` and `out` are
# template parameters: every law holds for every per-token update and readout and for every state
# / input / output type. Domain: any list of non-eos rounds (any cut of the committed stream into
# rounds, any rejected draft inputs) within the gdn_replay_laws domains (rounds_ok: window + 1
# rule / conv inputs, 1 <= window <= max_history, 1 <= count <= window + 1); the conv law also
# needs the K + H column buffer. An eos round ends the job (gdn_replay_laws.commit_eos).
import Base
import ./gdn_rounds.bend as Impl
import ./gdn_rounds_spec.bend as Spec
import ./gdn_replay.bend as GR
import ./gdn_replay_spec.bend as GS
import ./exl3_accept_spec.bend as Accept

# C1: whatever the round boundaries, the committed row 0 state is the fold over the committed
# stream, every kept output is the readout of one uninterrupted scan over that stream (the state
# before token i and its output), the next round's verify rows are that scan continued, every
# round commits, and the position counts the committed tokens.
law split_point_state:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~O: Data
  for ~step: S -> X -> S
  for ~out: S -> X -> O
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +rounds: List<&2, Impl.Round<X, Y>>
  for +next: List<&2, X>
  for ok: {Impl.rounds_ok(~X, ~Y, H, rounds) == True{} : Bool}
  {GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, GR.Committed{GR.Engine{s0, buf, position, lh}})) ==
    GS.fold(~S, ~X, ~step, Spec.stream_x(~X, ~Y, rounds), s0) : S} &
  {Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds, GR.Committed{GR.Engine{s0, buf, position, lh}}) ==
    GS.outputs(~S, ~X, ~O, ~step, ~out, Spec.stream_x(~X, ~Y, rounds), s0, Nil{}) : List<&2, O>} &
  {GR.verify(~S, ~X, ~O, ~step, ~out, next,
      GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, GR.Committed{GR.Engine{s0, buf, position, lh}}))) ==
    GS.outputs(~S, ~X, ~O, ~step, ~out, next, s0, Spec.stream_x(~X, ~Y, rounds)) : List<&2, O>} &
  {GR.committed(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, GR.Committed{GR.Engine{s0, buf, position, lh}})) == True{} : Bool} &
  {GR.position_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, GR.Committed{GR.Engine{s0, buf, position, lh}})) ==
    Nat.add(position, Spec.committed(~X, ~Y, rounds)) : Nat}

# C2: whatever the round boundaries, the conv window (columns [0, K)) is the last K of the initial
# window followed by every committed conv input, the buffer keeps its K + H columns, and the conv
# input window of the next round's token j (window followed by the round's first j conv inputs) is
# the last K of everything committed followed by those j inputs.
law conv_window_rounds:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~step: S -> X -> S
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +rounds: List<&2, Impl.Round<X, Y>>
  for +next_y: List<&2, Y>
  for +j: Nat
  for shaped_buf: {List.length(&2, Y, buf) == Nat.add(K, H) : Nat}
  for ok: {Impl.rounds_ok(~X, ~Y, H, rounds) == True{} : Bool}
  {List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, GR.Committed{GR.Engine{s0, buf, position, lh}})), K) ==
    GS.last(~Y, K, List.append(&2, Y, List.take(&2, Y, buf, K), Spec.stream_y(~X, ~Y, rounds))) : List<&2, Y>} &
  {List.length(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, GR.Committed{GR.Engine{s0, buf, position, lh}}))) ==
    Nat.add(K, H) : Nat} &
  {GS.last(~Y, K, List.append(&2, Y,
      List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds, GR.Committed{GR.Engine{s0, buf, position, lh}})), K),
      List.take(&2, Y, next_y, j))) ==
    GS.last(~Y, K, List.append(&2, Y, List.append(&2, Y, List.take(&2, Y, buf, K), Spec.stream_y(~X, ~Y, rounds)),
      List.take(&2, Y, next_y, j))) : List<&2, Y>}

# C3: the verify kernel (RULE_VERIFY, patch 0003) and the commit replay (RULE_COMMIT, patch 0004)
# run the same per-token routine, so splitting a verify at any point c is invisible: the verify
# rows after the first c equal a fresh verify of the remaining inputs from the state the replay
# commits for c tokens, that state is the fold of the first c inputs, and the first c rows
# followed by that fresh verify are the whole verify. Domain: every step / out, state s, inputs
# xs and every c (c > length(xs) included: the replay then commits all of xs and both sides
# are empty after the split).
law verify_split_point:
  for ~S: Data
  for ~X: Data
  for ~O: Data
  for ~step: S -> X -> S
  for ~out: S -> X -> O
  for +xs: List<&2, X>
  for +s: S
  for +c: Nat
  {List.drop(&2, O, GR.verify(~S, ~X, ~O, ~step, ~out, xs, s), c) ==
    GR.verify(~S, ~X, ~O, ~step, ~out, List.drop(&2, X, xs, c), GR.replay(~S, ~X, ~step, c, xs, s)) : List<&2, O>} &
  {GR.replay(~S, ~X, ~step, c, xs, s) == GS.fold(~S, ~X, ~step, List.take(&2, X, xs, c), s) : S} &
  {List.append(&2, O, List.take(&2, O, GR.verify(~S, ~X, ~O, ~step, ~out, xs, s), c),
      GR.verify(~S, ~X, ~O, ~step, ~out, List.drop(&2, X, xs, c), GR.replay(~S, ~X, ~step, c, xs, s))) ==
    GR.verify(~S, ~X, ~O, ~step, ~out, xs, s) : List<&2, O>}

# C3 (engine): a non-eos round with accepted count c (checkpoint boundary, mismatch or bonus
# position) verifies its window + 1 inputs from row 0, then commits: the verify rows after the
# first c equal a fresh verify of the remaining inputs from the row 0 the round committed, that
# row 0 is the batched_state_replay of the first c inputs, and the c kept rows followed by the
# fresh verify are the in-round verify. Domain: the gdn_replay_laws.commit_prefix domain
# (window + 1 rule inputs, c <= window + 1, every window / K / H / conv buffer); it contains the
# engine's rounds (1 <= c <= window + 1, 1 <= window <= H). c = 0 is refused (commit_empty) and
# leaves row 0 untouched, which is the replay of 0 inputs.
law verify_split_round:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~O: Data
  for ~step: S -> X -> S
  for ~out: S -> X -> O
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +window: Nat
  for +xs: List<&2, X>
  for +ys: List<&2, Y>
  for +count: Nat
  for shaped_xs: {List.length(&2, X, xs) == 1n+window : Nat}
  for bounded: {Nat.is_le(count, 1n+window) == True{} : Bool}
  {List.drop(&2, O, GR.verify(~S, ~X, ~O, ~step, ~out, xs, s0), count) ==
    GR.verify(~S, ~X, ~O, ~step, ~out, List.drop(&2, X, xs, count),
      GR.row0_of(~S, ~Y, GR.round(~S, ~X, ~Y, ~step, K, H, GR.Engine{s0, buf, position, lh}, window, xs, ys,
        Accept.Verdict{count, False{}}))) : List<&2, O>} &
  {GR.row0_of(~S, ~Y, GR.round(~S, ~X, ~Y, ~step, K, H, GR.Engine{s0, buf, position, lh}, window, xs, ys,
      Accept.Verdict{count, False{}})) ==
    GR.replay(~S, ~X, ~step, count, xs, s0) : S} &
  {List.append(&2, O, List.take(&2, O, GR.verify(~S, ~X, ~O, ~step, ~out, xs, s0), count),
      GR.verify(~S, ~X, ~O, ~step, ~out, List.drop(&2, X, xs, count),
        GR.row0_of(~S, ~Y, GR.round(~S, ~X, ~Y, ~step, K, H, GR.Engine{s0, buf, position, lh}, window, xs, ys,
          Accept.Verdict{count, False{}})))) ==
    GR.verify(~S, ~X, ~O, ~step, ~out, xs, s0) : List<&2, O>}

# C4 (speculation invariance): two round schedules that commit the same rule-input stream from
# the same committed engine leave the same row 0 state, emit the same outputs, give the same
# verify rows for any next round's inputs and the same position, however the stream was cut
# into rounds and whatever drafts were rejected. Domain: both schedules within rounds_ok.
law two_schedules:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~O: Data
  for ~step: S -> X -> S
  for ~out: S -> X -> O
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +rounds1: List<&2, Impl.Round<X, Y>>
  for +rounds2: List<&2, Impl.Round<X, Y>>
  for +next: List<&2, X>
  for ok1: {Impl.rounds_ok(~X, ~Y, H, rounds1) == True{} : Bool}
  for ok2: {Impl.rounds_ok(~X, ~Y, H, rounds2) == True{} : Bool}
  for same_x: {Spec.stream_x(~X, ~Y, rounds1) == Spec.stream_x(~X, ~Y, rounds2) : List<&2, X>}
  {GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, GR.Committed{GR.Engine{s0, buf, position, lh}})) ==
    GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, GR.Committed{GR.Engine{s0, buf, position, lh}})) : S} &
  {Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds1, GR.Committed{GR.Engine{s0, buf, position, lh}}) ==
    Impl.emitted(~S, ~X, ~Y, ~O, ~step, ~out, K, H, rounds2, GR.Committed{GR.Engine{s0, buf, position, lh}}) : List<&2, O>} &
  {GR.verify(~S, ~X, ~O, ~step, ~out, next,
      GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, GR.Committed{GR.Engine{s0, buf, position, lh}}))) ==
    GR.verify(~S, ~X, ~O, ~step, ~out, next,
      GR.row0_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, GR.Committed{GR.Engine{s0, buf, position, lh}}))) : List<&2, O>} &
  {GR.position_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, GR.Committed{GR.Engine{s0, buf, position, lh}})) ==
    GR.position_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, GR.Committed{GR.Engine{s0, buf, position, lh}})) : Nat}

# C4 (conv): two round schedules that commit the same conv-input stream from the same committed
# engine with a K + H column buffer leave the same conv window (columns [0, K)), so the next
# round's token j sees the same conv input window. Domain: both schedules within rounds_ok.
law two_schedules_conv:
  for ~S: Data
  for ~X: Data
  for ~Y: Data
  for ~step: S -> X -> S
  for +K: Nat
  for +H: Nat
  for +s0: S
  for +buf: List<&2, Y>
  for +position: Nat
  for +lh: Nat
  for +rounds1: List<&2, Impl.Round<X, Y>>
  for +rounds2: List<&2, Impl.Round<X, Y>>
  for +next_y: List<&2, Y>
  for +j: Nat
  for shaped_buf: {List.length(&2, Y, buf) == Nat.add(K, H) : Nat}
  for ok1: {Impl.rounds_ok(~X, ~Y, H, rounds1) == True{} : Bool}
  for ok2: {Impl.rounds_ok(~X, ~Y, H, rounds2) == True{} : Bool}
  for same_y: {Spec.stream_y(~X, ~Y, rounds1) == Spec.stream_y(~X, ~Y, rounds2) : List<&2, Y>}
  {List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, GR.Committed{GR.Engine{s0, buf, position, lh}})), K) ==
    List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, GR.Committed{GR.Engine{s0, buf, position, lh}})), K) : List<&2, Y>} &
  {GS.last(~Y, K, List.append(&2, Y,
      List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds1, GR.Committed{GR.Engine{s0, buf, position, lh}})), K),
      List.take(&2, Y, next_y, j))) ==
    GS.last(~Y, K, List.append(&2, Y,
      List.take(&2, Y, GR.conv_of(~S, ~Y, Impl.run(~S, ~X, ~Y, ~step, K, H, rounds2, GR.Committed{GR.Engine{s0, buf, position, lh}})), K),
      List.take(&2, Y, next_y, j))) : List<&2, Y>}

# Mutation witness for C3: with S = X = O = Nat, step = running sum, out = the state, inputs
# [1, 2, 3] from state 0 and split point 1, the in-round verify rows after the split are [3, 6],
# the engine's replay followed by a fresh verify gives [3, 6], and the mutant replay of
# Impl.replay_mut (each token stepped twice) followed by the same fresh verify gives [4, 7],
# which differs: C3 rejects a commit replay whose per-token update differs from the verify's.
law replay_step_mismatch_differs:
  {List.drop(&2, Nat, GR.verify(~Nat, ~Nat, ~Nat, ~Impl.wit_step, ~Impl.wit_out, [1n, 2n, 3n], 0n), 1n) ==
    [3n, 6n] : List<&2, Nat>} &
  {GR.verify(~Nat, ~Nat, ~Nat, ~Impl.wit_step, ~Impl.wit_out, List.drop(&2, Nat, [1n, 2n, 3n], 1n),
      GR.replay(~Nat, ~Nat, ~Impl.wit_step, 1n, [1n, 2n, 3n], 0n)) == [3n, 6n] : List<&2, Nat>} &
  {GR.verify(~Nat, ~Nat, ~Nat, ~Impl.wit_step, ~Impl.wit_out, List.drop(&2, Nat, [1n, 2n, 3n], 1n),
      Impl.replay_mut(~Nat, ~Nat, ~Impl.wit_step, 1n, [1n, 2n, 3n], 0n)) == [4n, 7n] : List<&2, Nat>} &
  {[3n, 6n] != [4n, 7n] : List<&2, Nat>}
