# Obligations for the device round advance (exl3_round.bend) composed with
# the EXL3 acceptance reference: every law takes the round's verdict from
# Accept.accept on a well-shaped round (k + 1 verify ids for k proposals,
# any k, so in particular every served k <= 7, and any ids, stop list,
# budget and checkpoint), and states what the advance kernel and the
# count-reading consumers do in terms of the committed token prefix.
import Base
import ./exl3_accept_spec.bend as Accept
import ./exl3_round.bend as Impl
import ./exl3_round_spec.bend as Spec

# (a) The position advances by exactly the committed prefix: count tokens
# while the job runs, none once it has stopped.
law advance_position:
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +checkpoint: Nat
  for +base: Nat
  for +interval: Nat
  for +position: Nat
  for +anchor: Nat
  for +stopped: Bool
  for +shaped: {List.length(&2, U32, targets) ==
    1n+List.length(&2, U32, proposals) : Nat}
  {Impl.position(Impl.advance(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      List.length(&2, U32, proposals), base, interval,
      Impl.State{position, budget, anchor, checkpoint, stopped})) ==
    Nat.add(position, List.length(&2, U32, Spec.committed(targets,
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      stopped))) : Nat}

# (b) A round that does not end the job replays exactly the committed
# prefix into the GDN state (steps = count), rewinds the conv state by the
# uncommitted verified suffix, and the consumers write.
law advance_replay:
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +checkpoint: Nat
  for +shaped: {List.length(&2, U32, targets) ==
    1n+List.length(&2, U32, proposals) : Nat}
  for +live: {Accept.eos(Accept.accept(targets, proposals, stops, budget,
    checkpoint)) == False{} : Bool}
  {Impl.steps(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)), List.length(&2, U32, proposals)) ==
    List.length(&2, U32, Spec.committed(targets,
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      False{})) : Nat} &
  {Impl.offset(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)), List.length(&2, U32, proposals)) ==
    List.length(&2, U32, Spec.uncommitted(targets,
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint))))
    : Nat} &
  {Impl.writes(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      List.length(&2, U32, proposals)) == True{} : Bool}

# (b) An eos round fully commits the (discarded) GDN state of the ended job:
# replay all k + 1 steps, no conv rewind.
law advance_replay_eos:
  for +count: Nat
  for +k: Nat
  {Impl.steps(count, True{}, k) == 1n+k : Nat} &
  {Impl.offset(count, True{}, k) == 0n : Nat}

# (b) The draft KV refresh writes k + 1 static rows at the old position, so
# every committed row is written, and its committed length is the new
# position.
law advance_refresh:
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +checkpoint: Nat
  for +base: Nat
  for +interval: Nat
  for +position: Nat
  for +anchor: Nat
  for +shaped: {List.length(&2, U32, targets) ==
    1n+List.length(&2, U32, proposals) : Nat}
  {Impl.refresh(position,
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)))
    == Impl.position(Impl.advance(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      List.length(&2, U32, proposals), base, interval,
      Impl.State{position, budget, anchor, checkpoint, False{}})) : Nat} &
  {Nat.is_le(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Impl.refresh_rows(List.length(&2, U32, proposals))) == True{} : Bool}

# (c) The next draft's anchor is verify_ids[count - 1], the last committed
# token.
law advance_anchor:
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +checkpoint: Nat
  for +base: Nat
  for +interval: Nat
  for +position: Nat
  for +anchor: Nat
  for +shaped: {List.length(&2, U32, targets) ==
    1n+List.length(&2, U32, proposals) : Nat}
  {List.get(&2, U32, targets, Impl.anchor(Impl.advance(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      List.length(&2, U32, proposals), base, interval,
      Impl.State{position, budget, anchor, checkpoint, False{}}))) ==
    List.last(&2, U32, Spec.committed(targets,
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      False{})) : Maybe<&2, U32>}

# (d) The budget decreases by exactly the committed prefix, never below 0:
# the new budget plus the committed count is the old positive budget.
law advance_budget:
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +checkpoint: Nat
  for +base: Nat
  for +interval: Nat
  for +position: Nat
  for +anchor: Nat
  for +stopped: Bool
  for +shaped: {List.length(&2, U32, targets) ==
    1n+List.length(&2, U32, proposals) : Nat}
  for positive: {Nat.is_lt(0n, budget) == True{} : Bool}
  {Nat.add(Impl.budget(Impl.advance(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      List.length(&2, U32, proposals), base, interval,
      Impl.State{position, budget, anchor, checkpoint, stopped})),
    List.length(&2, U32, Spec.committed(targets,
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      stopped))) == budget : Nat}

# (d) A job that keeps running keeps a positive budget, so the next round's
# accept call is again in the positive-budget domain (for any input budget:
# a round that exhausts the budget reports eos).
law advance_budget_live:
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +checkpoint: Nat
  for +base: Nat
  for +interval: Nat
  for +position: Nat
  for +anchor: Nat
  for +stopped: Bool
  for +shaped: {List.length(&2, U32, targets) ==
    1n+List.length(&2, U32, proposals) : Nat}
  {Bool.or(Impl.stopped(Impl.advance(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      List.length(&2, U32, proposals), base, interval,
      Impl.State{position, budget, anchor, checkpoint, stopped})),
    Nat.is_lt(0n, Impl.budget(Impl.advance(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      List.length(&2, U32, proposals), base, interval,
      Impl.State{position, budget, anchor, checkpoint, stopped})))) == True{}
    : Bool}

# (e) An eos round stops the job.
law advance_eos_stops:
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +checkpoint: Nat
  for +base: Nat
  for +interval: Nat
  for +position: Nat
  for +anchor: Nat
  for +stopped: Bool
  for ended: {Accept.eos(Accept.accept(targets, proposals, stops, budget,
    checkpoint)) == True{} : Bool}
  {Impl.stopped(Impl.advance(
      Accept.count(Accept.accept(targets, proposals, stops, budget, checkpoint)),
      Accept.eos(Accept.accept(targets, proposals, stops, budget, checkpoint)), List.length(&2, U32, proposals), base, interval,
      Impl.State{position, budget, anchor, checkpoint, stopped})) == True{}
    : Bool}

# (e) A failed decision (count 0, glue domain error) fails closed: nothing
# is committed and the job stops.
law advance_error_stops:
  for +eos: Bool
  for +window: Nat
  for +base: Nat
  for +interval: Nat
  for +position: Nat
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for +stopped: Bool
  {Impl.advance(0n, eos, window, base, interval,
      Impl.State{position, budget, anchor, checkpoint, stopped}) ==
    Impl.State{position, budget, anchor, checkpoint, True{}} : Impl.State}

# (e) A decision whose count exceeds window + 1 fails closed the same way.
law advance_range_stops:
  for +count: Nat
  for +eos: Bool
  for +window: Nat
  for +base: Nat
  for +interval: Nat
  for +position: Nat
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for +stopped: Bool
  for above: {Nat.is_lt(1n+window, count) == True{} : Bool}
  {Impl.advance(count, eos, window, base, interval,
      Impl.State{position, budget, anchor, checkpoint, stopped}) ==
    Impl.State{position, budget, anchor, checkpoint, True{}} : Impl.State}

# (e) Stopped is absorbing: after a stop, any sequence of later decisions
# (whatever their counts and eos) leaves the state, and so the committed
# position and budget, unchanged, and nothing further is committed.
law stop_absorbing:
  for +verdicts: List<&2, Accept.Verdict>
  for +window: Nat
  for +base: Nat
  for +interval: Nat
  for +position: Nat
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  {Impl.rounds(verdicts, window, base, interval,
      Impl.State{position, budget, anchor, checkpoint, True{}}) ==
    Impl.State{position, budget, anchor, checkpoint, True{}} : Impl.State}

law stop_commits_nothing:
  for +targets: List<&2, U32>
  for +count: Nat
  {Spec.committed(targets, count, True{}) == Nil{} : List<&2, U32>}

# (f) The checkpoint formula is _greedy_checkpoint's contract: the first
# committed count in 1..window that lands on a boundary, else 0.
law checkpoint_refinement:
  for +position: Nat
  for +base: Nat
  for +interval: Nat
  for +window: Nat
  for positive: {Nat.is_lt(0n, interval) == True{} : Bool}
  for above: {Nat.is_le(base, position) == True{} : Bool}
  {Impl.checkpoint(position, base, interval, window) ==
    Spec.checkpoint(position, base, interval, window) : Nat}

# (f) The advance keeps the state's checkpoint equal to the checkpoint of
# its position, so each round's accept input is Impl.checkpoint.
law checkpoint_invariant:
  for +count: Nat
  for +eos: Bool
  for +window: Nat
  for +base: Nat
  for +interval: Nat
  for +position: Nat
  for +budget: Nat
  for +anchor: Nat
  for +stopped: Bool
  {Impl.checkpoint_of(Impl.advance(count, eos, window, base, interval,
      Impl.State{position, budget, anchor,
        Impl.checkpoint(position, base, interval, window), stopped})) ==
    Impl.checkpoint(Impl.position(Impl.advance(count, eos, window, base,
      interval, Impl.State{position, budget, anchor,
        Impl.checkpoint(position, base, interval, window), stopped})),
      base, interval, window) : Nat}

# (f) A speculative round never crosses a checkpoint: with the state's
# checkpoint as accept input, no boundary lies strictly between the old
# position and the new one.
law round_checkpoint:
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +base: Nat
  for +interval: Nat
  for +position: Nat
  for +shaped: {List.length(&2, U32, targets) ==
    1n+List.length(&2, U32, proposals) : Nat}
  for positive: {Nat.is_lt(0n, interval) == True{} : Bool}
  for above: {Nat.is_le(base, position) == True{} : Bool}
  {Spec.crosses(Accept.count(Accept.accept(targets, proposals, stops, budget,
      Impl.checkpoint(position, base, interval,
        List.length(&2, U32, proposals)))),
    position, base, interval) == False{} : Bool}
