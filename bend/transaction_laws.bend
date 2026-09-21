# Laws for permitted abstract transitions and the finite executable host leaf.
# These declarations do NOT assert native stream/compiler/graph refinement.
import Base
import ./transaction_spec.bend as Spec
import ./transaction.bend as Impl
import ./RUNTIME.bend as Wire

law step_refinement:
  for +state: Spec.State
  for +event: Spec.Event
  {Impl.step(state, event) == Spec.step(state, event) : Spec.State}

law trace_refinement:
  for +events: List<&2, Spec.Event>
  for +state: Spec.State
  {Impl.run(events, state) == Spec.run(events, state) : Spec.State}

law trace_composition:
  for +prefix: List<&2, Spec.Event>
  for +suffix: List<&2, Spec.Event>
  for +state: Spec.State
  {Impl.run(List.append(&2, Spec.Event, prefix, suffix), state) ==
    Impl.run(suffix, Impl.run(prefix, state)) : Spec.State}

law effect_refinement:
  for +status: Spec.Status
  for +effect: Spec.Effect
  {Impl.apply_effect(status, effect) == Spec.effect(status, effect) : Spec.Status}

law poison_persistence:
  for payload: Nat
  for effect: Spec.Effect
  {Impl.poisoned(Impl.apply_effect(Spec.Poison{payload}, effect)) == True{} : Bool}

# Source has fill_(1): this preserves poison while discarding e.g. capacity bit.
law fill_one:
  for payload: Nat
  {Impl.apply_effect(Spec.Poison{payload}, Spec.FillOne{}) == Spec.Poison{0n} : Spec.Status}

law late_producer_invalidates:
  for +generation: Nat
  for snapshot: Nat
  for +status: Spec.Status
  for +effect: Spec.Effect
  {Impl.produce(Spec.State{generation, Spec.Snapshotted{snapshot}, status}, effect) ==
    Spec.State{1n+generation, Spec.Producing{}, Spec.effect(status, effect)} : Spec.State}

law checked_producer_invalidates:
  for +generation: Nat
  for snapshot: Nat
  for +status: Spec.Status
  for +effect: Spec.Effect
  {Impl.produce(Spec.State{generation, Spec.Checked{snapshot}, status}, effect) ==
    Spec.State{1n+generation, Spec.Producing{}, Spec.effect(status, effect)} : Spec.State}

law unchecked_publish_rejected:
  for +generation: Nat
  for snapshot: Nat
  for +status: Spec.Status
  {Impl.publish(Spec.State{generation, Spec.Snapshotted{snapshot}, status}) ==
    Spec.State{generation, Spec.Failed{Spec.InvalidOrder{}}, status} : Spec.State}

law incomplete_rejected:
  for +generation: Nat
  for +status: Spec.Status
  {Impl.snapshot(Spec.State{generation, Spec.Producing{}, status}, False{}) ==
    Spec.State{generation, Spec.Failed{Spec.IncompleteProducers{}}, status} : Spec.State}

law stale_publish_rejected:
  for +generation: Nat
  for +snapshot: Nat
  for +status: Spec.Status
  for stale: {Nat.is_eq(snapshot, generation) == False{} : Bool}
  {Impl.publish(Spec.State{generation, Spec.Checked{snapshot}, status}) ==
    Spec.State{generation, Spec.Failed{Spec.StaleSnapshot{}}, status} : Spec.State}

law late_check_rejected:
  for +generation: Nat
  for snapshot: Nat
  for +status: Spec.Status
  for +effect: Spec.Effect
  {Impl.check(Impl.produce(Spec.State{generation, Spec.Snapshotted{snapshot}, status}, effect)) ==
    Spec.State{1n+generation, Spec.Failed{Spec.InvalidOrder{}}, Spec.effect(status, effect)} : Spec.State}

# Nonvacuous successful path for EVERY generation, not one concrete history.
law legal_progress:
  for +generation: Nat
  {Impl.publish(Impl.check(Impl.snapshot(
    Spec.State{generation, Spec.Producing{}, Spec.Clean{}}, True{}))) ==
    Spec.State{generation, Spec.Published{}, Spec.Clean{}} : Spec.State}

law idle_progress:
  for +generation: Nat
  {Impl.publish(Spec.State{generation, Spec.Idle{}, Spec.Clean{}}) ==
    Spec.State{generation, Spec.Published{}, Spec.Clean{}} : Spec.State}

law poisoned_gate_rejected:
  for +generation: Nat
  for +payload: Nat
  {Impl.check(Spec.State{generation, Spec.Snapshotted{generation}, Spec.Poison{payload}}) ==
    Spec.State{generation, Spec.Failed{Spec.NativePoison{}}, Spec.Poison{payload}} : Spec.State}

law reset_requires_quiescence:
  for +state: Spec.State
  {Impl.reset(state, False{}) == state : Spec.State}

law quiescent_reset_progress:
  for +generation: Nat
  for phase: Spec.Phase
  for status: Spec.Status
  {Impl.reset(Spec.State{generation, phase, status}, True{}) ==
    Spec.State{1n+generation, Spec.Idle{}, Spec.Clean{}} : Spec.State}

law failure_preserved:
  for +generation: Nat
  for +reason: Spec.Failure
  for +status: Spec.Status
  for effect: Spec.Effect
  {Impl.produce(Spec.State{generation, Spec.Failed{reason}, status}, effect) ==
    Spec.State{generation, Spec.Failed{reason}, status} : Spec.State} &
  {Impl.check(Spec.State{generation, Spec.Failed{reason}, status}) ==
    Spec.State{generation, Spec.Failed{reason}, status} : Spec.State} &
  {Impl.publish(Spec.State{generation, Spec.Failed{reason}, status}) ==
    Spec.State{generation, Spec.Failed{reason}, status} : Spec.State}

law retire_refinement:
  for +mirror: Spec.Mirror
  for +synchronized: Bool
  {Impl.retire(mirror, synchronized) == Spec.retire(mirror, synchronized) : Spec.MirrorResult}

law rearm_refinement:
  for +old: Spec.Mirror
  for +synchronized: Bool
  for +generation: Nat
  for +status: Spec.Status
  for +event_exists: Bool
  {Impl.rearm(old, synchronized, generation, status, event_exists) ==
    Spec.rearm(old, synchronized, generation, status, event_exists) : Spec.MirrorResult}

law missing_snapshot_rejected:
  for synchronized: Bool
  {Impl.retire(Spec.Unarmed{}, synchronized) ==
    Spec.MirrorResult{Spec.Unarmed{}, Spec.MissingMirror{}} : Spec.MirrorResult}

law failed_sync_retains_writer:
  for +generation: Nat
  for +status: Spec.Status
  {Impl.retire(Spec.Armed{generation, status, True{}}, False{}) ==
    Spec.MirrorResult{Spec.Armed{generation, status, True{}},
      Spec.SynchronizationFailed{}} : Spec.MirrorResult}

law bad_snapshot_disarmed:
  for +generation: Nat
  for +payload: Nat
  for event_exists: Bool
  {Impl.retire(Spec.Armed{generation, Spec.Poison{payload}, event_exists}, True{}) ==
    Spec.MirrorResult{Spec.Unarmed{}, Spec.BadAt{generation, payload}} : Spec.MirrorResult}

law failed_rearm_no_overwrite:
  for +old_generation: Nat
  for +old_status: Spec.Status
  for new_generation: Nat
  for new_status: Spec.Status
  for new_event: Bool
  {Impl.rearm(Spec.Armed{old_generation, old_status, True{}}, False{},
    new_generation, new_status, new_event) ==
    Spec.MirrorResult{Spec.Armed{old_generation, old_status, True{}},
      Spec.SynchronizationFailed{}} : Spec.MirrorResult}

law bad_rearm_surfaces_failure:
  for +old_generation: Nat
  for +payload: Nat
  for old_event: Bool
  for new_generation: Nat
  for new_status: Spec.Status
  for new_event: Bool
  {Impl.rearm(Spec.Armed{old_generation, Spec.Poison{payload}, old_event}, True{},
    new_generation, new_status, new_event) ==
    Spec.MirrorResult{Spec.Unarmed{}, Spec.BadAt{old_generation, payload}} : Spec.MirrorResult}

law clean_rearm_progress:
  for old_generation: Nat
  for old_event: Bool
  for +generation: Nat
  for +status: Spec.Status
  for +event_exists: Bool
  {Impl.rearm(Spec.Armed{old_generation, Spec.Clean{}, old_event}, True{},
    generation, status, event_exists) ==
    Spec.MirrorResult{Spec.Armed{generation, status, event_exists},
      Spec.NoObservation{}} : Spec.MirrorResult}

law lifecycle_refinement:
  for +life: Spec.Life
  for +event: Spec.LifeEvent
  {Impl.lifecycle(life, event) == Spec.lifecycle(life, event) : Maybe<&2, Spec.Life>}

law cancellation_drains:
  {Impl.lifecycle(Spec.Running{}, Spec.Cancel{}) == Some{Spec.CancelDraining{}} : Maybe<&2, Spec.Life>} &
  {Spec.may_write(Spec.CancelDraining{}) == True{} : Bool} &
  {Impl.lifecycle(Spec.CancelDraining{}, Spec.Release{True{}}) == None{} : Maybe<&2, Spec.Life>} &
  {Impl.lifecycle(Spec.CancelDraining{}, Spec.Settle{False{}}) == None{} : Maybe<&2, Spec.Life>} &
  {Impl.lifecycle(Spec.CancelDraining{}, Spec.Settle{True{}}) == Some{Spec.Finished{}} : Maybe<&2, Spec.Life>} &
  {Impl.lifecycle(Spec.Finished{}, Spec.Release{True{}}) == Some{Spec.Released{}} : Maybe<&2, Spec.Life>}

law no_undrained_release:
  for life: Spec.Life
  {Impl.lifecycle(life, Spec.Release{False{}}) == None{} : Maybe<&2, Spec.Life>}

law route_refinement:
  for +route: Spec.Route
  for +graph: Nat
  for +target: Nat
  for +draft: Nat
  {Impl.issued(route, graph, target, draft) == Spec.issued(route, graph, target, draft) : Spec.Producers} &
  {Impl.eager_append(route) == Spec.eager_append(route) : Bool}

law exactly_once_refinement:
  for +counts: Spec.Producers
  {Impl.exactly_once(counts) == Spec.exactly_once(counts) : Bool}

law graph_progress:
  {Impl.exactly_once(Impl.issued(Spec.GraphReplayed{}, 1n, 0n, 0n)) == True{} : Bool} &
  {Impl.eager_append(Spec.GraphReplayed{}) == False{} : Bool}

law eager_fallback_progress:
  {Impl.exactly_once(Impl.issued(Spec.Eager{}, 0n, 1n, 1n)) == True{} : Bool} &
  {Impl.exactly_once(Impl.issued(Spec.CaptureFailed{}, 0n, 1n, 1n)) == True{} : Bool} &
  {Impl.exactly_once(Impl.issued(Spec.ShapeMismatch{}, 0n, 1n, 1n)) == True{} : Bool}

law duplicate_draft_rejected:
  {Impl.exactly_once(Impl.issued(Spec.GraphReplayed{}, 1n, 0n, 1n)) == False{} : Bool}

law missing_producer_rejected:
  for count: Nat
  {Impl.exactly_once(Spec.Producers{count, 0n}) == False{} : Bool}

law producer_contract_refinement:
  for +route: Spec.Route
  for +graph: Nat
  for +target: Nat
  for +draft: Nat
  {Impl.producer_contract(route, graph, target, draft) ==
    Spec.producer_contract(route, graph, target, draft) : Bool}

law producer_contract_progress:
  {Impl.producer_contract(Spec.GraphReplayed{}, 1n, 0n, 0n) == True{} : Bool} &
  {Impl.producer_contract(Spec.Eager{}, 0n, 1n, 1n) == True{} : Bool} &
  {Impl.producer_contract(Spec.CaptureFailed{}, 0n, 1n, 1n) == True{} : Bool} &
  {Impl.producer_contract(Spec.ShapeMismatch{}, 0n, 1n, 1n) == True{} : Bool}

law graph_and_eager_rejected:
  for target: Nat
  for draft: Nat
  {Impl.producer_contract(Spec.GraphReplayed{}, 1n, target, 1n+draft) == False{} : Bool}

law unreported_graph_rejected:
  for graph: Nat
  for target: Nat
  for draft: Nat
  {Impl.producer_contract(Spec.Eager{}, 1n+graph, target, draft) == False{} : Bool}

law poison_prevents_publication:
  for +generation: Nat
  for phase: Spec.Phase
  for payload: Nat
  {Spec.published(Impl.publish(Spec.State{generation, phase, Spec.Poison{payload}})) == False{} : Bool}

law free_policy_refinement:
  for +pending: Bool
  for +ready: Bool
  for +current: Bool
  {Impl.free_policy(pending, ready, current) == Spec.free_policy(pending, ready, current) : Nat}

law free_epoch_refinement:
  for +mirror: Spec.Epoch
  for +current: Nat
  for +pending: Bool
  for +ready: Bool
  {Impl.free_action(mirror, current, pending, ready) == Spec.free_action(mirror, current, pending, ready) : Nat}

law current_epoch_progress:
  for +epoch: Nat
  for +pending: Bool
  {Impl.free_action(Spec.ValidEpoch{epoch}, epoch, pending, True{}) == 1n : Nat}

law successor_epoch_invalidates:
  for +epoch: Nat
  for pending: Bool
  for ready: Bool
  {Impl.free_action(Spec.ValidEpoch{epoch}, 1n+epoch, pending, ready) == 0n : Nat}

law missing_epoch_recounts:
  for current: Nat
  for pending: Bool
  for ready: Bool
  {Impl.free_action(Spec.InvalidEpoch{}, current, pending, ready) == 0n : Nat}

law pending_unready_recounts:
  for mirror: Spec.Epoch
  for current: Nat
  {Impl.free_action(mirror, current, True{}, False{}) == 0n : Nat}

law status_policy_refinement:
  for +armed: Bool
  for +event_exists: Bool
  for +ready: Bool
  {Impl.status_policy(armed, event_exists, ready) == Spec.status_policy(armed, event_exists, ready) : Nat}

law status_ready_irrelevant:
  for +armed: Bool
  for +event_exists: Bool
  for ready: Bool
  {Impl.status_policy(armed, event_exists, ready) == Impl.status_policy(armed, event_exists, False{}) : Nat}

law free_finite_domain:
  {Impl.free_table(3n, False{}, False{}, False{}) ==
    [Spec.free_row(0n), Spec.free_row(1n), Spec.free_row(2n), Spec.free_row(3n),
      Spec.free_row(4n), Spec.free_row(5n), Spec.free_row(6n), Spec.free_row(7n)] : List<&2, Nat>}

law status_finite_domain:
  {Impl.status_table(3n, False{}, False{}, False{}) ==
    [Spec.status_row(0n), Spec.status_row(1n), Spec.status_row(2n), Spec.status_row(3n),
      Spec.status_row(4n), Spec.status_row(5n), Spec.status_row(6n), Spec.status_row(7n)] : List<&2, Nat>}

law wire_exact:
  {Wire.protocol() == Spec.protocol() : String}

law pools_ready_refinement:
  for +checks: Spec.PoolChecks
  for +generation: Nat
  {Impl.pools_ready(checks, generation) == Spec.pools_ready(checks, generation) : Bool}

law publish_all_refinement:
  for +state: Spec.State
  for +checks: Spec.PoolChecks
  {Impl.publish_all(state, checks) == Spec.publish_all(state, checks) : Spec.State}

law pools_current_progress:
  for +generation: Nat
  {Impl.pools_ready(Spec.PoolChecks{Spec.CleanAt{generation},
    Spec.CleanAt{generation}}, generation) == True{} : Bool}

law either_pool_failure_rejected:
  for +generation: Nat
  for +bad_generation: Nat
  for +payload: Nat
  for +other: Spec.Observation
  {Impl.pools_ready(Spec.PoolChecks{Spec.BadAt{bad_generation, payload}, other},
    generation) == False{} : Bool} &
  {Impl.pools_ready(Spec.PoolChecks{other, Spec.BadAt{bad_generation, payload}},
    generation) == False{} : Bool}

law missing_draft_rejected:
  for generation: Nat
  for target: Spec.Observation
  {Impl.pools_ready(Spec.PoolChecks{target, Spec.NoObservation{}}, generation) == False{} : Bool}

law all_pools_publish_progress:
  for +generation: Nat
  {Impl.publish_all(Spec.State{generation, Spec.Checked{generation}, Spec.Clean{}},
    Spec.PoolChecks{Spec.CleanAt{generation}, Spec.CleanAt{generation}}) ==
    Spec.State{generation, Spec.Published{}, Spec.Clean{}} : Spec.State}

# Boolean implication: either an explicitly quiescent reset was granted, or
# poison survives the entire state transition (including failure branches).
law nonreset_poison:
  for +event: Spec.Event
  for +generation: Nat
  for +phase: Spec.Phase
  for +payload: Nat
  {Bool.or(Spec.reset_granted(event), Spec.state_poisoned(
    Impl.step(Spec.State{generation, phase, Spec.Poison{payload}}, event))) == True{} : Bool}
