# Constructor proofs cover the finite policy domain; structural induction covers
# arbitrary Nat generations and every finite event trace. No compiler/native
# semantics are assumed proved here. Original Bend2.0.20 proof declarations.
import Base
import ./transaction_spec.bend as Spec
import ./transaction.bend as Impl
import ./transaction_laws.bend as Laws

# Nat.cmp recursively strips matching successors: no bounded epoch surrogate.
def equal_self(+n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      equal_self(p)

def unequal_successor(+n: Nat) -> {Nat.is_eq(n, 1n+n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      unequal_successor(p)

def gate_result_refinement(+current: Bool, +generation: Nat,
  +status: Spec.Status, +next: Spec.Phase)
  -> {Impl.gate_result(current, generation, status, next) ==
    Spec.gate_result(current, generation, status, next) : Spec.State}:
  match current:
    case False{}:
      {==}
    case True{}:
      match status:
        case Spec.Clean{}:
          {==}
        case Spec.Poison{payload}:
          {==}

def gate_refinement(+generation: Nat, +snapshot: Nat,
  +status: Spec.Status, +next: Spec.Phase)
  -> {Impl.gate(generation, snapshot, status, next) ==
    Spec.gate(generation, snapshot, status, next) : Spec.State}:
  gate_result_refinement(Nat.is_eq(snapshot, generation), generation, status, next)

def Laws.effect_refinement(status, effect):
  match effect:
    case Spec.KeepStatus{}:
      {==}
    case Spec.PoisonObserved{payload}:
      {==}
    case Spec.FillOne{}:
      {==}

def producer_effect_reference(+generation: Nat, +status: Spec.Status, +change: Spec.Effect)
  -> {Spec.State{1n+generation, Spec.Producing{}, Impl.apply_effect(status, change)} ==
    Spec.State{1n+generation, Spec.Producing{}, Spec.effect(status, change)} : Spec.State}:
  Equal.cong(Spec.Status, Spec.State,
    value => Spec.State{1n+generation, Spec.Producing{}, value},
    Impl.apply_effect(status, change), Spec.effect(status, change),
    Laws.effect_refinement(status, change))

def event_refinement(+event: Spec.Event, +state: Spec.State)
  -> {Impl.step(state, event) == Spec.step(state, event) : Spec.State}:
  match event:
    case Spec.Producer{change}:
      match state:
        case Spec.State{generation, Spec.Idle{}, status}:
          producer_effect_reference(generation, status, change)
        case Spec.State{generation, Spec.Producing{}, status}:
          producer_effect_reference(generation, status, change)
        case Spec.State{generation, Spec.Snapshotted{snapshot}, status}:
          producer_effect_reference(generation, status, change)
        case Spec.State{generation, Spec.Checked{snapshot}, status}:
          producer_effect_reference(generation, status, change)
        case Spec.State{generation, Spec.Published{}, status}:
          {==}
        case Spec.State{generation, Spec.Failed{reason}, status}:
          {==}
    case Spec.Snapshot{complete}:
      match complete state:
        case False{} Spec.State{generation, Spec.Idle{}, status}:
          {==}
        case False{} Spec.State{generation, Spec.Producing{}, status}:
          {==}
        case False{} Spec.State{generation, Spec.Snapshotted{snapshot}, status}:
          {==}
        case False{} Spec.State{generation, Spec.Checked{snapshot}, status}:
          {==}
        case False{} Spec.State{generation, Spec.Published{}, status}:
          {==}
        case False{} Spec.State{generation, Spec.Failed{reason}, status}:
          {==}
        case True{} Spec.State{generation, Spec.Idle{}, status}:
          {==}
        case True{} Spec.State{generation, Spec.Producing{}, status}:
          {==}
        case True{} Spec.State{generation, Spec.Snapshotted{snapshot}, status}:
          {==}
        case True{} Spec.State{generation, Spec.Checked{snapshot}, status}:
          {==}
        case True{} Spec.State{generation, Spec.Published{}, status}:
          {==}
        case True{} Spec.State{generation, Spec.Failed{reason}, status}:
          {==}
    case Spec.Check{}:
      match state:
        case Spec.State{generation, Spec.Idle{}, status}:
          {==}
        case Spec.State{generation, Spec.Producing{}, status}:
          {==}
        case Spec.State{generation, Spec.Snapshotted{snapshot}, status}:
          gate_refinement(generation, snapshot, status, Spec.Checked{snapshot})
        case Spec.State{generation, Spec.Checked{snapshot}, status}:
          {==}
        case Spec.State{generation, Spec.Published{}, status}:
          {==}
        case Spec.State{generation, Spec.Failed{reason}, status}:
          {==}
    case Spec.Publish{}:
      match state:
        case Spec.State{generation, Spec.Idle{}, Spec.Clean{}}:
          {==}
        case Spec.State{generation, Spec.Idle{}, Spec.Poison{payload}}:
          {==}
        case Spec.State{generation, Spec.Producing{}, status}:
          {==}
        case Spec.State{generation, Spec.Snapshotted{snapshot}, status}:
          {==}
        case Spec.State{generation, Spec.Checked{snapshot}, status}:
          gate_refinement(generation, snapshot, status, Spec.Published{})
        case Spec.State{generation, Spec.Published{}, status}:
          {==}
        case Spec.State{generation, Spec.Failed{reason}, status}:
          {==}
    case Spec.Reset{quiescent}:
      match quiescent state:
        case False{} Spec.State{generation, phase, status}:
          {==}
        case True{} Spec.State{generation, phase, status}:
          {==}

def Laws.step_refinement(state, event):
  event_refinement(event, state)

def Laws.trace_refinement(events, state):
  match events:
    case Nil{}:
      {==}
    case event <> rest:
      Equal.trans(Spec.State, Impl.run(rest, Impl.step(state, event)),
        Spec.run(rest, Impl.step(state, event)), Spec.run(rest, Spec.step(state, event)),
        Laws.trace_refinement(rest, Impl.step(state, event)),
        Equal.cong(Spec.State, Spec.State, next => Spec.run(rest, next),
          Impl.step(state, event), Spec.step(state, event), Laws.step_refinement(state, event)))

def Laws.trace_composition(prefix, suffix, state):
  match prefix:
    case Nil{}:
      {==}
    case event <> rest:
      Laws.trace_composition(rest, suffix, Impl.step(state, event))

def Laws.poison_persistence(payload, effect):
  match effect:
    case Spec.KeepStatus{}:
      {==}
    case Spec.PoisonObserved{next}:
      {==}
    case Spec.FillOne{}:
      {==}

def Laws.fill_one(payload):
  {==}

def Laws.late_producer_invalidates(generation, snapshot, status, effect):
  Equal.cong(Spec.Status, Spec.State,
    value => Spec.State{1n+generation, Spec.Producing{}, value},
    Impl.apply_effect(status, effect), Spec.effect(status, effect),
    Laws.effect_refinement(status, effect))

def Laws.checked_producer_invalidates(generation, snapshot, status, effect):
  Equal.cong(Spec.Status, Spec.State,
    value => Spec.State{1n+generation, Spec.Producing{}, value},
    Impl.apply_effect(status, effect), Spec.effect(status, effect),
    Laws.effect_refinement(status, effect))

def Laws.unchecked_publish_rejected(generation, snapshot, status):
  {==}

def Laws.incomplete_rejected(generation, status):
  {==}

def Laws.stale_publish_rejected(generation, snapshot, status, stale):
  Equal.cong(Bool, Spec.State,
    current => Impl.gate_result(current, generation, status, Spec.Published{}),
    Nat.is_eq(snapshot, generation), False{}, stale)

def Laws.late_check_rejected(generation, snapshot, status, effect):
  Equal.cong(Spec.Status, Spec.State,
    value => Spec.State{1n+generation, Spec.Failed{Spec.InvalidOrder{}}, value},
    Impl.apply_effect(status, effect), Spec.effect(status, effect),
    Laws.effect_refinement(status, effect))

def checked_current(+generation: Nat)
  -> {Impl.check(Spec.State{generation, Spec.Snapshotted{generation}, Spec.Clean{}}) ==
    Spec.State{generation, Spec.Checked{generation}, Spec.Clean{}} : Spec.State}:
  Equal.cong(Bool, Spec.State,
    current => Impl.gate_result(current, generation, Spec.Clean{}, Spec.Checked{generation}),
    Nat.is_eq(generation, generation), True{}, equal_self(generation))

def publish_current(+generation: Nat)
  -> {Impl.publish(Spec.State{generation, Spec.Checked{generation}, Spec.Clean{}}) ==
    Spec.State{generation, Spec.Published{}, Spec.Clean{}} : Spec.State}:
  Equal.cong(Bool, Spec.State,
    current => Impl.gate_result(current, generation, Spec.Clean{}, Spec.Published{}),
    Nat.is_eq(generation, generation), True{}, equal_self(generation))

def Laws.legal_progress(generation):
  Equal.trans(Spec.State,
    Impl.publish(Impl.check(Spec.State{generation, Spec.Snapshotted{generation}, Spec.Clean{}})),
    Impl.publish(Spec.State{generation, Spec.Checked{generation}, Spec.Clean{}}),
    Spec.State{generation, Spec.Published{}, Spec.Clean{}},
    Equal.cong(Spec.State, Spec.State, value => Impl.publish(value),
      Impl.check(Spec.State{generation, Spec.Snapshotted{generation}, Spec.Clean{}}),
      Spec.State{generation, Spec.Checked{generation}, Spec.Clean{}}, checked_current(generation)),
    publish_current(generation))

def Laws.idle_progress(generation):
  {==}

def Laws.poisoned_gate_rejected(generation, payload):
  Equal.cong(Bool, Spec.State,
    current => Impl.gate_result(current, generation, Spec.Poison{payload}, Spec.Checked{generation}),
    Nat.is_eq(generation, generation), True{}, equal_self(generation))

def Laws.reset_requires_quiescence(state):
  {==}

def Laws.quiescent_reset_progress(generation, phase, status):
  {==}

def Laws.failure_preserved(generation, reason, status, effect):
  ({==}, {==}, {==})

def observed_reference(+generation: Nat, +status: Spec.Status)
  -> {Spec.MirrorResult{Spec.Unarmed{}, Impl.observed(generation, status)} ==
    Spec.MirrorResult{Spec.Unarmed{}, Spec.observed(generation, status)} : Spec.MirrorResult}:
  match status:
    case Spec.Clean{}:
      {==}
    case Spec.Poison{payload}:
      {==}

def Laws.retire_refinement(mirror, synchronized):
  match mirror:
    case Spec.Unarmed{}:
      {==}
    case Spec.Armed{generation, status, event_exists}:
      match event_exists synchronized:
        case False{} False{}:
          observed_reference(generation, status)
        case False{} True{}:
          observed_reference(generation, status)
        case True{} False{}:
          {==}
        case True{} True{}:
          observed_reference(generation, status)

def Laws.rearm_refinement(old, synchronized, generation, status, event_exists):
  match old:
    case Spec.Unarmed{}:
      {==}
    case Spec.Armed{old_generation, old_status, old_event}:
      match old_status old_event synchronized:
        case Spec.Clean{} False{} False{}:
          {==}
        case Spec.Clean{} False{} True{}:
          {==}
        case Spec.Clean{} True{} False{}:
          {==}
        case Spec.Clean{} True{} True{}:
          {==}
        case Spec.Poison{payload} False{} False{}:
          {==}
        case Spec.Poison{payload} False{} True{}:
          {==}
        case Spec.Poison{payload} True{} False{}:
          {==}
        case Spec.Poison{payload} True{} True{}:
          {==}

def Laws.missing_snapshot_rejected(synchronized):
  {==}

def Laws.failed_sync_retains_writer(generation, status):
  {==}

def Laws.bad_snapshot_disarmed(generation, payload, event_exists):
  match event_exists:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.failed_rearm_no_overwrite(old_generation, old_status, new_generation, new_status, new_event):
  {==}

def Laws.bad_rearm_surfaces_failure(old_generation, payload, old_event, new_generation, new_status, new_event):
  match old_event:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.clean_rearm_progress(old_generation, old_event, generation, status, event_exists):
  match old_event:
    case False{}:
      {==}
    case True{}:
      {==}

def lifecycle_event_refinement(+event: Spec.LifeEvent, +life: Spec.Life)
  -> {Impl.lifecycle(life, event) == Spec.lifecycle(life, event) : Maybe<&2, Spec.Life>}:
  match event:
    case Spec.Cancel{}:
      match life:
        case Spec.Running{}:
          {==}
        case Spec.CancelDraining{}:
          {==}
        case Spec.Finished{}:
          {==}
        case Spec.Retracted{}:
          {==}
        case Spec.Released{}:
          {==}
    case Spec.Settle{drained}:
      match drained life:
        case False{} Spec.Running{}:
          {==}
        case False{} Spec.CancelDraining{}:
          {==}
        case False{} Spec.Finished{}:
          {==}
        case False{} Spec.Retracted{}:
          {==}
        case False{} Spec.Released{}:
          {==}
        case True{} Spec.Running{}:
          {==}
        case True{} Spec.CancelDraining{}:
          {==}
        case True{} Spec.Finished{}:
          {==}
        case True{} Spec.Retracted{}:
          {==}
        case True{} Spec.Released{}:
          {==}
    case Spec.Retract{drained}:
      match drained life:
        case False{} Spec.Running{}:
          {==}
        case False{} Spec.CancelDraining{}:
          {==}
        case False{} Spec.Finished{}:
          {==}
        case False{} Spec.Retracted{}:
          {==}
        case False{} Spec.Released{}:
          {==}
        case True{} Spec.Running{}:
          {==}
        case True{} Spec.CancelDraining{}:
          {==}
        case True{} Spec.Finished{}:
          {==}
        case True{} Spec.Retracted{}:
          {==}
        case True{} Spec.Released{}:
          {==}
    case Spec.Release{drained}:
      match drained life:
        case False{} Spec.Running{}:
          {==}
        case False{} Spec.CancelDraining{}:
          {==}
        case False{} Spec.Finished{}:
          {==}
        case False{} Spec.Retracted{}:
          {==}
        case False{} Spec.Released{}:
          {==}
        case True{} Spec.Running{}:
          {==}
        case True{} Spec.CancelDraining{}:
          {==}
        case True{} Spec.Finished{}:
          {==}
        case True{} Spec.Retracted{}:
          {==}
        case True{} Spec.Released{}:
          {==}

def Laws.lifecycle_refinement(life, event):
  lifecycle_event_refinement(event, life)

def Laws.cancellation_drains():
  ({==}, {==}, {==}, {==}, {==}, {==})

def Laws.no_undrained_release(life):
  match life:
    case Spec.Running{}:
      {==}
    case Spec.CancelDraining{}:
      {==}
    case Spec.Finished{}:
      {==}
    case Spec.Retracted{}:
      {==}
    case Spec.Released{}:
      {==}

def Laws.route_refinement(route, graph, target, draft):
  match route:
    case Spec.Eager{}:
      ({==}, {==})
    case Spec.CaptureFailed{}:
      ({==}, {==})
    case Spec.ShapeMismatch{}:
      ({==}, {==})
    case Spec.GraphReplayed{}:
      ({==}, {==})

def both_one_refinement(+a: Bool, +b: Bool)
  -> {Impl.both_one(a, b) == Bool.and(a, b) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.exactly_once_refinement(counts):
  match counts:
    case Spec.Producers{target, draft}:
      both_one_refinement(Nat.is_eq(target, 1n), Nat.is_eq(draft, 1n))

def Laws.graph_progress():
  ({==}, {==})

def Laws.eager_fallback_progress():
  ({==}, {==}, {==})

def Laws.duplicate_draft_rejected():
  {==}

def both_one_missing(a: Bool) -> {Impl.both_one(a, False{}) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.missing_producer_rejected(count):
  both_one_missing(Nat.is_eq(count, 1n))

def Laws.free_policy_refinement(pending, ready, current):
  match pending ready current:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def Laws.free_epoch_refinement(mirror, current, pending, ready):
  match mirror:
    case Spec.InvalidEpoch{}:
      Laws.free_policy_refinement(pending, ready, False{})
    case Spec.ValidEpoch{value}:
      Laws.free_policy_refinement(pending, ready, Nat.is_eq(value, current))

def ready_current(pending: Bool) -> {Impl.free_policy(pending, True{}, True{}) == 1n : Nat}:
  match pending:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.current_epoch_progress(epoch, pending):
  Equal.trans(Nat, Impl.free_policy(pending, True{}, Nat.is_eq(epoch, epoch)),
    Impl.free_policy(pending, True{}, True{}), 1n,
    Equal.cong(Bool, Nat, current => Impl.free_policy(pending, True{}, current),
      Nat.is_eq(epoch, epoch), True{}, equal_self(epoch)), ready_current(pending))

def Laws.successor_epoch_invalidates(epoch, pending, ready):
  Equal.cong(Bool, Nat, current => Impl.free_policy(pending, ready, current),
    Nat.is_eq(epoch, 1n+epoch), False{}, unequal_successor(epoch))

def Laws.missing_epoch_recounts(current, pending, ready):
  {==}

def unready(current: Bool) -> {Impl.free_policy(True{}, False{}, current) == 0n : Nat}:
  match current:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.pending_unready_recounts(mirror, current):
  unready(Impl.epoch_current(mirror, current))

def Laws.status_policy_refinement(armed, event_exists, ready):
  match armed event_exists:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Laws.status_ready_irrelevant(armed, event_exists, ready):
  match armed event_exists:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# These two are complete domains of THREE Booleans, not samples of Nat epochs.
# The independent rows decode index arithmetic while the implementation expands
# the balanced Boolean tree. Normalization is only eight small rows per table.
def Laws.free_finite_domain():
  {==}

def Laws.status_finite_domain():
  {==}

def Laws.wire_exact():
  {==}

def Laws.producer_contract_refinement(route, graph, target, draft):
  match route:
    case Spec.Eager{}:
      {==}
    case Spec.CaptureFailed{}:
      {==}
    case Spec.ShapeMismatch{}:
      {==}
    case Spec.GraphReplayed{}:
      {==}

def Laws.producer_contract_progress():
  ({==}, {==}, {==}, {==})

def and_false(value: Bool) -> {Bool.and(value, False{}) == False{} : Bool}:
  match value:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.graph_and_eager_rejected(target, draft):
  and_false(Nat.is_eq(target, 0n))

def Laws.unreported_graph_rejected(graph, target, draft):
  {==}

def poisoned_gate_not_published(current: Bool, generation: Nat,
  payload: Nat, next: Spec.Phase)
  -> {Spec.published(Impl.gate_result(current, generation, Spec.Poison{payload}, next)) == False{} : Bool}:
  match current:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.poison_prevents_publication(generation, phase, payload):
  match phase:
    case Spec.Idle{}:
      {==}
    case Spec.Producing{}:
      {==}
    case Spec.Snapshotted{snapshot}:
      {==}
    case Spec.Checked{snapshot}:
      poisoned_gate_not_published(Nat.is_eq(snapshot, generation), generation, payload, Spec.Published{})
    case Spec.Published{}:
      {==}
    case Spec.Failed{reason}:
      {==}

def Laws.pools_ready_refinement(checks, generation):
  match checks:
    case Spec.PoolChecks{Spec.NoObservation{}, draft}:
      {==}
    case Spec.PoolChecks{Spec.BadAt{target_generation, payload}, draft}:
      {==}
    case Spec.PoolChecks{Spec.MissingMirror{}, draft}:
      {==}
    case Spec.PoolChecks{Spec.SynchronizationFailed{}, draft}:
      {==}
    case Spec.PoolChecks{Spec.CleanAt{target_generation}, Spec.CleanAt{draft_generation}}:
      {==}
    case Spec.PoolChecks{Spec.CleanAt{target_generation}, Spec.NoObservation{}}:
      and_false(Nat.is_eq(target_generation, generation))
    case Spec.PoolChecks{Spec.CleanAt{target_generation}, Spec.BadAt{draft_generation, payload}}:
      and_false(Nat.is_eq(target_generation, generation))
    case Spec.PoolChecks{Spec.CleanAt{target_generation}, Spec.MissingMirror{}}:
      and_false(Nat.is_eq(target_generation, generation))
    case Spec.PoolChecks{Spec.CleanAt{target_generation}, Spec.SynchronizationFailed{}}:
      and_false(Nat.is_eq(target_generation, generation))

def publish_permitted_refinement(+permitted: Bool, +state: Spec.State)
  -> {Impl.publish_permitted(permitted, state) == Spec.publish_permitted(permitted, state) : Spec.State}:
  match permitted:
    case True{}:
      Laws.step_refinement(state, Spec.Publish{})
    case False{}:
      match state:
        case Spec.State{generation, Spec.Idle{}, status}:
          {==}
        case Spec.State{generation, Spec.Producing{}, status}:
          {==}
        case Spec.State{generation, Spec.Snapshotted{snapshot}, status}:
          {==}
        case Spec.State{generation, Spec.Checked{snapshot}, status}:
          {==}
        case Spec.State{generation, Spec.Published{}, status}:
          {==}
        case Spec.State{generation, Spec.Failed{reason}, status}:
          {==}

def Laws.publish_all_refinement(state, checks):
  match state:
    case Spec.State{generation, phase, status}:
      Equal.trans(Spec.State,
        Impl.publish_permitted(Impl.pools_ready(checks, generation), Spec.State{generation, phase, status}),
        Impl.publish_permitted(Spec.pools_ready(checks, generation), Spec.State{generation, phase, status}),
        Spec.publish_permitted(Spec.pools_ready(checks, generation), Spec.State{generation, phase, status}),
        Equal.cong(Bool, Spec.State,
          permitted => Impl.publish_permitted(permitted, Spec.State{generation, phase, status}),
          Impl.pools_ready(checks, generation), Spec.pools_ready(checks, generation),
          Laws.pools_ready_refinement(checks, generation)),
        publish_permitted_refinement(Spec.pools_ready(checks, generation), Spec.State{generation, phase, status}))

def Laws.pools_current_progress(generation):
  Equal.cong(Bool, Bool, +current => Bool.and(current, current),
    Nat.is_eq(generation, generation), True{}, equal_self(generation))

def Laws.either_pool_failure_rejected(generation, bad_generation, payload, other):
  ({==}, and_false(Impl.current_observation(other, generation)))

def Laws.missing_draft_rejected(generation, target):
  and_false(Impl.current_observation(target, generation))

def Laws.all_pools_publish_progress(generation):
  Equal.trans(Spec.State,
    Impl.publish_all(Spec.State{generation, Spec.Checked{generation}, Spec.Clean{}},
      Spec.PoolChecks{Spec.CleanAt{generation}, Spec.CleanAt{generation}}),
    Impl.publish(Spec.State{generation, Spec.Checked{generation}, Spec.Clean{}}),
    Spec.State{generation, Spec.Published{}, Spec.Clean{}},
    Equal.cong(Bool, Spec.State,
      permitted => Impl.publish_permitted(permitted,
        Spec.State{generation, Spec.Checked{generation}, Spec.Clean{}}),
      Impl.pools_ready(Spec.PoolChecks{Spec.CleanAt{generation}, Spec.CleanAt{generation}}, generation),
      True{}, Laws.pools_current_progress(generation)),
    publish_current(generation))

def gate_poison(current: Bool, generation: Nat, payload: Nat, next: Spec.Phase)
  -> {Spec.state_poisoned(Impl.gate_result(current, generation, Spec.Poison{payload}, next)) == True{} : Bool}:
  match current:
    case False{}:
      {==}
    case True{}:
      {==}

def snapshot_poison(+phase: Spec.Phase, +complete: Bool, +generation: Nat, +payload: Nat)
  -> {Spec.state_poisoned(Impl.snapshot(Spec.State{generation, phase, Spec.Poison{payload}}, complete)) == True{} : Bool}:
  match phase:
    case Spec.Idle{}:
      match complete:
        case False{}:
          {==}
        case True{}:
          {==}
    case Spec.Producing{}:
      match complete:
        case False{}:
          {==}
        case True{}:
          {==}
    case Spec.Snapshotted{snapshot}:
      {==}
    case Spec.Checked{snapshot}:
      {==}
    case Spec.Published{}:
      {==}
    case Spec.Failed{reason}:
      {==}

def produced_poison(generation: Nat, payload: Nat, change: Spec.Effect)
  -> {Spec.state_poisoned(Spec.State{1n+generation, Spec.Producing{},
    Impl.apply_effect(Spec.Poison{payload}, change)}) == True{} : Bool}:
  match change:
    case Spec.KeepStatus{}:
      {==}
    case Spec.PoisonObserved{next}:
      {==}
    case Spec.FillOne{}:
      {==}

def Laws.nonreset_poison(event, generation, phase, payload):
  match event:
    case Spec.Producer{change}:
      match phase:
        case Spec.Idle{}:
          produced_poison(generation, payload, change)
        case Spec.Producing{}:
          produced_poison(generation, payload, change)
        case Spec.Snapshotted{snapshot}:
          produced_poison(generation, payload, change)
        case Spec.Checked{snapshot}:
          produced_poison(generation, payload, change)
        case Spec.Published{}:
          {==}
        case Spec.Failed{reason}:
          {==}
    case Spec.Snapshot{complete}:
      snapshot_poison(phase, complete, generation, payload)
    case Spec.Check{}:
      match phase:
        case Spec.Idle{}:
          {==}
        case Spec.Producing{}:
          {==}
        case Spec.Snapshotted{snapshot}:
          gate_poison(Nat.is_eq(snapshot, generation), generation, payload, Spec.Checked{snapshot})
        case Spec.Checked{snapshot}:
          {==}
        case Spec.Published{}:
          {==}
        case Spec.Failed{reason}:
          {==}
    case Spec.Publish{}:
      match phase:
        case Spec.Idle{}:
          {==}
        case Spec.Producing{}:
          {==}
        case Spec.Snapshotted{snapshot}:
          {==}
        case Spec.Checked{snapshot}:
          gate_poison(Nat.is_eq(snapshot, generation), generation, payload, Spec.Published{})
        case Spec.Published{}:
          {==}
        case Spec.Failed{reason}:
          {==}
    case Spec.Reset{quiescent}:
      match quiescent:
        case False{}:
          {==}
        case True{}:
          {==}
