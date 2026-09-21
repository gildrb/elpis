# Executable abstract checker, with independently specified transitions.
# Only free/status finite policies are intended for current host integration.
# Full transaction generations/completion/drain facts are NOT yet instrumented
# in native execution; this model does not certify them or CUDA instructions.
import Base
import ./transaction_spec.bend as Spec

def poisoned(status: Spec.Status) -> Bool:
  match status:
    case Spec.Clean{}:
      False{}
    case Spec.Poison{payload}:
      True{}

def apply_effect(status: Spec.Status, change: Spec.Effect) -> Spec.Status:
  match change:
    case Spec.KeepStatus{}:
      status
    case Spec.PoisonObserved{payload}:
      Spec.Poison{payload}
    case Spec.FillOne{}:
      Spec.Poison{0n}

def reject(generation: Nat, phase: Spec.Phase, status: Spec.Status,
  reason: Spec.Failure) -> Spec.State:
  match phase:
    case Spec.Failed{old}:
      Spec.State{generation, Spec.Failed{old}, status}
    case _:
      Spec.State{generation, Spec.Failed{reason}, status}

def produce(state: Spec.State, change: Spec.Effect) -> Spec.State:
  match state:
    case Spec.State{generation, Spec.Published{}, status}:
      Spec.State{generation, Spec.Failed{Spec.InvalidOrder{}}, status}
    case Spec.State{generation, Spec.Failed{reason}, status}:
      Spec.State{generation, Spec.Failed{reason}, status}
    case Spec.State{generation, phase, status}:
      Spec.State{1n+generation, Spec.Producing{}, apply_effect(status, change)}

def snapshot(+state: Spec.State, complete: Bool) -> Spec.State:
  match state:
    case Spec.State{generation, Spec.Idle{}, status}:
      match complete:
        case True{}:
          Spec.State{generation, Spec.Snapshotted{generation}, status}
        case False{}:
          Spec.State{generation, Spec.Failed{Spec.IncompleteProducers{}}, status}
    case Spec.State{generation, Spec.Producing{}, status}:
      match complete:
        case True{}:
          Spec.State{generation, Spec.Snapshotted{generation}, status}
        case False{}:
          Spec.State{generation, Spec.Failed{Spec.IncompleteProducers{}}, status}
    case Spec.State{generation, phase, status}:
      reject(generation, phase, status, Spec.InvalidOrder{})

def gate_result(current: Bool, generation: Nat, status: Spec.Status,
  next: Spec.Phase) -> Spec.State:
  match current:
    case True{}:
      match status:
        case Spec.Clean{}:
          Spec.State{generation, next, Spec.Clean{}}
        case Spec.Poison{payload}:
          Spec.State{generation, Spec.Failed{Spec.NativePoison{}}, Spec.Poison{payload}}
    case False{}:
      Spec.State{generation, Spec.Failed{Spec.StaleSnapshot{}}, status}

def gate(+generation: Nat, captured: Nat, status: Spec.Status,
  next: Spec.Phase) -> Spec.State:
  gate_result(Nat.is_eq(captured, generation), generation, status, next)

def check(+state: Spec.State) -> Spec.State:
  match state:
    case Spec.State{generation, Spec.Snapshotted{captured}, status}:
      gate(generation, captured, status, Spec.Checked{captured})
    case Spec.State{generation, phase, status}:
      reject(generation, phase, status, Spec.InvalidOrder{})

def publish(+state: Spec.State) -> Spec.State:
  match state:
    case Spec.State{generation, Spec.Checked{captured}, status}:
      gate(generation, captured, status, Spec.Published{})
    case Spec.State{generation, Spec.Idle{}, Spec.Clean{}}:
      Spec.State{generation, Spec.Published{}, Spec.Clean{}}
    case Spec.State{generation, Spec.Idle{}, Spec.Poison{payload}}:
      Spec.State{generation, Spec.Failed{Spec.NativePoison{}}, Spec.Poison{payload}}
    case Spec.State{generation, phase, status}:
      reject(generation, phase, status, Spec.InvalidOrder{})

def reset_when(quiescent: Bool, state: Spec.State) -> Spec.State:
  match quiescent:
    case False{}:
      state
    case True{}:
      match state:
        case Spec.State{generation, phase, status}:
          Spec.State{1n+generation, Spec.Idle{}, Spec.Clean{}}

def reset(state: Spec.State, quiescent: Bool) -> Spec.State:
  reset_when(quiescent, state)

def step(state: Spec.State, event: Spec.Event) -> Spec.State:
  match event:
    case Spec.Producer{change}:
      produce(state, change)
    case Spec.Snapshot{complete}:
      snapshot(state, complete)
    case Spec.Check{}:
      check(state)
    case Spec.Publish{}:
      publish(state)
    case Spec.Reset{quiescent}:
      reset(state, quiescent)

def run(events: List<&2, Spec.Event>, state: Spec.State) -> Spec.State:
  match events:
    case Nil{}:
      state
    case event <> rest:
      run(rest, step(state, event))

def observed(generation: Nat, status: Spec.Status) -> Spec.Observation:
  match status:
    case Spec.Clean{}:
      Spec.CleanAt{generation}
    case Spec.Poison{payload}:
      Spec.BadAt{generation, payload}

def retire(+mirror: Spec.Mirror, synchronized: Bool) -> Spec.MirrorResult:
  match mirror:
    case Spec.Unarmed{}:
      Spec.MirrorResult{Spec.Unarmed{}, Spec.MissingMirror{}}
    case Spec.Armed{generation, status, event_exists}:
      match event_exists:
        case False{}:
          Spec.MirrorResult{Spec.Unarmed{}, observed(generation, status)}
        case True{}:
          match synchronized:
            case False{}:
              Spec.MirrorResult{Spec.Armed{generation, status, True{}}, Spec.SynchronizationFailed{}}
            case True{}:
              Spec.MirrorResult{Spec.Unarmed{}, observed(generation, status)}

def rearm_result(result: Spec.MirrorResult, generation: Nat,
  status: Spec.Status, event_exists: Bool) -> Spec.MirrorResult:
  match result:
    case Spec.MirrorResult{remaining, Spec.CleanAt{checked_generation}}:
      Spec.MirrorResult{Spec.Armed{generation, status, event_exists}, Spec.NoObservation{}}
    case Spec.MirrorResult{remaining, observation}:
      Spec.MirrorResult{remaining, observation}

def rearm(old: Spec.Mirror, synchronized: Bool, generation: Nat,
  status: Spec.Status, event_exists: Bool) -> Spec.MirrorResult:
  match old:
    case Spec.Unarmed{}:
      Spec.MirrorResult{Spec.Armed{generation, status, event_exists}, Spec.NoObservation{}}
    case Spec.Armed{old_generation, old_status, old_event}:
      rearm_result(retire(Spec.Armed{old_generation, old_status, old_event}, synchronized),
        generation, status, event_exists)

def lifecycle(life: Spec.Life, event: Spec.LifeEvent) -> Maybe<&2, Spec.Life>:
  match life:
    case Spec.Running{}:
      match event:
        case Spec.Cancel{}:
          Some{Spec.CancelDraining{}}
        case Spec.Settle{drained}:
          match drained:
            case True{}:
              Some{Spec.Finished{}}
            case False{}:
              None{}
        case Spec.Retract{drained}:
          match drained:
            case True{}:
              Some{Spec.Retracted{}}
            case False{}:
              None{}
        case Spec.Release{drained}:
          None{}
    case Spec.CancelDraining{}:
      match event:
        case Spec.Cancel{}:
          Some{Spec.CancelDraining{}}
        case Spec.Settle{drained}:
          match drained:
            case True{}:
              Some{Spec.Finished{}}
            case False{}:
              None{}
        case _:
          None{}
    case Spec.Finished{}:
      match event:
        case Spec.Release{drained}:
          match drained:
            case True{}:
              Some{Spec.Released{}}
            case False{}:
              None{}
        case _:
          None{}
    case Spec.Retracted{}:
      match event:
        case Spec.Release{drained}:
          match drained:
            case True{}:
              Some{Spec.Released{}}
            case False{}:
              None{}
        case _:
          None{}
    case Spec.Released{}:
      None{}

def eager_append(route: Spec.Route) -> Bool:
  match route:
    case Spec.Eager{}:
      True{}
    case Spec.CaptureFailed{}:
      True{}
    case Spec.ShapeMismatch{}:
      True{}
    case Spec.GraphReplayed{}:
      False{}

def producer_contract_eager(eager: Bool, graph: Nat, target: Nat, draft: Nat) -> Bool:
  match eager:
    case True{}:
      Bool.and(Nat.is_eq(graph, 0n),
        Bool.and(Nat.is_eq(target, 1n), Nat.is_eq(draft, 1n)))
    case False{}:
      Bool.and(Nat.is_eq(graph, 1n),
        Bool.and(Nat.is_eq(target, 0n), Nat.is_eq(draft, 0n)))

def producer_contract(route: Spec.Route, graph: Nat, target: Nat, draft: Nat) -> Bool:
  producer_contract_eager(eager_append(route), graph, target, draft)

def issued_eager(eager: Bool, +graph: Nat, target: Nat, draft: Nat) -> Spec.Producers:
  match eager:
    case True{}:
      Spec.Producers{target, draft}
    case False{}:
      Spec.Producers{Nat.add(graph, target), Nat.add(graph, draft)}

def issued(route: Spec.Route, graph: Nat, target: Nat, draft: Nat) -> Spec.Producers:
  issued_eager(eager_append(route), graph, target, draft)

def both_one(target: Bool, draft: Bool) -> Bool:
  match target:
    case False{}:
      False{}
    case True{}:
      draft

def exactly_once(counts: Spec.Producers) -> Bool:
  Spec.Producers{target, draft} = counts
  both_one(Nat.is_eq(target, 1n), Nat.is_eq(draft, 1n))

def epoch_current(mirror: Spec.Epoch, current: Nat) -> Bool:
  match mirror:
    case Spec.InvalidEpoch{}:
      False{}
    case Spec.ValidEpoch{value}:
      Nat.is_eq(value, current)

def free_current(current: Bool, pending: Bool, ready: Bool) -> Nat:
  match current:
    case False{}:
      0n
    case True{}:
      match pending:
        case False{}:
          1n
        case True{}:
          match ready:
            case False{}:
              0n
            case True{}:
              1n

def free_policy(pending: Bool, ready: Bool, current: Bool) -> Nat:
  free_current(current, pending, ready)

def free_action(mirror: Spec.Epoch, current: Nat, pending: Bool, ready: Bool) -> Nat:
  free_policy(pending, ready, epoch_current(mirror, current))

def status_policy(armed: Bool, event_exists: Bool, ready: Bool) -> Nat:
  match armed:
    case False{}:
      0n
    case True{}:
      match event_exists:
        case True{}:
          1n
        case False{}:
          2n

# Balanced boolean enumeration; depth 3 yields every finite input exactly once.
# The newest decision is LSB, so row i has flags (i&1,i&2,i&4).
def free_table(+depth: Nat, +a: Bool, +b: Bool, +c: Bool) -> List<&2, Nat>:
  match depth:
    case 0n:
      [free_policy(a, b, c)]
    case 1n+p:
      left right = free_table(p, False{}, a, b) free_table(p, True{}, a, b)
      List.append(&2, Nat, left, right)

def status_table(+depth: Nat, +a: Bool, +b: Bool, +c: Bool) -> List<&2, Nat>:
  match depth:
    case 0n:
      [status_policy(a, b, c)]
    case 1n+p:
      left right = status_table(p, False{}, a, b) status_table(p, True{}, a, b)
      List.append(&2, Nat, left, right)

def current_observation(observation: Spec.Observation, generation: Nat) -> Bool:
  match observation:
    case Spec.CleanAt{captured}:
      Nat.is_eq(captured, generation)
    case _:
      False{}

def pools_ready(checks: Spec.PoolChecks, +generation: Nat) -> Bool:
  Spec.PoolChecks{target, draft} = checks
  Bool.and(current_observation(target, generation), current_observation(draft, generation))

def publish_permitted(permitted: Bool, state: Spec.State) -> Spec.State:
  match permitted:
    case False{}:
      match state:
        case Spec.State{generation, phase, status}:
          reject(generation, phase, status, Spec.InvalidOrder{})
    case True{}:
      publish(state)

def publish_all(+state: Spec.State, checks: Spec.PoolChecks) -> Spec.State:
  match state:
    case Spec.State{generation, phase, status}:
      publish_permitted(pools_ready(checks, generation), Spec.State{generation, phase, status})
