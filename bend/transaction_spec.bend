# Abstract permitted control transitions, NOT a CUDA/native refinement theorem.
# Source: KVarNTokenToKVPool.{clear,begin_status_mirror,finish_status_mirror,
# mirrored_tail_slots}, DFlashWorkerV2 final commit/append/publication boundary,
# _KVarNCommitGraphRunner._run_region, Scheduler.abort_request.
# Generation is arbitrary Nat ghost identity: native status has no epoch field.
# Free-slot epochs are actual unbounded host integers; -1 is InvalidEpoch.
# Stream ordering, complete target/draft layer coverage, truthful observations,
# no aliasing, and all-writer/reference quiescence remain external premises.
import Base
import ./marlin_pipeline_spec.bend as MarlinPipeline

type Epoch is Data:
  InvalidEpoch{}
  ValidEpoch{value: Nat}

type Status is Data:
  Clean{}
  Poison{payload: Nat}

# Poison payload encodes unsigned nonzero status as 1+payload. It includes
# unknown bits; host signed int32 interpretation is an external ABI obligation.
# PoisonObserved is the observed NONZERO result of an OR-producing kernel,
# not an assertion that every payload is obtainable from every prior word.
# FillOne represents packed_attention_flash's actual native_status.fill_(1).
# Only zero/nonzero persistence is modeled; bitwise monotonicity is FALSE.
type Effect is Data:
  KeepStatus{}
  PoisonObserved{payload: Nat}
  FillOne{}

type Failure is Data:
  InvalidOrder{}
  IncompleteProducers{}
  StaleSnapshot{}
  NativePoison{}

type Phase is Data:
  Idle{}
  Producing{}
  Snapshotted{generation: Nat}
  Checked{generation: Nat}
  Published{}
  Failed{reason: Failure}

type State is Data:
  State{generation: Nat, phase: Phase, status: Status}

type Event is Data:
  Producer{effect: Effect}
  Snapshot{complete: Bool}
  Check{}
  Publish{}
  Reset{quiescent: Bool}

# Completion is a declared event contract: all required producers were issued
# before this stream-ordered snapshot. No currently instrumented native counter
# measures it. A snapshot alone is not evidence for that premise.
def poisoned(status: Status) -> Bool:
  match status:
    case Clean{}:
      False{}
    case Poison{payload}:
      True{}

def effect(status: Status, change: Effect) -> Status:
  match change:
    case KeepStatus{}:
      status
    case PoisonObserved{payload}:
      Poison{payload}
    case FillOne{}:
      Poison{0n}

def live(phase: Phase) -> Bool:
  match phase:
    case Idle{}:
      True{}
    case Producing{}:
      True{}
    case Snapshotted{generation}:
      True{}
    case Checked{generation}:
      True{}
    case Published{}:
      False{}
    case Failed{reason}:
      False{}

def reject(generation: Nat, phase: Phase, status: Status, reason: Failure) -> State:
  match phase:
    case Failed{old}:
      State{generation, Failed{old}, status}
    case _:
      State{generation, Failed{reason}, status}

def gate_result(current: Bool, generation: Nat, status: Status, next: Phase) -> State:
  match current:
    case False{}:
      State{generation, Failed{StaleSnapshot{}}, status}
    case True{}:
      match status:
        case Clean{}:
          State{generation, next, Clean{}}
        case Poison{payload}:
          State{generation, Failed{NativePoison{}}, Poison{payload}}

def gate(+generation: Nat, snapshot: Nat, status: Status, next: Phase) -> State:
  gate_result(Nat.is_eq(snapshot, generation), generation, status, next)

def dispatch(event: Event, +state: State) -> State:
  match event state:
    case Producer{change} State{generation, Published{}, status}:
      State{generation, Failed{InvalidOrder{}}, status}
    case Producer{change} State{generation, Failed{reason}, status}:
      State{generation, Failed{reason}, status}
    case Producer{change} State{generation, phase, status}:
      State{1n+generation, Producing{}, effect(status, change)}
    case Snapshot{True{}} State{generation, Idle{}, status}:
      State{generation, Snapshotted{generation}, status}
    case Snapshot{True{}} State{generation, Producing{}, status}:
      State{generation, Snapshotted{generation}, status}
    case Snapshot{False{}} State{generation, Idle{}, status}:
      State{generation, Failed{IncompleteProducers{}}, status}
    case Snapshot{False{}} State{generation, Producing{}, status}:
      State{generation, Failed{IncompleteProducers{}}, status}
    case Snapshot{complete} State{generation, phase, status}:
      reject(generation, phase, status, InvalidOrder{})
    case Check{} State{generation, Snapshotted{snapshot}, status}:
      gate(generation, snapshot, status, Checked{snapshot})
    case Check{} State{generation, phase, status}:
      reject(generation, phase, status, InvalidOrder{})
    case Publish{} State{generation, Checked{snapshot}, status}:
      gate(generation, snapshot, status, Published{})
    case Publish{} State{generation, Idle{}, Clean{}}:
      State{generation, Published{}, Clean{}}
    case Publish{} State{generation, Idle{}, Poison{payload}}:
      State{generation, Failed{NativePoison{}}, Poison{payload}}
    case Publish{} State{generation, phase, status}:
      reject(generation, phase, status, InvalidOrder{})
    case Reset{False{}} State{generation, phase, status}:
      State{generation, phase, status}
    case Reset{True{}} State{generation, phase, status}:
      # ALL writers joined AND references gone, outside capture. Native clear
      # joins mirror writers, not unrelated streams; caller supplies the rest.
      State{1n+generation, Idle{}, Clean{}}

def step(state: State, event: Event) -> State:
  dispatch(event, state)

def run(events: List<&2, Event>, state: State) -> State:
  match events:
    case Nil{}:
      state
    case event <> rest:
      run(rest, step(state, event))

# Snapshot lifetime is separate from transaction success. A failed first pool
# can leave a second pool armed. Sync failure must retain that writer; observed
# bad status is disarmed before error; rearm first retires an old snapshot.
type Mirror is Data:
  Unarmed{}
  Armed{generation: Nat, status: Status, event_exists: Bool}

type Observation is Data:
  NoObservation{}
  CleanAt{generation: Nat}
  BadAt{generation: Nat, payload: Nat}
  MissingMirror{}
  SynchronizationFailed{}

type MirrorResult is Data:
  MirrorResult{mirror: Mirror, observation: Observation}

def observed(generation: Nat, status: Status) -> Observation:
  match status:
    case Clean{}:
      CleanAt{generation}
    case Poison{payload}:
      BadAt{generation, payload}

def retire_blocked(blocked: Bool, generation: Nat, status: Status,
  event_exists: Bool) -> MirrorResult:
  match blocked:
    case True{}:
      MirrorResult{Armed{generation, status, event_exists}, SynchronizationFailed{}}
    case False{}:
      MirrorResult{Unarmed{}, observed(generation, status)}

def retire(+mirror: Mirror, synchronized: Bool) -> MirrorResult:
  match mirror:
    case Unarmed{}:
      MirrorResult{Unarmed{}, MissingMirror{}}
    case Armed{generation, status, event_exists}:
      retire_blocked(Bool.and(event_exists, Bool.not(synchronized)),
        generation, status, event_exists)

def rearm_result(result: MirrorResult, generation: Nat,
  status: Status, event_exists: Bool) -> MirrorResult:
  match result:
    case MirrorResult{remaining, CleanAt{checked_generation}}:
      MirrorResult{Armed{generation, status, event_exists}, NoObservation{}}
    case MirrorResult{remaining, observation}:
      MirrorResult{remaining, observation}

def rearm(old: Mirror, synchronized: Bool, generation: Nat,
  status: Status, event_exists: Bool) -> MirrorResult:
  match old:
    case Unarmed{}:
      MirrorResult{Armed{generation, status, event_exists}, NoObservation{}}
    case Armed{old_generation, old_status, old_event}:
      rearm_result(retire(Armed{old_generation, old_status, old_event}, synchronized),
        generation, status, event_exists)

# Cancellation is deferred: already-issued/next decode writes may finish.
# The drain premise includes result ownership and last GPU reader/writer, not
# merely a request's finished flag. This is NOT a theorem about chunked abort.
type Life is Data:
  Running{}
  CancelDraining{}
  Finished{}
  Retracted{}
  Released{}

type LifeEvent is Data:
  Cancel{}
  Settle{drained: Bool}
  Retract{drained: Bool}
  Release{drained: Bool}

def lifecycle_event(event: LifeEvent, life: Life) -> Maybe<&2, Life>:
  match event:
    case Cancel{}:
      match life:
        case Running{}:
          Some{CancelDraining{}}
        case CancelDraining{}:
          Some{CancelDraining{}}
        case _:
          None{}
    case Settle{drained}:
      match drained life:
        case True{} Running{}:
          Some{Finished{}}
        case True{} CancelDraining{}:
          Some{Finished{}}
        case _ _:
          None{}
    case Retract{drained}:
      match drained life:
        case True{} Running{}:
          Some{Retracted{}}
        case _ _:
          None{}
    case Release{drained}:
      match drained life:
        case True{} Finished{}:
          Some{Released{}}
        case True{} Retracted{}:
          Some{Released{}}
        case _ _:
          None{}

def lifecycle(life: Life, event: LifeEvent) -> Maybe<&2, Life>:
  lifecycle_event(event, life)

def may_write(life: Life) -> Bool:
  match life:
    case Running{}:
      True{}
    case CancelDraining{}:
      True{}
    case _:
      False{}

# Graph flag != replay. Failed capture and mismatch remain eager. Counts are
# issued-producer obligations over arbitrary Nat, not measured GPU execution.
type Route is Data:
  Eager{}
  CaptureFailed{}
  ShapeMismatch{}
  GraphReplayed{}

type Producers is Data:
  Producers{target: Nat, draft: Nat}

# Authorization checks actual issued-event counts, including the forbidden
# branch. `issued` alone is a route projection, NOT an authorization predicate.
# There is currently no native event counter providing these Nat observations.
def producer_contract(route: Route, graph: Nat, target: Nat, draft: Nat) -> Bool:
  match route:
    case GraphReplayed{}:
      Bool.and(Nat.is_eq(graph, 1n),
        Bool.and(Nat.is_eq(target, 0n), Nat.is_eq(draft, 0n)))
    case _:
      Bool.and(Nat.is_eq(graph, 0n),
        Bool.and(Nat.is_eq(target, 1n), Nat.is_eq(draft, 1n)))

def eager_append(route: Route) -> Bool:
  match route:
    case GraphReplayed{}:
      False{}
    case _:
      True{}

def issued(route: Route, +graph: Nat, +target: Nat, +draft: Nat) -> Producers:
  match route:
    case GraphReplayed{}:
      Producers{Nat.add(graph, target), Nat.add(graph, draft)}
    case _:
      Producers{target, draft}

def exactly_once(counts: Producers) -> Bool:
  Producers{target, draft} = counts
  Bool.and(Nat.is_eq(target, 1n), Nat.is_eq(draft, 1n))

def epoch_current(mirror: Epoch, current: Nat) -> Bool:
  match mirror:
    case InvalidEpoch{}:
      False{}
    case ValidEpoch{value}:
      Nat.is_eq(value, current)

# 0=ExactRecount, 1=ReadMirror. Missing event while pending is a host invariant
# violation handled by existing native exception logic before a usable read.
def free_eligible(eligible: Bool) -> Nat:
  match eligible:
    case False{}:
      0n
    case True{}:
      1n

def free_policy(pending: Bool, ready: Bool, current: Bool) -> Nat:
  free_eligible(Bool.and(current, Bool.or(Bool.not(pending), ready)))

def free_action(mirror: Epoch, current: Nat, pending: Bool, ready: Bool) -> Nat:
  free_policy(pending, ready, epoch_current(mirror, current))

# 0=RejectUnarmed, 1=SynchronizeThenCheck, 2=CheckImmediately. Readiness NEVER
# bypasses event.synchronize(), because its error observation is contractual.
def status_policy(armed: Bool, event_exists: Bool, ready: Bool) -> Nat:
  match armed event_exists:
    case False{} _:
      0n
    case True{} True{}:
      1n
    case True{} False{}:
      2n

# Arithmetic row decoding is independent of the executable boolean generator.
def bit(+index: Nat) -> Bool:
  Nat.is_ne(Nat.mod(index, 2n), 0n)

def free_row(+index: Nat) -> Nat:
  free_policy(bit(index), bit(Nat.div(index, 2n)), bit(Nat.div(index, 4n)))

def status_row(+index: Nat) -> Nat:
  status_policy(bit(index), bit(Nat.div(index, 2n)), bit(Nat.div(index, 4n)))

def free_rows(count: Nat, +index: Nat) -> String:
  match count:
    case 0n:
      ""
    case 1n+p:
      Nat.show(free_row(index)) ++ "\n" ++ free_rows(p, 1n+index)

def status_rows(count: Nat, +index: Nat) -> String:
  match count:
    case 0n:
      ""
    case 1n+p:
      Nat.show(status_row(index)) ++ "\n" ++ status_rows(p, 1n+index)

def marlin_rows(count: Nat, +index: Nat) -> String:
  match count:
    case 0n:
      ""
    case 1n+p:
      Nat.show(MarlinPipeline.row(index)) ++ "\n" ++ marlin_rows(p, 1n+index)

def protocol() -> String:
  "QWEN_RUNTIME_CONTROL_V2\nFREE_MIRROR\n8\n" ++ free_rows(8n, 0n) ++
    "STATUS\n8\n" ++ status_rows(8n, 0n) ++
    "MARLIN_EIGHT_STAGE\n8\n" ++ marlin_rows(8n, 0n) ++
    "END_QWEN_RUNTIME_CONTROL"

def published(state: State) -> Bool:
  match state:
    case State{generation, Published{}, status}:
      True{}
    case State{generation, phase, status}:
      False{}

# Active native target/draft publication requires BOTH current clean checks.
# MissingMirror/NoObservation remain explicit, never treated as a clean pool.
# Empty batches use the separate Idle transition, not fabricated pool checks.
type PoolChecks is Data:
  PoolChecks{target: Observation, draft: Observation}

def pools_ready(checks: PoolChecks, +generation: Nat) -> Bool:
  match checks:
    case PoolChecks{CleanAt{target}, CleanAt{draft}}:
      Bool.and(Nat.is_eq(target, generation), Nat.is_eq(draft, generation))
    case PoolChecks{target, draft}:
      False{}

def publish_permitted(permitted: Bool, state: State) -> State:
  match permitted:
    case True{}:
      step(state, Publish{})
    case False{}:
      match state:
        case State{generation, phase, status}:
          reject(generation, phase, status, InvalidOrder{})

def publish_all(+state: State, checks: PoolChecks) -> State:
  match state:
    case State{generation, phase, status}:
      publish_permitted(pools_ready(checks, generation), State{generation, phase, status})

def reset_granted(event: Event) -> Bool:
  match event:
    case Reset{quiescent}:
      quiescent
    case _:
      False{}

def state_poisoned(state: State) -> Bool:
  match state:
    case State{generation, phase, Clean{}}:
      False{}
    case State{generation, phase, Poison{payload}}:
      True{}
