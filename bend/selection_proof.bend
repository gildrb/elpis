# Proof-only entry point. No main, local foreign code, unsafe definitions or
# axioms. Constructor cases establish the finite algebra; structural induction
# establishes the result for ALL finite observation lists, without a bound.
import Base
import ./objectives.bend as Objectives
import ./selection.bend as Selection
import ./selection_laws.bend as Laws
import ./SELECT.bend as Wire

# Independent predicate accumulation for an already nonempty projection.
# Unavailable evidence absorbs every combination of gain and loss.
def step_summary(available: Bool, gain: Bool, loss: Bool, order: Objectives.Order)
  -> {Selection.step(Objectives.relation(True{}, available, gain, loss), order) ==
    Objectives.relation(True{}, Bool.and(Objectives.known([order]), available),
      Bool.or(Objectives.better([order]), gain), Bool.or(Objectives.worse([order]), loss)) : Objectives.Relation}:
  match available:
    case False{}:
      match order:
        case Objectives.Better{}:
          {==}
        case Objectives.Same{}:
          {==}
        case Objectives.Worse{}:
          {==}
        case Objectives.Missing{}:
          {==}
    case True{}:
      match gain loss order:
        case False{} False{} Objectives.Better{}:
          {==}
        case False{} False{} Objectives.Same{}:
          {==}
        case False{} False{} Objectives.Worse{}:
          {==}
        case False{} False{} Objectives.Missing{}:
          {==}
        case False{} True{} Objectives.Better{}:
          {==}
        case False{} True{} Objectives.Same{}:
          {==}
        case False{} True{} Objectives.Worse{}:
          {==}
        case False{} True{} Objectives.Missing{}:
          {==}
        case True{} False{} Objectives.Better{}:
          {==}
        case True{} False{} Objectives.Same{}:
          {==}
        case True{} False{} Objectives.Worse{}:
          {==}
        case True{} False{} Objectives.Missing{}:
          {==}
        case True{} True{} Objectives.Better{}:
          {==}
        case True{} True{} Objectives.Same{}:
          {==}
        case True{} True{} Objectives.Worse{}:
          {==}
        case True{} True{} Objectives.Missing{}:
          {==}

# The empty projection is handled separately: no spurious objective is created.
def spec_step(+xs: List<&2, Objectives.Order>, order: Objectives.Order)
  -> {Selection.step(Objectives.classify_orders(xs), order) ==
    Objectives.classify_orders(order <> xs) : Objectives.Relation}:
  match xs:
    case Nil{}:
      match order:
        case Objectives.Better{}:
          {==}
        case Objectives.Same{}:
          {==}
        case Objectives.Worse{}:
          {==}
        case Objectives.Missing{}:
          {==}
    case h <> t:
      match order:
        case Objectives.Better{}:
          step_summary(Objectives.known(h <> t), Objectives.better(h <> t), Objectives.worse(h <> t), Objectives.Better{})
        case Objectives.Same{}:
          step_summary(Objectives.known(h <> t), Objectives.better(h <> t), Objectives.worse(h <> t), Objectives.Same{})
        case Objectives.Worse{}:
          step_summary(Objectives.known(h <> t), Objectives.better(h <> t), Objectives.worse(h <> t), Objectives.Worse{})
        case Objectives.Missing{}:
          step_summary(Objectives.known(h <> t), Objectives.better(h <> t), Objectives.worse(h <> t), Objectives.Missing{})

# Exhaustive constructor proof of commutation, NOT enumeration of input lists.
# This permits the tail fold to agree with the independent recursive predicates.
def step_commute(state: Objectives.Relation, a: Objectives.Order, b: Objectives.Order)
  -> {Selection.step(Selection.step(state, a), b) ==
    Selection.step(Selection.step(state, b), a) : Objectives.Relation}:
  match state:
    case Objectives.NoObjectives{}:
      match a b:
        case Objectives.Better{} Objectives.Better{}:
          {==}
        case Objectives.Better{} Objectives.Same{}:
          {==}
        case Objectives.Better{} Objectives.Worse{}:
          {==}
        case Objectives.Better{} Objectives.Missing{}:
          {==}
        case Objectives.Same{} Objectives.Better{}:
          {==}
        case Objectives.Same{} Objectives.Same{}:
          {==}
        case Objectives.Same{} Objectives.Worse{}:
          {==}
        case Objectives.Same{} Objectives.Missing{}:
          {==}
        case Objectives.Worse{} Objectives.Better{}:
          {==}
        case Objectives.Worse{} Objectives.Same{}:
          {==}
        case Objectives.Worse{} Objectives.Worse{}:
          {==}
        case Objectives.Worse{} Objectives.Missing{}:
          {==}
        case Objectives.Missing{} Objectives.Better{}:
          {==}
        case Objectives.Missing{} Objectives.Same{}:
          {==}
        case Objectives.Missing{} Objectives.Worse{}:
          {==}
        case Objectives.Missing{} Objectives.Missing{}:
          {==}
    case Objectives.Equivalent{}:
      match a b:
        case Objectives.Better{} Objectives.Better{}:
          {==}
        case Objectives.Better{} Objectives.Same{}:
          {==}
        case Objectives.Better{} Objectives.Worse{}:
          {==}
        case Objectives.Better{} Objectives.Missing{}:
          {==}
        case Objectives.Same{} Objectives.Better{}:
          {==}
        case Objectives.Same{} Objectives.Same{}:
          {==}
        case Objectives.Same{} Objectives.Worse{}:
          {==}
        case Objectives.Same{} Objectives.Missing{}:
          {==}
        case Objectives.Worse{} Objectives.Better{}:
          {==}
        case Objectives.Worse{} Objectives.Same{}:
          {==}
        case Objectives.Worse{} Objectives.Worse{}:
          {==}
        case Objectives.Worse{} Objectives.Missing{}:
          {==}
        case Objectives.Missing{} Objectives.Better{}:
          {==}
        case Objectives.Missing{} Objectives.Same{}:
          {==}
        case Objectives.Missing{} Objectives.Worse{}:
          {==}
        case Objectives.Missing{} Objectives.Missing{}:
          {==}
    case Objectives.Dominates{}:
      match a b:
        case Objectives.Better{} Objectives.Better{}:
          {==}
        case Objectives.Better{} Objectives.Same{}:
          {==}
        case Objectives.Better{} Objectives.Worse{}:
          {==}
        case Objectives.Better{} Objectives.Missing{}:
          {==}
        case Objectives.Same{} Objectives.Better{}:
          {==}
        case Objectives.Same{} Objectives.Same{}:
          {==}
        case Objectives.Same{} Objectives.Worse{}:
          {==}
        case Objectives.Same{} Objectives.Missing{}:
          {==}
        case Objectives.Worse{} Objectives.Better{}:
          {==}
        case Objectives.Worse{} Objectives.Same{}:
          {==}
        case Objectives.Worse{} Objectives.Worse{}:
          {==}
        case Objectives.Worse{} Objectives.Missing{}:
          {==}
        case Objectives.Missing{} Objectives.Better{}:
          {==}
        case Objectives.Missing{} Objectives.Same{}:
          {==}
        case Objectives.Missing{} Objectives.Worse{}:
          {==}
        case Objectives.Missing{} Objectives.Missing{}:
          {==}
    case Objectives.Dominated{}:
      match a b:
        case Objectives.Better{} Objectives.Better{}:
          {==}
        case Objectives.Better{} Objectives.Same{}:
          {==}
        case Objectives.Better{} Objectives.Worse{}:
          {==}
        case Objectives.Better{} Objectives.Missing{}:
          {==}
        case Objectives.Same{} Objectives.Better{}:
          {==}
        case Objectives.Same{} Objectives.Same{}:
          {==}
        case Objectives.Same{} Objectives.Worse{}:
          {==}
        case Objectives.Same{} Objectives.Missing{}:
          {==}
        case Objectives.Worse{} Objectives.Better{}:
          {==}
        case Objectives.Worse{} Objectives.Same{}:
          {==}
        case Objectives.Worse{} Objectives.Worse{}:
          {==}
        case Objectives.Worse{} Objectives.Missing{}:
          {==}
        case Objectives.Missing{} Objectives.Better{}:
          {==}
        case Objectives.Missing{} Objectives.Same{}:
          {==}
        case Objectives.Missing{} Objectives.Worse{}:
          {==}
        case Objectives.Missing{} Objectives.Missing{}:
          {==}
    case Objectives.Tradeoff{}:
      match a b:
        case Objectives.Better{} Objectives.Better{}:
          {==}
        case Objectives.Better{} Objectives.Same{}:
          {==}
        case Objectives.Better{} Objectives.Worse{}:
          {==}
        case Objectives.Better{} Objectives.Missing{}:
          {==}
        case Objectives.Same{} Objectives.Better{}:
          {==}
        case Objectives.Same{} Objectives.Same{}:
          {==}
        case Objectives.Same{} Objectives.Worse{}:
          {==}
        case Objectives.Same{} Objectives.Missing{}:
          {==}
        case Objectives.Worse{} Objectives.Better{}:
          {==}
        case Objectives.Worse{} Objectives.Same{}:
          {==}
        case Objectives.Worse{} Objectives.Worse{}:
          {==}
        case Objectives.Worse{} Objectives.Missing{}:
          {==}
        case Objectives.Missing{} Objectives.Better{}:
          {==}
        case Objectives.Missing{} Objectives.Same{}:
          {==}
        case Objectives.Missing{} Objectives.Worse{}:
          {==}
        case Objectives.Missing{} Objectives.Missing{}:
          {==}
    case Objectives.Incomplete{}:
      {==}

# Structural induction, generalized to every accumulator and inserted order.
def fold_step(+rows: List<&2, Objectives.Observation>, +state: Objectives.Relation, +order: Objectives.Order)
  -> {Selection.fold(rows, Selection.step(state, order)) ==
    Selection.step(Selection.fold(rows, state), order) : Objectives.Relation}:
  match rows:
    case Nil{}:
      {==}
    case Objectives.Observation{family, next} <> rest:
      match family:
        case Objectives.Quality{}:
          %step_commute(state, next, order) : {Selection.fold(rest, _) == Selection.step(Selection.fold(rest, Selection.step(state, next)), order) : Objectives.Relation}
          fold_step(rest, Selection.step(state, next), order)
        case Objectives.Throughput{}:
          %step_commute(state, next, order) : {Selection.fold(rest, _) == Selection.step(Selection.fold(rest, Selection.step(state, next)), order) : Objectives.Relation}
          fold_step(rest, Selection.step(state, next), order)
        case Objectives.FirstToken{}:
          %step_commute(state, next, order) : {Selection.fold(rest, _) == Selection.step(Selection.fold(rest, Selection.step(state, next)), order) : Objectives.Relation}
          fold_step(rest, Selection.step(state, next), order)
        case Objectives.Energy{}:
          fold_step(rest, state, order)

def Laws.classify_semantics(rows):
  match rows:
    case Nil{}:
      {==}
    case Objectives.Observation{family, order} <> rest:
      match family:
        case Objectives.Quality{}:
          %spec_step(Objectives.primary(rest), order) : {Selection.fold(rest, Selection.step(Objectives.NoObjectives{}, order)) == _ : Objectives.Relation}
          %Laws.classify_semantics(rest) : {Selection.fold(rest, Selection.step(Objectives.NoObjectives{}, order)) == Selection.step(_, order) : Objectives.Relation}
          fold_step(rest, Objectives.NoObjectives{}, order)
        case Objectives.Throughput{}:
          %spec_step(Objectives.primary(rest), order) : {Selection.fold(rest, Selection.step(Objectives.NoObjectives{}, order)) == _ : Objectives.Relation}
          %Laws.classify_semantics(rest) : {Selection.fold(rest, Selection.step(Objectives.NoObjectives{}, order)) == Selection.step(_, order) : Objectives.Relation}
          fold_step(rest, Objectives.NoObjectives{}, order)
        case Objectives.FirstToken{}:
          %spec_step(Objectives.primary(rest), order) : {Selection.fold(rest, Selection.step(Objectives.NoObjectives{}, order)) == _ : Objectives.Relation}
          %Laws.classify_semantics(rest) : {Selection.fold(rest, Selection.step(Objectives.NoObjectives{}, order)) == Selection.step(_, order) : Objectives.Relation}
          fold_step(rest, Objectives.NoObjectives{}, order)
        case Objectives.Energy{}:
          Laws.classify_semantics(rest)

# A fold compositionality theorem gives report-only invariance at any position.
def fold_append(+prefix: List<&2, Objectives.Observation>, +suffix: List<&2, Objectives.Observation>, +state: Objectives.Relation)
  -> {Selection.fold(List.append(&2, Objectives.Observation, prefix, suffix), state) ==
    Selection.fold(suffix, Selection.fold(prefix, state)) : Objectives.Relation}:
  match prefix:
    case Nil{}:
      {==}
    case Objectives.Observation{family, order} <> rest:
      match family:
        case Objectives.Quality{}:
          fold_append(rest, suffix, Selection.step(state, order))
        case Objectives.Throughput{}:
          fold_append(rest, suffix, Selection.step(state, order))
        case Objectives.FirstToken{}:
          fold_append(rest, suffix, Selection.step(state, order))
        case Objectives.Energy{}:
          fold_append(rest, suffix, state)

def Laws.report_only_invariance(prefix, order, suffix):
  %Equal.sym(Objectives.Relation,
    Selection.fold(List.append(&2, Objectives.Observation, prefix, Objectives.Observation{Objectives.Energy{}, order} <> suffix), Objectives.NoObjectives{}),
    Selection.fold(Objectives.Observation{Objectives.Energy{}, order} <> suffix, Selection.fold(prefix, Objectives.NoObjectives{})),
    fold_append(prefix, Objectives.Observation{Objectives.Energy{}, order} <> suffix, Objectives.NoObjectives{})) :
    {_ == Selection.classify(List.append(&2, Objectives.Observation, prefix, suffix)) : Objectives.Relation}
  Equal.sym(Objectives.Relation,
    Selection.fold(List.append(&2, Objectives.Observation, prefix, suffix), Objectives.NoObjectives{}),
    Selection.fold(suffix, Selection.fold(prefix, Objectives.NoObjectives{})),
    fold_append(prefix, suffix, Objectives.NoObjectives{}))

def equivalent_gain(kinds: List<&2, Objectives.Family>)
  -> {Selection.fold(Objectives.equivalent_rows(kinds), Objectives.Dominates{}) == Objectives.Dominates{} : Objectives.Relation}:
  match kinds:
    case Nil{}:
      {==}
    case family <> rest:
      match family:
        case Objectives.Quality{}:
          equivalent_gain(rest)
        case Objectives.Throughput{}:
          equivalent_gain(rest)
        case Objectives.FirstToken{}:
          equivalent_gain(rest)
        case Objectives.Energy{}:
          equivalent_gain(rest)

def Laws.quality_only_improvement(kinds):
  equivalent_gain(kinds)

def Laws.no_speed_improvement_required(kinds, energy):
  equivalent_gain(kinds)

# Constructor discrimination is derived by transport, never asserted.
def Truth(value: Bool) -> Type:
  match value:
    case True{}:
      Unit
    case False{}:
      Empty

def true_not_false(e: {True{} == False{} : Bool}) -> Empty:
  %e : Truth(_)
  Unit{}

def spec_missing(+xs: List<&2, Objectives.Order>, missing: {Objectives.known(xs) == False{} : Bool})
  -> {Objectives.classify_orders(xs) == Objectives.Incomplete{} : Objectives.Relation}:
  match xs:
    case Nil{}:
      Empty.absurd({Objectives.NoObjectives{} == Objectives.Incomplete{} : Objectives.Relation}, true_not_false(missing))
    case h <> t:
      %Equal.sym(Bool, Objectives.known(h <> t), False{}, missing) : {Objectives.relation(True{}, _, Objectives.better(h <> t), Objectives.worse(h <> t)) == Objectives.Incomplete{} : Objectives.Relation}
      {==}

def Laws.missing_primary_rejected(rows, missing):
  %Equal.sym(Objectives.Relation, Selection.classify(rows), Objectives.classify(rows), Laws.classify_semantics(rows)) : {_ == Objectives.Incomplete{} : Objectives.Relation}
  spec_missing(Objectives.primary(rows), missing)

def spec_mixed(+xs: List<&2, Objectives.Order>,
    known: {Objectives.known(xs) == True{} : Bool},
    gain: {Objectives.better(xs) == True{} : Bool},
    loss: {Objectives.worse(xs) == True{} : Bool})
  -> {Objectives.classify_orders(xs) == Objectives.Tradeoff{} : Objectives.Relation}:
  match xs:
    case Nil{}:
      Empty.absurd({Objectives.NoObjectives{} == Objectives.Tradeoff{} : Objectives.Relation},
        true_not_false(Equal.sym(Bool, False{}, True{}, gain)))
    case h <> t:
      %Equal.sym(Bool, Objectives.known(h <> t), True{}, known) : {Objectives.relation(True{}, _, Objectives.better(h <> t), Objectives.worse(h <> t)) == Objectives.Tradeoff{} : Objectives.Relation}
      %Equal.sym(Bool, Objectives.better(h <> t), True{}, gain) : {Objectives.relation(True{}, True{}, _, Objectives.worse(h <> t)) == Objectives.Tradeoff{} : Objectives.Relation}
      %Equal.sym(Bool, Objectives.worse(h <> t), True{}, loss) : {Objectives.relation(True{}, True{}, True{}, _) == Objectives.Tradeoff{} : Objectives.Relation}
      {==}

def Laws.mixed_gain_loss_incomparable(rows, known, gain, loss):
  %Equal.sym(Objectives.Relation, Selection.classify(rows), Objectives.classify(rows), Laws.classify_semantics(rows)) : {_ == Objectives.Tradeoff{} : Objectives.Relation}
  spec_mixed(Objectives.primary(rows), known, gain, loss)

# Separate transition evaluation from decimal rendering. The payload proof
# still checks every byte against the independently fixed wire literal, but
# never unfolds Selection.step while traversing the serialized string.
def policy_payload(-roles: List<&2, Nat>, -transitions: List<&2, Nat>,
    roles_equal: {roles == [0n, 0n, 0n, 1n] : List<&2, Nat>},
    transitions_equal: {transitions ==
      [2n, 1n, 3n, 5n, 2n, 1n, 3n, 5n, 2n, 2n, 4n, 5n,
        4n, 3n, 3n, 5n, 4n, 4n, 4n, 5n, 5n, 5n, 5n, 5n] : List<&2, Nat>})
  -> {"QWEN_OBJECTIVE_POLICY_V1\nROLES\n" ++ Wire.rows(roles) ++
    "TRANSITIONS\n" ++ Wire.rows(transitions) ++ "END_QWEN_OBJECTIVE_POLICY" ==
    Laws.expected_wire() : String}:
  %Equal.sym(List<&2, Nat>, roles, [0n, 0n, 0n, 1n], roles_equal) :
    {"QWEN_OBJECTIVE_POLICY_V1\nROLES\n" ++ Wire.rows(_) ++
      "TRANSITIONS\n" ++ Wire.rows(transitions) ++ "END_QWEN_OBJECTIVE_POLICY" ==
      Laws.expected_wire() : String}
  %Equal.sym(List<&2, Nat>, transitions,
    [2n, 1n, 3n, 5n, 2n, 1n, 3n, 5n, 2n, 2n, 4n, 5n,
      4n, 3n, 3n, 5n, 4n, 4n, 4n, 5n, 5n, 5n, 5n, 5n], transitions_equal) :
    {"QWEN_OBJECTIVE_POLICY_V1\nROLES\n" ++ Wire.rows([0n, 0n, 0n, 1n]) ++
      "TRANSITIONS\n" ++ Wire.rows(_) ++ "END_QWEN_OBJECTIVE_POLICY" ==
      Laws.expected_wire() : String}
  {==}

def Laws.policy_wire():
  policy_payload(Wire.roles(),
    Wire.table([Objectives.NoObjectives{}, Objectives.Equivalent{},
      Objectives.Dominates{}, Objectives.Dominated{}, Objectives.Tradeoff{},
      Objectives.Incomplete{}]), {==}, {==})
