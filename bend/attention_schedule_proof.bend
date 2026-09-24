# Exhaustive finite policy cases, full-state constructor equality and structural
# ordered-list induction. No holes, unsafe code, foreign bodies or native axioms.
import Base
import ./attention_schedule.bend as Impl
import ./attention_schedule_spec.bend as Spec
import ./attention_schedule_laws.bend as Laws

def Laws.policy_refinement(head256, rows32):
  match head256 rows32:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Laws.action_range(head256, rows32):
  match head256:
    case False{}:
      Unit{}
    case True{}:
      match rows32:
        case False{}:
          Unit{}
        case True{}:
          Unit{}

def Laws.head_fallback(rows32):
  {==}

def Laws.rows_fallback(head256):
  match head256:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.late_value_progress():
  {==}

def Laws.table_order():
  ({==}, {==})

def Laws.table_lookup(head256, rows32):
  match head256 rows32:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Laws.wire_exact():
  {==}

def Laws.packed_guard_exact(input):
  {==}

def Laws.raw_guard_exact(input):
  {==}

def Laws.packed_value_operands(input):
  {==}

def Laws.packed_scores_exact(input, keys, maximum):
  {==}

def Laws.packed_maximum_exact(input, keys, maximum):
  {==}

def Laws.packed_live_exact(input, keys, maximum):
  {==}

def Laws.packed_entering_maximum(input, keys, maximum):
  {==}

def Laws.packed_probability_exact(input, keys, maximum):
  {==}

def Laws.packed_value_softmax_commutes(input, state):
  match state:
    case Spec.State{keys, values, softmax, maximum, denominator, raw, rotated, status}:
      {==}

# The commutation lemma is actually used, then the unchanged PV update is
# applied to both complete states. K preparation stays before either schedule.
def Laws.packed_late_value_state(input, state):
  +prepared = Spec.prepare_keys(input, state)
  Equal.cong(Spec.State, Spec.State, Spec.packed_update,
    Spec.load_value(input, Spec.score_softmax(input, prepared)),
    Spec.score_softmax(input, Spec.load_value(input, prepared)),
    Equal.sym(Spec.State,
      Spec.score_softmax(input, Spec.load_value(input, prepared)),
      Spec.load_value(input, Spec.score_softmax(input, prepared)),
      Laws.packed_value_softmax_commutes(input, prepared)))

def Laws.packed_update_exact(keys, values, scores, next, live, alpha,
    probability, maximum, denominator, raw, rotated, status):
  {==}

def Laws.selected_packed_state(head256, rows32, input, state):
  match head256 rows32:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      Laws.packed_late_value_state(input, state)

def Laws.selected_target_schedule(input, state):
  {==}

def Laws.selected_head_fallback(rows32, input, state):
  {==}

def Laws.selected_rows_fallback(head256, input, state):
  match head256:
    case False{}:
      {==}
    case True{}:
      {==}

# Every guard combination, with post-raw state passed into the selected packed
# theorem. Neither skipped pass is simulated by evaluating zero-probability PV.
def Laws.guarded_block_state(block, head256, rows32, state):
  match block:
    case Spec.Block{input, False{}, False{}}:
      {==}
    case Spec.Block{input, False{}, True{}}:
      Laws.selected_packed_state(head256, rows32, input, state)
    case Spec.Block{input, True{}, False{}}:
      {==}
    case Spec.Block{+input, True{}, True{}}:
      Laws.selected_packed_state(head256, rows32, input, Spec.raw_step(input, state))

def Laws.packed_skip(head256, rows32, input, state):
  {==}

def Laws.inactive_block(input, head256, rows32, state):
  {==}

def Laws.raw_only_block(input, head256, rows32, state):
  {==}

def Laws.mixed_raw_before_packed(input, head256, rows32, state):
  Laws.selected_packed_state(head256, rows32, input, Spec.raw_step(input, state))

# The inductive hypothesis is universally quantified over the incoming state;
# it therefore applies to the arbitrary post-block state, not only zero starts.
def Laws.late_value_recurrence(blocks, head256, rows32, state):
  match blocks:
    case Nil{}:
      {==}
    case +block <> +rest:
      Equal.trans(Spec.State,
        Laws.selected_run(block <> rest, head256, rows32, state),
        Laws.selected_run(rest, head256, rows32, Spec.reference_block(block, state)),
        Spec.reference_run(block <> rest, state),
        Equal.cong(Spec.State, Spec.State,
          next => Laws.selected_run(rest, head256, rows32, next),
          Laws.selected_block(block, head256, rows32, state), Spec.reference_block(block, state),
          Laws.guarded_block_state(block, head256, rows32, state)),
        Laws.late_value_recurrence(rest, head256, rows32, Spec.reference_block(block, state)))

def Laws.empty_recurrence(head256, rows32, state):
  {==}

def Laws.postprocessing_invariant(blocks, head256, rows32, input, state):
  Equal.cong(Spec.State, Spec.Stored, next => Spec.finish(input, next),
    Laws.selected_run(blocks, head256, rows32, state), Spec.reference_run(blocks, state),
    Laws.late_value_recurrence(blocks, head256, rows32, state))

def Laws.partition_outputs_invariant(partitions, head256, rows32):
  match partitions:
    case Nil{}:
      {==}
    case Spec.Partition{+input, +blocks, +initial} <> +rest:
      Equal.trans(List<&2, Spec.Stored>,
        Laws.selected_outputs(Spec.Partition{input, blocks, initial} <> rest, head256, rows32),
        Spec.finish(input, Spec.reference_run(blocks, initial)) <>
          Laws.selected_outputs(rest, head256, rows32),
        Spec.reference_outputs(Spec.Partition{input, blocks, initial} <> rest),
        Equal.cong(Spec.Stored, List<&2, Spec.Stored>,
          stored => stored <> Laws.selected_outputs(rest, head256, rows32),
          Spec.finish(input, Laws.selected_run(blocks, head256, rows32, initial)),
          Spec.finish(input, Spec.reference_run(blocks, initial)),
          Laws.postprocessing_invariant(blocks, head256, rows32, input, initial)),
        Equal.cong(List<&2, Spec.Stored>, List<&2, Spec.Stored>,
          stored => Spec.finish(input, Spec.reference_run(blocks, initial)) <> stored,
          Laws.selected_outputs(rest, head256, rows32), Spec.reference_outputs(rest),
          Laws.partition_outputs_invariant(rest, head256, rows32)))

def Laws.reducer_input_invariant(partitions, head256, rows32):
  Equal.cong(List<&2, Spec.Stored>, Spec.Reduced, partials => Spec.Reduced{partials},
    Laws.selected_outputs(partitions, head256, rows32), Spec.reference_outputs(partitions),
    Laws.partition_outputs_invariant(partitions, head256, rows32))
