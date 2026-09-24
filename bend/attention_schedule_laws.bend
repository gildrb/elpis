# Production policy and exact symbolic scheduling laws. All model types remain
# proof-only. Native correspondence premises are documented in the spec, not
# invented as axioms or silently discharged by ownership-model theorems.
import Base
import ./attention_schedule.bend as Impl
import ./attention_schedule_spec.bend as Spec
import ./RUNTIME.bend as Wire

law policy_refinement:
  for +head256: Bool
  for +rows32: Bool
  {Impl.late_value(head256, rows32) == Spec.late_value(head256, rows32) : Nat}

law action_range:
  for head256: Bool
  for rows32: Bool
  Spec.Action(Impl.late_value(head256, rows32))

law head_fallback:
  for rows32: Bool
  {Impl.late_value(False{}, rows32) == 0n : Nat}

law rows_fallback:
  for head256: Bool
  {Impl.late_value(head256, False{}) == 0n : Nat}

law late_value_progress:
  {Impl.late_value(True{}, True{}) == 1n : Nat}

law table_order:
  {Impl.table(2n, False{}, False{}) == [0n, 0n, 0n, 1n] : List<&2, Nat>} &
  {Impl.table(2n, False{}, False{}) ==
    [Spec.row(0n), Spec.row(1n), Spec.row(2n), Spec.row(3n)] : List<&2, Nat>}

law table_lookup:
  for +head256: Bool
  for +rows32: Bool
  {Spec.row(Nat.add(Bool.pick(Nat, head256, 1n, 0n),
    Nat.mul(2n, Bool.pick(Nat, rows32, 1n, 0n)))) == Impl.late_value(head256, rows32) : Nat}

law wire_exact:
  {Wire.protocol() == Spec.protocol() : String}

# Source mask identities: block-wide any over the actual representation mask,
# NOT page_ok or per-row guards. V/K loads still use page_ok in the spec.
law packed_guard_exact:
  for +input: Spec.Input
  {Spec.packed_guard(input) == Spec.Greater{Spec.AllSum{Spec.I32{
    Spec.And{Spec.Ref{input, Spec.Valid{}}, Spec.Not{Spec.Column{Spec.Ref{input, Spec.UseRaw{}}}}}}},
    Spec.Zero{}} : Spec.Expr}

law raw_guard_exact:
  for +input: Spec.Input
  {Spec.raw_guard(input) == Spec.Greater{Spec.AllSum{Spec.I32{
    Spec.And{Spec.Column{Spec.Ref{input, Spec.UseRaw{}}}, Spec.Ref{input, Spec.Valid{}}}}},
    Spec.Zero{}} : Spec.Expr}

# Exact ordered source chains make cast/mask/entering-maximum mistakes fail
# independently of commutation (two equally wrong schedules could commute).
law packed_value_operands:
  for +input: Spec.Input
  {Spec.packed_values(input) == Spec.Values{
    Spec.F32{Spec.Load{input, Spec.VChannel{}, Spec.Ref{input, Spec.PageOK{}}, Spec.Zero{}}},
    Spec.F32{Spec.Load{input, Spec.VScale{}, Spec.Ref{input, Spec.PageOK{}}, Spec.Zero{}}},
    Spec.F32{Spec.Load{input, Spec.VZero{}, Spec.Ref{input, Spec.PageOK{}}, Spec.Zero{}}},
    Spec.I32{Spec.Load{input, Spec.VByte{}, Spec.Ref{input, Spec.PageOK{}}, Spec.Zero{}}},
    Spec.Mul{Spec.Add{Spec.Mul{
      Spec.F32{Spec.Bits{Spec.Shift{
        Spec.I32{Spec.Load{input, Spec.VByte{}, Spec.Ref{input, Spec.PageOK{}}, Spec.Zero{}}},
        Spec.Mul{Spec.Mod{Spec.Row{Spec.Ref{input, Spec.Channel{}}}, Spec.Number{4n}}, Spec.Number{2n}}},
        Spec.Number{3n}}},
      Spec.Column{Spec.F32{Spec.Load{input, Spec.VScale{}, Spec.Ref{input, Spec.PageOK{}}, Spec.Zero{}}}}},
      Spec.Column{Spec.F32{Spec.Load{input, Spec.VZero{}, Spec.Ref{input, Spec.PageOK{}}, Spec.Zero{}}}}},
      Spec.Row{Spec.F32{Spec.Load{input, Spec.VChannel{}, Spec.Ref{input, Spec.PageOK{}}, Spec.Zero{}}}}}}
    : Spec.Values}

law packed_scores_exact:
  for +input: Spec.Input
  for +keys: Spec.Expr
  for maximum: Spec.Expr
  {Spec.scores(Spec.packed_softmax(input, keys, maximum)) ==
    Spec.Where{Spec.And{Spec.Ref{input, Spec.Valid{}}, Spec.Not{Spec.Column{Spec.Ref{input, Spec.UseRaw{}}}}},
      Spec.Mul{Spec.Dot{Spec.F16{Spec.Ref{input, Spec.RotatedQuery{}}}, Spec.F16{keys}},
        Spec.Ref{input, Spec.Scale{}}}, Spec.NegInfinity{}} : Spec.Expr}

law packed_maximum_exact:
  for +input: Spec.Input
  for +keys: Spec.Expr
  for +maximum: Spec.Expr
  {Spec.next_maximum(Spec.packed_softmax(input, keys, maximum)) ==
    Spec.Maximum{maximum, Spec.RowMax{Spec.scores(Spec.packed_softmax(input, keys, maximum))}} : Spec.Expr}

law packed_live_exact:
  for +input: Spec.Input
  for +keys: Spec.Expr
  for +maximum: Spec.Expr
  {Spec.live(Spec.packed_softmax(input, keys, maximum)) ==
    Spec.Greater{Spec.next_maximum(Spec.packed_softmax(input, keys, maximum)), Spec.NegInfinity{}} : Spec.Expr}

law packed_entering_maximum:
  for +input: Spec.Input
  for +keys: Spec.Expr
  for +maximum: Spec.Expr
  {Spec.alpha(Spec.packed_softmax(input, keys, maximum)) ==
    Spec.Where{Spec.live(Spec.packed_softmax(input, keys, maximum)),
      Spec.Exp{Spec.Sub{maximum, Spec.next_maximum(Spec.packed_softmax(input, keys, maximum))}},
      Spec.Zero{}} : Spec.Expr}

law packed_probability_exact:
  for +input: Spec.Input
  for +keys: Spec.Expr
  for +maximum: Spec.Expr
  {Spec.probability(Spec.packed_softmax(input, keys, maximum)) ==
    Spec.Where{Spec.And{Spec.And{Spec.Column{Spec.live(Spec.packed_softmax(input, keys, maximum))},
      Spec.Ref{input, Spec.Valid{}}}, Spec.Not{Spec.Column{Spec.Ref{input, Spec.UseRaw{}}}}},
      Spec.Exp{Spec.Sub{Spec.scores(Spec.packed_softmax(input, keys, maximum)),
        Spec.Column{Spec.next_maximum(Spec.packed_softmax(input, keys, maximum))}}}, Spec.Zero{}} : Spec.Expr}

# Full state, including all temporary results, arbitrary old max/denominator,
# both accumulators and sticky status. These transitions read the SAME snapshot.
law packed_value_softmax_commutes:
  for +input: Spec.Input
  for +state: Spec.State
  {Spec.score_softmax(input, Spec.load_value(input, state)) ==
    Spec.load_value(input, Spec.score_softmax(input, state)) : Spec.State}

law packed_late_value_state:
  for +input: Spec.Input
  for +state: Spec.State
  {Spec.late_packed(input, state) == Spec.early_packed(input, state) : Spec.State}

# Pin the four ordered output expressions, including BOTH FP16 PV conversions;
# no arithmetic identity hides rescaling, maximum order or a changed accumulator.
law packed_update_exact:
  for +keys: Spec.Expr
  for +values: Spec.Values
  for +scores: Spec.Expr
  for +next: Spec.Expr
  for +live: Spec.Expr
  for +alpha: Spec.Expr
  for +probability: Spec.Expr
  for maximum: Spec.Expr
  for +denominator: Spec.Expr
  for +raw: Spec.Expr
  for +rotated: Spec.Expr
  for +status: Spec.Expr
  {Spec.packed_update(Spec.State{keys, values, Spec.Softmax{scores, next, live, alpha, probability},
    maximum, denominator, raw, rotated, status}) ==
    Spec.State{keys, values, Spec.Softmax{scores, next, live, alpha, probability}, next,
      Spec.Add{Spec.Mul{denominator, alpha}, Spec.RowSum{probability}},
      Spec.Mul{raw, Spec.Column{alpha}},
      Spec.Add{Spec.Mul{rotated, Spec.Column{alpha}},
        Spec.Dot{Spec.F16{probability}, Spec.F16{Spec.dequantized(values)}}}, status} : Spec.State}

# The actual compiled decision chooses the composition used by the recurrence.
# 0 retains early V; the proved 0/1 action range excludes every other native row.
def scheduled_packed(action: Nat, input: Spec.Input, state: Spec.State) -> Spec.State:
  match action:
    case 0n:
      Spec.early_packed(input, state)
    case 1n+p:
      Spec.late_packed(input, state)

def selected_packed(head256: Bool, rows32: Bool, input: Spec.Input, state: Spec.State) -> Spec.State:
  scheduled_packed(Impl.late_value(head256, rows32), input, state)

def selected_packed_if(enabled: Bool, head256: Bool, rows32: Bool,
    input: Spec.Input, state: Spec.State) -> Spec.State:
  match enabled:
    case False{}:
      state
    case True{}:
      selected_packed(head256, rows32, input, state)

def selected_block(block: Spec.Block, head256: Bool, rows32: Bool, state: Spec.State) -> Spec.State:
  match block:
    case Spec.Block{+input, raw_any, packed_any}:
      selected_packed_if(packed_any, head256, rows32, input, Spec.raw_if(raw_any, input, state))

law selected_packed_state:
  for +head256: Bool
  for +rows32: Bool
  for +input: Spec.Input
  for +state: Spec.State
  {selected_packed(head256, rows32, input, state) == Spec.early_packed(input, state) : Spec.State}

law selected_target_schedule:
  for +input: Spec.Input
  for +state: Spec.State
  {selected_packed(True{}, True{}, input, state) == Spec.late_packed(input, state) : Spec.State}

law selected_head_fallback:
  for rows32: Bool
  for +input: Spec.Input
  for +state: Spec.State
  {selected_packed(False{}, rows32, input, state) == Spec.early_packed(input, state) : Spec.State}

law selected_rows_fallback:
  for head256: Bool
  for +input: Spec.Input
  for +state: Spec.State
  {selected_packed(head256, False{}, input, state) == Spec.early_packed(input, state) : Spec.State}

law guarded_block_state:
  for +block: Spec.Block
  for head256: Bool
  for rows32: Bool
  for +state: Spec.State
  {selected_block(block, head256, rows32, state) == Spec.reference_block(block, state) : Spec.State}

law packed_skip:
  for head256: Bool
  for rows32: Bool
  for input: Spec.Input
  for +state: Spec.State
  {selected_packed_if(False{}, head256, rows32, input, state) == state : Spec.State}

law inactive_block:
  for input: Spec.Input
  for head256: Bool
  for rows32: Bool
  for +state: Spec.State
  {selected_block(Spec.Block{input, False{}, False{}}, head256, rows32, state) == state : Spec.State}

law raw_only_block:
  for +input: Spec.Input
  for head256: Bool
  for rows32: Bool
  for +state: Spec.State
  {selected_block(Spec.Block{input, True{}, False{}}, head256, rows32, state) ==
    Spec.raw_step(input, state) : Spec.State}

law mixed_raw_before_packed:
  for +input: Spec.Input
  for head256: Bool
  for rows32: Bool
  for +state: Spec.State
  {selected_block(Spec.Block{input, True{}, True{}}, head256, rows32, state) ==
    Spec.early_packed(input, Spec.raw_step(input, state)) : Spec.State}

# The first (structurally decreasing) argument is the SAME ordered block list.
# Each recursive call threads the entire previous state, never a zero reset.
def selected_run(blocks: List<&2, Spec.Block>, +head256: Bool, +rows32: Bool,
    state: Spec.State) -> Spec.State:
  match blocks:
    case Nil{}:
      state
    case block <> rest:
      selected_run(rest, head256, rows32, selected_block(block, head256, rows32, state))

law late_value_recurrence:
  for +blocks: List<&2, Spec.Block>
  for +head256: Bool
  for +rows32: Bool
  for +state: Spec.State
  {selected_run(blocks, head256, rows32, state) == Spec.reference_run(blocks, state) : Spec.State}

law empty_recurrence:
  for head256: Bool
  for rows32: Bool
  for +state: Spec.State
  {selected_run(Nil{}, head256, rows32, state) == state : Spec.State}

law postprocessing_invariant:
  for +blocks: List<&2, Spec.Block>
  for head256: Bool
  for rows32: Bool
  for +input: Spec.Input
  for +state: Spec.State
  {Spec.finish(input, selected_run(blocks, head256, rows32, state)) ==
    Spec.finish(input, Spec.reference_run(blocks, state)) : Spec.Stored}

# Preserve every original query tile/split and its independently supplied reset.
# Ordered split reduction is lifted by congruence, not rearranged or re-proved.
def selected_outputs(partitions: List<&2, Spec.Partition>, +head256: Bool, +rows32: Bool)
    -> List<&2, Spec.Stored>:
  match partitions:
    case Nil{}:
      Nil{}
    case Spec.Partition{input, blocks, initial} <> rest:
      Spec.finish(input, selected_run(blocks, head256, rows32, initial)) <>
        selected_outputs(rest, head256, rows32)

law partition_outputs_invariant:
  for +partitions: List<&2, Spec.Partition>
  for +head256: Bool
  for +rows32: Bool
  {selected_outputs(partitions, head256, rows32) == Spec.reference_outputs(partitions) : List<&2, Spec.Stored>}

law reducer_input_invariant:
  for +partitions: List<&2, Spec.Partition>
  for head256: Bool
  for rows32: Bool
  {Spec.Reduced{selected_outputs(partitions, head256, rows32)} ==
    Spec.Reduced{Spec.reference_outputs(partitions)} : Spec.Reduced}
