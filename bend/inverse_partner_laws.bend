# Bounded transport and ordered symbolic-expression refinement, linked to the
# actual independent startup selector. Native source/compiler claims excluded.
import Base
import ./inverse_partner.bend as Impl
import ./inverse_partner_spec.bend as Spec
import ./attention_schedule_spec.bend as Attention
import ./numerical_spec.bend as Order

law policy_refinement:
  for +head256: Bool
  for +rows32: Bool
  {Impl.inverse_partner(head256, rows32) == Spec.inverse_partner(head256, rows32) : Nat}

law action_range:
  for head256: Bool
  for rows32: Bool
  Spec.Action(Impl.inverse_partner(head256, rows32))

law head_fallback:
  for rows32: Bool
  {Impl.inverse_partner(False{}, rows32) == 0n : Nat}

law rows_fallback:
  for head256: Bool
  {Impl.inverse_partner(head256, False{}) == 0n : Nat}

law target_progress:
  {Impl.inverse_partner(True{}, True{}) == 1n : Nat}

law table_order:
  {Impl.table(2n, False{}, False{}) == [0n, 0n, 0n, 1n] : List<&2, Nat>} &
  {Impl.table(2n, False{}, False{}) ==
    [Spec.row(0n), Spec.row(1n), Spec.row(2n), Spec.row(3n)] : List<&2, Nat>}

law table_lookup:
  for +head256: Bool
  for +rows32: Bool
  {Spec.row(Nat.add(Bool.pick(Nat, head256, 1n, 0n),
    Nat.mul(2n, Bool.pick(Nat, rows32, 1n, 0n)))) == Impl.inverse_partner(head256, rows32) : Nat}

# Source-chain anchors: these fail independently if both endpoint models are
# changed together. Transpose/split/join axis order is explicit, not named XOR.
law transport_chain:
  for +row: Nat
  for +group: Nat
  for +high: Bool
  for +offset: Nat
  {Spec.transport(Spec.Coord{row, group, high, offset}) ==
    Spec.Coord{row, group, Bool.not(high), offset} : Spec.Coord}

law split_join_planes:
  for +row: Nat
  for +group: Nat
  for +offset: Nat
  {Spec.split_join(Spec.Transposed{row, group, offset, False{}}) ==
    Spec.Transposed{row, group, offset, True{}} : Spec.Transposed} &
  {Spec.split_join(Spec.Transposed{row, group, offset, True{}}) ==
    Spec.Transposed{row, group, offset, False{}} : Spec.Transposed}

law reference_bit_chain:
  for +stage: Nat
  for +lane: Nat
  {Spec.reference_partner(stage, lane) ==
    Order.value(Spec.xor_bits(Spec.bits(8n, lane), Spec.one_hot(8n, stage, 0n))) : Nat} &
  {Spec.reference_mask(stage, lane) ==
    Order.value(Spec.and_bits(Spec.bits(8n, lane), Spec.one_hot(8n, stage, 0n))) : Nat}

# The reference mask really is the native single-bit 1 << stage, not merely
# a helper named one_hot. Only the selected native stages 0..7 are admitted.
law one_hot_mask:
  for +stage: Nat
  for bounded: Order.Le(1n+stage, 8n)
  {Order.value(Spec.one_hot(8n, stage, 0n)) == Order.power2(stage) : Nat}

law coordinate_table:
  for +kind: Spec.Check
  {Spec.stage_checks(8n, 0n, kind) == True{} : Bool}

law bounded_coordinate:
  for +kind: Spec.Check
  for +stage: Nat
  for +lane: Nat
  for stage_bound: Order.Le(1n+stage, 8n)
  for lane_bound: Order.Le(1n+lane, 256n)
  {Spec.check(kind, stage, lane) == True{} : Bool}

# Completeness for every selected native lane (not only pre-decomposed lanes).
# Universal row is carried through every map without arithmetic or wraparound.
law coordinate_coverage:
  for +stage: Nat
  for +row: Nat
  for +lane: Nat
  for +stage_bound: Order.Le(1n+stage, 8n)
  for +lane_bound: Order.Le(1n+lane, 256n)
  {Spec.flatten(stage, Spec.reshape(stage, row, lane)) == lane : Nat} &
  {Order.value(Spec.bits(8n, lane)) == lane : Nat} &
  Order.Le(1n+Spec.coordinate_group(Spec.reshape(stage, row, lane)),
    Nat.div(256n, Nat.double(Order.power2(stage)))) &
  Order.Le(1n+Spec.coordinate_offset(Spec.reshape(stage, row, lane)), Order.power2(stage))

law row_and_axes_preserved:
  for +stage: Nat
  for +row: Nat
  for +lane: Nat
  {Spec.coordinate_row(Spec.transport(Spec.reshape(stage, row, lane))) == row : Nat} &
  {Spec.coordinate_group(Spec.transport(Spec.reshape(stage, row, lane))) ==
    Spec.coordinate_group(Spec.reshape(stage, row, lane)) : Nat} &
  {Spec.coordinate_offset(Spec.transport(Spec.reshape(stage, row, lane))) ==
    Spec.coordinate_offset(Spec.reshape(stage, row, lane)) : Nat} &
  {Spec.flatten(stage, Spec.transport(Spec.reshape(stage, row, lane))) ==
    Spec.selected_partner(stage, lane) : Nat}

law partner_exact:
  for +stage: Nat
  for +lane: Nat
  for stage_bound: Order.Le(1n+stage, 8n)
  for lane_bound: Order.Le(1n+lane, 256n)
  {Spec.selected_partner(stage, lane) == Spec.reference_partner(stage, lane) : Nat}

law branch_bit:
  for +stage: Nat
  for +lane: Nat
  for stage_bound: Order.Le(1n+stage, 8n)
  for lane_bound: Order.Le(1n+lane, 256n)
  {Spec.selected_low(stage, lane) == Spec.reference_low(stage, lane) : Bool}

law partner_bound:
  for +stage: Nat
  for +lane: Nat
  for stage_bound: Order.Le(1n+stage, 8n)
  for lane_bound: Order.Le(1n+lane, 256n)
  Order.Le(1n+Spec.selected_partner(stage, lane), 256n)

law partner_involution:
  for +stage: Nat
  for +lane: Nat
  for stage_bound: Order.Le(1n+stage, 8n)
  for lane_bound: Order.Le(1n+lane, 256n)
  {Spec.selected_partner(stage, Spec.selected_partner(stage, lane)) == lane : Nat}

# Bounded total involution is surjective: partner(lane) is a bounded preimage.
law partner_surjective:
  for +stage: Nat
  for +lane: Nat
  for +stage_bound: Order.Le(1n+stage, 8n)
  for +lane_bound: Order.Le(1n+lane, 256n)
  exs source: Nat
  Order.Le(1n+source, 256n) & {Spec.selected_partner(stage, source) == lane : Nat}

law partner_injective:
  for +stage: Nat
  for +left: Nat
  for +right: Nat
  for +stage_bound: Order.Le(1n+stage, 8n)
  for left_bound: Order.Le(1n+left, 256n)
  for right_bound: Order.Le(1n+right, 256n)
  for same: {Spec.selected_partner(stage, left) == Spec.selected_partner(stage, right) : Nat}
  {left == right : Nat}

law butterfly_operands:
  for +low: Bool
  for +current: Attention.Expr
  for +partner: Attention.Expr
  {Spec.butterfly(low, current, partner) ==
    Attention.Where{Bool.pick(Attention.Expr, low, Attention.One{}, Attention.Zero{}),
      Attention.Add{current, partner}, Attention.Sub{partner, current}} : Attention.Expr}

# The selected mathematical branch is the original mask predicate. Both
# branches remain present and ordered even when that predicate is known.
law selected_stage_source:
  for +stage: Nat
  for +lane: Nat
  for +values: List<&2, Attention.Expr>
  for stage_bound: Order.Le(1n+stage, 8n)
  for lane_bound: Order.Le(1n+lane, 256n)
  {Spec.lift(Spec.selected_low(stage, lane), Spec.lookup(values, lane),
    Spec.lookup(values, Spec.selected_partner(stage, lane))) ==
    Spec.lift(Spec.reference_low(stage, lane), Spec.lookup(values, lane),
      Spec.lookup(values, Spec.selected_partner(stage, lane))) : Maybe<&2, Attention.Expr>}

law stage_refinement:
  for +stage: Nat
  for +lane: Nat
  for +values: List<&2, Attention.Expr>
  for +stage_bound: Order.Le(1n+stage, 8n)
  for +lane_bound: Order.Le(1n+lane, 256n)
  {Spec.lift(Spec.selected_low(stage, lane), Spec.lookup(values, lane),
    Spec.lookup(values, Spec.selected_partner(stage, lane))) ==
    Spec.lift(Spec.reference_low(stage, lane), Spec.lookup(values, lane),
      Spec.lookup(values, Spec.reference_partner(stage, lane))) : Maybe<&2, Attention.Expr>}

law exact_stage_order:
  {Spec.stages(Spec.count(True{})) == [0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n] : List<&2, Nat>} &
  {Spec.stages(Spec.count(False{})) == [0n, 1n, 2n, 3n, 4n, 5n, 6n] : List<&2, Nat>}

law native_stage_count:
  {Spec.count(True{}) == 8n : Nat} & {Spec.count(False{}) == 7n : Nat}

law action0_recurrence:
  for +count: Nat
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  {Spec.scheduled(count, 0n, values, lane) == Spec.reference(count, values, lane) : Maybe<&2, Attention.Expr>}

law ordered_recurrence:
  for +count: Nat
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  for +count_bound: Order.Le(count, 8n)
  for +lane_bound: Order.Le(1n+lane, 256n)
  {Spec.scheduled(count, 1n, values, lane) == Spec.reference(count, values, lane) : Maybe<&2, Attention.Expr>}

law reference_complete:
  for +count: Nat
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  for +count_bound: Order.Le(count, 8n)
  for +lane_bound: Order.Le(1n+lane, 256n)
  for +input_bound: Order.Le(256n, List.length(&2, Attention.Expr, values))
  Spec.Present(Spec.reference(count, values, lane))

# The prefix remains symbolic in expression theorems to avoid eagerly expanding
# concrete eight-stage trees in conversion checking. Every native-facing law
# explicitly pins it to count(head256), with the same <=8 bound. Instantiating
# prefix=count(head256) and reflexivity gives the original fixed native claim;
# native_stage_count/exact_stage_order pin eight/ seven and ascending order.
# This is a quantified exact-count theorem, NOT an opaque evaluator or axiom.
def selected(prefix: Nat, head256: Bool, rows32: Bool, values: List<&2, Attention.Expr>, lane: Nat)
    -> Maybe<&2, Attention.Expr>:
  Spec.scheduled(prefix, Impl.inverse_partner(head256, rows32), values, lane)

law selected_inverse_refinement:
  for +prefix: Nat
  for +head256: Bool
  for +rows32: Bool
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  for native_count: {prefix == Spec.count(head256) : Nat}
  for count_bound: Order.Le(prefix, 8n)
  for lane_bound: Order.Le(1n+lane, 256n)
  {selected(prefix, head256, rows32, values, lane) ==
    Spec.reference(prefix, values, lane) : Maybe<&2, Attention.Expr>}

law selected_complete:
  for +prefix: Nat
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  for native_count: {prefix == Spec.count(True{}) : Nat}
  for +count_bound: Order.Le(prefix, 8n)
  for +lane_bound: Order.Le(1n+lane, 256n)
  for input_bound: Order.Le(256n, List.length(&2, Attention.Expr, values))
  Spec.Present(selected(prefix, True{}, True{}, values, lane))

law selected_head_fallback:
  for +prefix: Nat
  for rows32: Bool
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  for native_count: {prefix == Spec.count(False{}) : Nat}
  for count_bound: Order.Le(prefix, 8n)
  {selected(prefix, False{}, rows32, values, lane) == Spec.reference(prefix, values, lane) : Maybe<&2, Attention.Expr>}

law selected_rows_fallback:
  for +prefix: Nat
  for +head256: Bool
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  for native_count: {prefix == Spec.count(head256) : Nat}
  for count_bound: Order.Le(prefix, 8n)
  {selected(prefix, head256, False{}, values, lane) ==
    Spec.reference(prefix, values, lane) : Maybe<&2, Attention.Expr>}

law finish_operands:
  for +input: Attention.Input
  for +keys: Attention.Expr
  for +values: Attention.Values
  for +softmax: Attention.Softmax
  for +maximum: Attention.Expr
  for +denominator: Attention.Expr
  for +raw: Attention.Expr
  for +rotated: Attention.Expr
  for +status: Attention.Expr
  for +inverse: Attention.Expr
  {Spec.finish(input, Attention.State{keys, values, softmax, maximum, denominator, raw, rotated, status}, inverse) ==
    Attention.Stored{input, Attention.Ref{input, Attention.RowReal{}},
      Attention.Div{Attention.Add{raw, Attention.Mul{inverse, Attention.Ref{input, Attention.Normalize{}}}},
        Attention.Column{Attention.Where{Attention.Greater{denominator, Attention.Zero{}}, denominator, Attention.One{}}}},
      Attention.Where{Attention.Greater{denominator, Attention.Zero{}},
        Attention.Add{maximum, Attention.Log{Attention.Where{Attention.Greater{denominator, Attention.Zero{}}, denominator, Attention.One{}}}},
        Attention.NegInfinity{}}, status} : Attention.Stored}

law finish_refinement:
  for +prefix: Nat
  for +head256: Bool
  for +rows32: Bool
  for +input: Attention.Input
  for +state: Attention.State
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  for native_count: {prefix == Spec.count(head256) : Nat}
  for count_bound: Order.Le(prefix, 8n)
  for lane_bound: Order.Le(1n+lane, 256n)
  {Spec.finish_result(input, state, selected(prefix, head256, rows32, values, lane)) ==
    Spec.finish_result(input, state, Spec.reference(prefix, values, lane)) : Maybe<&2, Attention.Stored>}

# Production-selected output consumes the entire coordinate domain certificate
# as well as the loop refinement. Arbitrary Check includes coverage, both
# coordinate limits, XOR, branch, bounds and involution (hence bijection).
law selected_output_refinement:
  for +prefix: Nat
  for +kind: Spec.Check
  for +stage: Nat
  for +row: Nat
  for +input: Attention.Input
  for +state: Attention.State
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  for +native_count: {prefix == Spec.count(True{}) : Nat}
  for +count_bound: Order.Le(prefix, 8n)
  for stage_bound: Order.Le(1n+stage, 8n)
  for row_bound: Order.Le(1n+row, 32n)
  for +lane_bound: Order.Le(1n+lane, 256n)
  for input_bound: Order.Le(256n, List.length(&2, Attention.Expr, values))
  {Spec.check(kind, stage, lane) == True{} : Bool} &
  {Spec.coordinate_row(Spec.transport(Spec.reshape(stage, row, lane))) == row : Nat} &
  Order.Le(1n+Spec.coordinate_row(Spec.transport(Spec.reshape(stage, row, lane))), 32n) &
  {Spec.finish_result(input, state, selected(prefix, True{}, True{}, values, lane)) ==
    Spec.finish_result(input, state, Spec.reference(prefix, values, lane)) : Maybe<&2, Attention.Stored>} &
  Spec.StoredPresent(Spec.finish_result(input, state, selected(prefix, True{}, True{}, values, lane)))

def selected_outputs(partitions: List<&2, Spec.Partition>, +prefix: Nat, +head256: Bool, +rows32: Bool)
    -> List<&2, Maybe<&2, Attention.Stored>>:
  match partitions:
    case Nil{}:
      Nil{}
    case Spec.Partition{input, state, values, lane} <> rest:
      Spec.finish_result(input, state, selected(prefix, head256, rows32, values, lane)) <>
        selected_outputs(rest, prefix, head256, rows32)

law partition_outputs_refinement:
  for +partitions: List<&2, Spec.Partition>
  for +prefix: Nat
  for +head256: Bool
  for +rows32: Bool
  for +native_count: {prefix == Spec.count(head256) : Nat}
  for +count_bound: Order.Le(prefix, 8n)
  for domain: Spec.Domain(partitions)
  {selected_outputs(partitions, prefix, head256, rows32) ==
    Spec.reference_outputs(partitions, prefix) : List<&2, Maybe<&2, Attention.Stored>>}

law partition_outputs_complete:
  for +partitions: List<&2, Spec.Partition>
  for +prefix: Nat
  for +native_count: {prefix == Spec.count(True{}) : Nat}
  for +count_bound: Order.Le(prefix, 8n)
  for domain: Spec.Domain(partitions)
  Spec.OutputsPresent(selected_outputs(partitions, prefix, True{}, True{}))
