# Production-connected bounded source/model obligations; no native IEEE,
# compiler, physical register/warp, GPU execution or throughput conclusion.
import Base
import ./forward_partner.bend as Impl
import ./forward_partner_spec.bend as Spec
import ./inverse_partner_spec.bend as Transport
import ./attention_schedule_spec.bend as Attention
import ./numerical_spec.bend as Order

law policy_refinement:
  for +head256: Bool
  for +rows32: Bool
  {Impl.forward_partner_stages(head256, rows32) == Spec.forward_partner_stages(head256, rows32) : Nat}

law action_range:
  for head256: Bool
  for rows32: Bool
  Spec.Action(Impl.forward_partner_stages(head256, rows32))

law head_fallback:
  for rows32: Bool
  {Impl.forward_partner_stages(False{}, rows32) == 0n : Nat}

law rows_fallback:
  for head256: Bool
  {Impl.forward_partner_stages(head256, False{}) == 0n : Nat}

law target_progress:
  {Impl.forward_partner_stages(True{}, True{}) == 3n : Nat}

law table_order:
  {Impl.table(2n, False{}, False{}) == [0n, 0n, 0n, 3n] : List<&2, Nat>} &
  {Impl.table(2n, False{}, False{}) ==
    [Spec.row(0n), Spec.row(1n), Spec.row(2n), Spec.row(3n)] : List<&2, Nat>}

law table_lookup:
  for +head256: Bool
  for +rows32: Bool
  {Spec.row(Nat.add(Bool.pick(Nat, head256, 1n, 0n),
    Nat.mul(2n, Bool.pick(Nat, rows32, 1n, 0n)))) == Impl.forward_partner_stages(head256, rows32) : Nat}

law zero_route:
  for +stage: Nat
  {Spec.permute(stage, 0n) == False{} : Bool}

law early_route:
  for +stage: Nat
  for bounded: Order.Le(1n+stage, 3n)
  {Spec.permute(stage, Impl.forward_partner_stages(True{}, True{})) == True{} : Bool}

# Every stage >=3 keeps the original gather, in particular native stages 3..7.
law late_route:
  for +offset: Nat
  {Spec.permute(3n+offset, Impl.forward_partner_stages(True{}, True{})) == False{} : Bool}

law native_stage_count:
  {Spec.native_count(True{}) == 8n : Nat} & {Spec.native_count(False{}) == 7n : Nat}

law native_trace:
  {Spec.trace(Spec.native_count(True{}), Impl.forward_partner_stages(True{}, True{})) ==
    [True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>} &
  {Spec.trace(Spec.native_count(True{}), Impl.forward_partner_stages(True{}, False{})) ==
    [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>} &
  {Spec.trace(Spec.native_count(False{}), Impl.forward_partner_stages(False{}, True{})) ==
    [False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>} &
  {Spec.trace(Spec.native_count(False{}), Impl.forward_partner_stages(False{}, False{})) ==
    [False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>}

law stage_order:
  {Transport.stages(Spec.native_count(True{})) == [0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n] : List<&2, Nat>} &
  {Transport.stages(Spec.native_count(False{})) == [0n, 1n, 2n, 3n, 4n, 5n, 6n] : List<&2, Nat>}

law gather_source:
  for +stage: Nat
  for +lane: Nat
  {Spec.partner(False{}, stage, lane) == Transport.reference_partner(stage, lane) : Nat}

law mixed_partner_exact:
  for +permute: Bool
  for +stage: Nat
  for +lane: Nat
  for stage_bound: Order.Le(1n+stage, 8n)
  for lane_bound: Order.Le(1n+lane, 256n)
  {Spec.partner(permute, stage, lane) == Transport.reference_partner(stage, lane) : Nat}

law mixed_partner_bound:
  for +permute: Bool
  for +stage: Nat
  for +lane: Nat
  for stage_bound: Order.Le(1n+stage, 8n)
  for lane_bound: Order.Le(1n+lane, 256n)
  Order.Le(1n+Spec.partner(permute, stage, lane), 256n)

law mixed_row_preserved:
  for +permute: Bool
  for +stage: Nat
  for +row: Nat
  for +lane: Nat
  {Spec.read_row(permute, stage, row, lane) == row : Nat}

law mixed_involution:
  for +permute: Bool
  for +stage: Nat
  for +lane: Nat
  for +stage_bound: Order.Le(1n+stage, 8n)
  for +lane_bound: Order.Le(1n+lane, 256n)
  {Spec.partner(permute, stage, Spec.partner(permute, stage, lane)) == lane : Nat}

law mixed_surjective:
  for +permute: Bool
  for +stage: Nat
  for +lane: Nat
  for +stage_bound: Order.Le(1n+stage, 8n)
  for +lane_bound: Order.Le(1n+lane, 256n)
  exs source: Nat
  Order.Le(1n+source, 256n) & {Spec.partner(permute, stage, source) == lane : Nat}

law mixed_injective:
  for +permute: Bool
  for +stage: Nat
  for +left: Nat
  for +right: Nat
  for +stage_bound: Order.Le(1n+stage, 8n)
  for left_bound: Order.Le(1n+left, 256n)
  for right_bound: Order.Le(1n+right, 256n)
  for same: {Spec.partner(permute, stage, left) == Spec.partner(permute, stage, right) : Nat}
  {left == right : Nat}

law local_table:
  for +stage: Nat
  for bounded: Order.Le(1n+stage, 3n)
  {Spec.local_checks(256n, 0n, stage) == True{} : Bool}

law selected_register_local:
  for +stage: Nat
  for +lane: Nat
  for +stage_bound: Order.Le(1n+stage, 3n)
  for lane_bound: Order.Le(1n+lane, 256n)
  {Nat.div(Spec.partner(Spec.permute(stage, Impl.forward_partner_stages(True{}, True{})), stage, lane), 8n) ==
    Nat.div(lane, 8n) : Nat}

law selected_coordinate:
  for +head256: Bool
  for +rows32: Bool
  for +stage: Nat
  for +row: Nat
  for +lane: Nat
  for +stage_bound: Order.Le(1n+stage, 8n)
  for row_bound: Order.Le(1n+row, 32n)
  for +lane_bound: Order.Le(1n+lane, 256n)
  {Spec.partner(Spec.permute(stage, Impl.forward_partner_stages(head256, rows32)), stage, lane) ==
    Transport.reference_partner(stage, lane) : Nat} &
  Order.Le(1n+Spec.partner(Spec.permute(stage, Impl.forward_partner_stages(head256, rows32)), stage, lane), 256n) &
  {Spec.read_row(Spec.permute(stage, Impl.forward_partner_stages(head256, rows32)), stage, row, lane) == row : Nat} &
  Order.Le(1n+Spec.read_row(Spec.permute(stage, Impl.forward_partner_stages(head256, rows32)), stage, row, lane), 32n)

law ordered_operands:
  for +low: Bool
  for +current: Attention.Expr
  for +partner: Attention.Expr
  {Transport.butterfly(low, current, partner) ==
    Attention.Where{Bool.pick(Attention.Expr, low, Attention.One{}, Attention.Zero{}),
      Attention.Add{current, partner}, Attention.Sub{partner, current}} : Attention.Expr}

law prior_prefix_reads:
  for +prefix: Nat
  for +stages: Nat
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  {Spec.scheduled(1n+prefix, stages, values, lane) ==
    Transport.lift(Transport.reference_low(prefix, lane), Spec.scheduled(prefix, stages, values, lane),
      Spec.scheduled(prefix, stages, values, Spec.partner(Spec.permute(prefix, stages), prefix, lane)))
    : Maybe<&2, Attention.Expr>}

law zero_recurrence:
  for +count: Nat
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  {Spec.scheduled(count, 0n, values, lane) == Transport.reference(count, values, lane) : Maybe<&2, Attention.Expr>}

law ordered_recurrence:
  for +count: Nat
  for +stages: Nat
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  for +count_bound: Order.Le(count, 8n)
  for +lane_bound: Order.Le(1n+lane, 256n)
  {Spec.scheduled(count, stages, values, lane) == Transport.reference(count, values, lane) : Maybe<&2, Attention.Expr>}

# Production selector is an argument of the evaluated schedule, not an assumed
# private permission. Keep prefix symbolic; exact native equality and count/trace
# laws pin 8/7 without forcing conversion to expand closed expression trees.
def selected(prefix: Nat, head256: Bool, rows32: Bool, values: List<&2, Attention.Expr>, lane: Nat)
    -> Maybe<&2, Attention.Expr>:
  Spec.scheduled(prefix, Impl.forward_partner_stages(head256, rows32), values, lane)

law selected_forward_refinement:
  for +prefix: Nat
  for +head256: Bool
  for +rows32: Bool
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  for native_count: {prefix == Spec.native_count(head256) : Nat}
  for count_bound: Order.Le(prefix, 8n)
  for lane_bound: Order.Le(1n+lane, 256n)
  {selected(prefix, head256, rows32, values, lane) == Transport.reference(prefix, values, lane) : Maybe<&2, Attention.Expr>}

law selected_complete:
  for +prefix: Nat
  for +head256: Bool
  for +rows32: Bool
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  for native_count: {prefix == Spec.native_count(head256) : Nat}
  for +count_bound: Order.Le(prefix, 8n)
  for +lane_bound: Order.Le(1n+lane, 256n)
  for input_bound: Order.Le(256n, List.length(&2, Attention.Expr, values))
  Transport.Present(selected(prefix, head256, rows32, values, lane))

law selected_head_fallback:
  for +prefix: Nat
  for rows32: Bool
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  for native_count: {prefix == Spec.native_count(False{}) : Nat}
  {selected(prefix, False{}, rows32, values, lane) == Transport.reference(prefix, values, lane) : Maybe<&2, Attention.Expr>}

law selected_rows_fallback:
  for +prefix: Nat
  for +head256: Bool
  for +values: List<&2, Attention.Expr>
  for +lane: Nat
  for native_count: {prefix == Spec.native_count(head256) : Nat}
  {selected(prefix, head256, False{}, values, lane) == Transport.reference(prefix, values, lane) : Maybe<&2, Attention.Expr>}

# Retaining the WHOLE context makes sanitization/mask/guard/status identity part
# of equality, including inactive/raw-only/packed-only/mixed observations.
law finish_operands:
  for +context: Spec.Context
  for +original: Attention.Expr
  for +result: Attention.Expr
  {Spec.finish(context, original, result) ==
    Spec.Query{context, Attention.F16{original},
      Attention.F16{Attention.Mul{result, Attention.Ref{Spec.input(context), Attention.Normalize{}}}}} : Spec.Query}

law missing_query:
  for +context: Spec.Context
  for +value: Maybe<&2, Attention.Expr>
  {Spec.finish_result(context, None{}, value) == None{} : Maybe<&2, Spec.Query>} &
  {Spec.finish_result(context, value, None{}) == None{} : Maybe<&2, Spec.Query>}

def selected_query(prefix: Nat, head256: Bool, rows32: Bool, +context: Spec.Context, +lane: Nat)
    -> Maybe<&2, Spec.Query>:
  Spec.finish_result(context, Transport.lookup(Spec.entering(context), lane),
    selected(prefix, head256, rows32, Spec.entering(context), lane))

law selected_query_refinement:
  for +prefix: Nat
  for +head256: Bool
  for +rows32: Bool
  for +context: Spec.Context
  for +lane: Nat
  for native_count: {prefix == Spec.native_count(head256) : Nat}
  for count_bound: Order.Le(prefix, 8n)
  for lane_bound: Order.Le(1n+lane, 256n)
  {selected_query(prefix, head256, rows32, context, lane) == Spec.reference_query(prefix, context, lane) : Maybe<&2, Spec.Query>}

law selected_query_complete:
  for +prefix: Nat
  for +head256: Bool
  for +rows32: Bool
  for +context: Spec.Context
  for +lane: Nat
  for native_count: {prefix == Spec.native_count(head256) : Nat}
  for +count_bound: Order.Le(prefix, 8n)
  for +lane_bound: Order.Le(1n+lane, 256n)
  for +input_bound: Order.Le(256n, List.length(&2, Attention.Expr, Spec.entering(context)))
  Spec.QueryPresent(selected_query(prefix, head256, rows32, context, lane))
