# Reuse the checked 8x256 inverse coordinate certificates and ordered-expression
# helpers. The new finite certificate is ONLY the first-three group-of-eight
# property; mixed recurrence is structural induction on a symbolic prefix.
import Base
import ./forward_partner.bend as Impl
import ./forward_partner_spec.bend as Spec
import ./forward_partner_laws.bend as Laws
import ./inverse_partner_spec.bend as Transport
import ./inverse_partner_laws.bend as TransportLaws
import ./inverse_partner_proof.bend as TransportProof
import ./attention_schedule_spec.bend as Attention
import ./numerical_spec.bend as Order
import ./numerical_proof.bend as NumericalProof
import ./marlin_pipeline_proof.bend as MarlinProof

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
  match head256 rows32:
    case False{} False{}:
      Unit{}
    case False{} True{}:
      Unit{}
    case True{} False{}:
      Unit{}
    case True{} True{}:
      Unit{}

def Laws.head_fallback(rows32):
  {==}

def Laws.rows_fallback(head256):
  match head256:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.target_progress():
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

def Laws.zero_route(stage):
  match stage:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Laws.early_route(stage, bounded):
  match stage:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+r:
              Empty.absurd({Spec.permute(3n+r, Impl.forward_partner_stages(True{}, True{})) == True{} : Bool}, bounded)

def Laws.late_route(offset):
  match offset:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Laws.native_stage_count():
  ({==}, {==})

def Laws.native_trace():
  ({==}, ({==}, ({==}, {==})))

def Laws.stage_order():
  TransportLaws.exact_stage_order()

def Laws.gather_source(stage, lane):
  {==}

def Laws.mixed_partner_exact(permute, stage, lane, stage_bound, lane_bound):
  match permute:
    case False{}:
      {==}
    case True{}:
      TransportLaws.partner_exact(stage, lane, stage_bound, lane_bound)

def selected_to_mixed(permute: Bool, +stage: Nat, +lane: Nat,
    stage_bound: Order.Le(1n+stage, 8n), lane_bound: Order.Le(1n+lane, 256n))
    -> {Transport.selected_partner(stage, lane) == Spec.partner(permute, stage, lane) : Nat}:
  match permute:
    case False{}:
      TransportLaws.partner_exact(stage, lane, stage_bound, lane_bound)
    case True{}:
      {==}

def Laws.mixed_partner_bound(permute, stage, lane, stage_bound, lane_bound):
  match permute:
    case False{}:
      TransportProof.reference_partner_bound(stage, lane, stage_bound, lane_bound)
    case True{}:
      TransportLaws.partner_bound(stage, lane, stage_bound, lane_bound)

def Laws.mixed_row_preserved(permute, stage, row, lane):
  match permute:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.mixed_involution(permute, stage, lane, stage_bound, lane_bound):
  Equal.trans(Nat, Spec.partner(permute, stage, Spec.partner(permute, stage, lane)),
    Transport.selected_partner(stage, Spec.partner(permute, stage, lane)), lane,
    Equal.sym(Nat, Transport.selected_partner(stage, Spec.partner(permute, stage, lane)),
      Spec.partner(permute, stage, Spec.partner(permute, stage, lane)),
      selected_to_mixed(permute, stage, Spec.partner(permute, stage, lane), stage_bound,
        Laws.mixed_partner_bound(permute, stage, lane, stage_bound, lane_bound))),
    Equal.trans(Nat, Transport.selected_partner(stage, Spec.partner(permute, stage, lane)),
      Transport.selected_partner(stage, Transport.selected_partner(stage, lane)), lane,
      Equal.cong(Nat, Nat, partner => Transport.selected_partner(stage, partner),
        Spec.partner(permute, stage, lane), Transport.selected_partner(stage, lane),
        Equal.sym(Nat, Transport.selected_partner(stage, lane), Spec.partner(permute, stage, lane),
          selected_to_mixed(permute, stage, lane, stage_bound, lane_bound))),
      TransportLaws.partner_involution(stage, lane, stage_bound, lane_bound)))

def Laws.mixed_surjective(permute, stage, lane, stage_bound, lane_bound):
  (Spec.partner(permute, stage, lane),
    (Laws.mixed_partner_bound(permute, stage, lane, stage_bound, lane_bound),
      Laws.mixed_involution(permute, stage, lane, stage_bound, lane_bound)))

def Laws.mixed_injective(permute, stage, left, right, stage_bound, left_bound, right_bound, same):
  Equal.trans(Nat, left, Spec.partner(permute, stage, Spec.partner(permute, stage, left)), right,
    Equal.sym(Nat, Spec.partner(permute, stage, Spec.partner(permute, stage, left)), left,
      Laws.mixed_involution(permute, stage, left, stage_bound, left_bound)),
    Equal.trans(Nat, Spec.partner(permute, stage, Spec.partner(permute, stage, left)),
      Spec.partner(permute, stage, Spec.partner(permute, stage, right)), right,
      Equal.cong(Nat, Nat, lane => Spec.partner(permute, stage, lane),
        Spec.partner(permute, stage, left), Spec.partner(permute, stage, right), same),
      Laws.mixed_involution(permute, stage, right, stage_bound, right_bound)))

# Exhaustive 3x256 NEW local-group property; no duplicate 8x256 transport proof.
def Laws.local_table(stage, bounded):
  match stage:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+r:
              Empty.absurd({Spec.local_checks(256n, 0n, 3n+r) == True{} : Bool}, bounded)

def local_at(+count: Nat, +index: Nat, +start: Nat, +stage: Nat,
    bounded: Order.Le(1n+index, count),
    accepted: {Spec.local_checks(count, start, stage) == True{} : Bool})
    -> {Spec.local_check(stage, Nat.add(start, index)) == True{} : Bool}:
  match count index:
    case 0n _:
      Empty.absurd({Spec.local_check(stage, Nat.add(start, index)) == True{} : Bool}, bounded)
    case 1n+p 0n:
      Equal.trans(Bool, Spec.local_check(stage, Nat.add(start, 0n)), Spec.local_check(stage, start), True{},
        Equal.cong(Nat, Bool, lane => Spec.local_check(stage, lane),
          Nat.add(start, 0n), start, MarlinProof.add_zero(start)),
        TransportProof.true_left(Spec.local_check(stage, start), Spec.local_checks(p, 1n+start, stage), accepted))
    case 1n+p 1n+q:
      Equal.trans(Bool, Spec.local_check(stage, Nat.add(start, 1n+q)),
        Spec.local_check(stage, 1n+Nat.add(start, q)), True{},
        Equal.cong(Nat, Bool, lane => Spec.local_check(stage, lane),
          Nat.add(start, 1n+q), 1n+Nat.add(start, q), NumericalProof.add_succ(start, q)),
        local_at(p, q, 1n+start, stage, bounded,
          TransportProof.true_right(Spec.local_check(stage, start), Spec.local_checks(p, 1n+start, stage), accepted)))

def Laws.selected_register_local(stage, lane, stage_bound, lane_bound):
  %Equal.sym(Bool, Spec.permute(stage, Impl.forward_partner_stages(True{}, True{})), True{},
    Laws.early_route(stage, stage_bound)) :
    {Nat.div(Spec.partner(_, stage, lane), 8n) == Nat.div(lane, 8n) : Nat}
  NumericalProof.nat_eq_sound(Nat.div(Transport.selected_partner(stage, lane), 8n), Nat.div(lane, 8n),
    local_at(256n, lane, 0n, stage, lane_bound, Laws.local_table(stage, stage_bound)))

def mixed_row_bound(+permute: Bool, +stage: Nat, +row: Nat, +lane: Nat,
    bounded: Order.Le(1n+row, 32n)) -> Order.Le(1n+Spec.read_row(permute, stage, row, lane), 32n):
  %Equal.sym(Nat, Spec.read_row(permute, stage, row, lane), row,
    Laws.mixed_row_preserved(permute, stage, row, lane)) : Order.Le(1n+_, 32n)
  bounded

def Laws.selected_coordinate(head256, rows32, stage, row, lane, stage_bound, row_bound, lane_bound):
  (Laws.mixed_partner_exact(Spec.permute(stage, Impl.forward_partner_stages(head256, rows32)), stage, lane, stage_bound, lane_bound),
    (Laws.mixed_partner_bound(Spec.permute(stage, Impl.forward_partner_stages(head256, rows32)), stage, lane, stage_bound, lane_bound),
      (Laws.mixed_row_preserved(Spec.permute(stage, Impl.forward_partner_stages(head256, rows32)), stage, row, lane),
        mixed_row_bound(Spec.permute(stage, Impl.forward_partner_stages(head256, rows32)), stage, row, lane, row_bound))))

def Laws.ordered_operands(low, current, partner):
  TransportLaws.butterfly_operands(low, current, partner)

def Laws.prior_prefix_reads(prefix, stages, values, lane):
  {==}

def zero_partner(+stage: Nat, +lane: Nat)
    -> {Spec.partner(Spec.permute(stage, 0n), stage, lane) == Transport.reference_partner(stage, lane) : Nat}:
  Equal.cong(Bool, Nat, permute => Spec.partner(permute, stage, lane),
    Spec.permute(stage, 0n), False{}, Laws.zero_route(stage))

def Laws.zero_recurrence(count, values, lane):
  match count:
    case 0n:
      {==}
    case 1n+p:
      TransportProof.lift_equal(Transport.reference_low(p, lane), Transport.reference_low(p, lane),
        Spec.scheduled(p, 0n, values, lane), Transport.reference(p, values, lane),
        Spec.scheduled(p, 0n, values, Spec.partner(Spec.permute(p, 0n), p, lane)),
        Transport.reference(p, values, Transport.reference_partner(p, lane)), {==},
        Laws.zero_recurrence(p, values, lane),
        Equal.trans(Maybe<&2, Attention.Expr>,
          Spec.scheduled(p, 0n, values, Spec.partner(Spec.permute(p, 0n), p, lane)),
          Spec.scheduled(p, 0n, values, Transport.reference_partner(p, lane)),
          Transport.reference(p, values, Transport.reference_partner(p, lane)),
          Equal.cong(Nat, Maybe<&2, Attention.Expr>, partner => Spec.scheduled(p, 0n, values, partner),
            Spec.partner(Spec.permute(p, 0n), p, lane), Transport.reference_partner(p, lane), zero_partner(p, lane)),
          Laws.zero_recurrence(p, values, Transport.reference_partner(p, lane))))

def Laws.ordered_recurrence(count, stages, values, lane, count_bound, lane_bound):
  match count:
    case 0n:
      {==}
    case 1n+p:
      TransportProof.lift_equal(Transport.reference_low(p, lane), Transport.reference_low(p, lane),
        Spec.scheduled(p, stages, values, lane), Transport.reference(p, values, lane),
        Spec.scheduled(p, stages, values, Spec.partner(Spec.permute(p, stages), p, lane)),
        Transport.reference(p, values, Transport.reference_partner(p, lane)), {==},
        Laws.ordered_recurrence(p, stages, values, lane, NumericalProof.le_drop(p, 8n, count_bound), lane_bound),
        Equal.trans(Maybe<&2, Attention.Expr>,
          Spec.scheduled(p, stages, values, Spec.partner(Spec.permute(p, stages), p, lane)),
          Transport.reference(p, values, Spec.partner(Spec.permute(p, stages), p, lane)),
          Transport.reference(p, values, Transport.reference_partner(p, lane)),
          Laws.ordered_recurrence(p, stages, values, Spec.partner(Spec.permute(p, stages), p, lane),
            NumericalProof.le_drop(p, 8n, count_bound),
            Laws.mixed_partner_bound(Spec.permute(p, stages), p, lane, count_bound, lane_bound)),
          Equal.cong(Nat, Maybe<&2, Attention.Expr>, partner => Transport.reference(p, values, partner),
            Spec.partner(Spec.permute(p, stages), p, lane), Transport.reference_partner(p, lane),
            Laws.mixed_partner_exact(Spec.permute(p, stages), p, lane, count_bound, lane_bound))))

def Laws.selected_forward_refinement(prefix, head256, rows32, values, lane, native_count, count_bound, lane_bound):
  Laws.ordered_recurrence(prefix, Impl.forward_partner_stages(head256, rows32), values, lane, count_bound, lane_bound)

def Laws.selected_complete(prefix, head256, rows32, values, lane, native_count, count_bound, lane_bound, input_bound):
  %Equal.sym(Maybe<&2, Attention.Expr>, Laws.selected(prefix, head256, rows32, values, lane),
    Transport.reference(prefix, values, lane),
    Laws.selected_forward_refinement(prefix, head256, rows32, values, lane, native_count, count_bound, lane_bound)) :
      Transport.Present(_)
  TransportLaws.reference_complete(prefix, values, lane, count_bound, lane_bound, input_bound)

def Laws.selected_head_fallback(prefix, rows32, values, lane, native_count):
  Laws.zero_recurrence(prefix, values, lane)

def Laws.selected_rows_fallback(prefix, head256, values, lane, native_count):
  %Equal.sym(Nat, Impl.forward_partner_stages(head256, False{}), 0n, Laws.rows_fallback(head256)) :
    {Spec.scheduled(prefix, _, values, lane) == Transport.reference(prefix, values, lane) : Maybe<&2, Attention.Expr>}
  Laws.zero_recurrence(prefix, values, lane)

def Laws.finish_operands(context, original, result):
  {==}

def Laws.missing_query(context, value):
  match value:
    case None{}:
      ({==}, {==})
    case Some{expression}:
      ({==}, {==})

def Laws.selected_query_refinement(prefix, head256, rows32, context, lane, native_count, count_bound, lane_bound):
  Equal.cong(Maybe<&2, Attention.Expr>, Maybe<&2, Spec.Query>,
    result => Spec.finish_result(context, Transport.lookup(Spec.entering(context), lane), result),
    Laws.selected(prefix, head256, rows32, Spec.entering(context), lane),
    Transport.reference(prefix, Spec.entering(context), lane),
    Laws.selected_forward_refinement(prefix, head256, rows32, Spec.entering(context), lane, native_count, count_bound, lane_bound))

def finish_present(+context: Spec.Context, +original: Maybe<&2, Attention.Expr>, +result: Maybe<&2, Attention.Expr>,
    original_present: Transport.Present(original), result_present: Transport.Present(result))
    -> Spec.QueryPresent(Spec.finish_result(context, original, result)):
  match original result:
    case None{} None{}:
      Empty.absurd(Spec.QueryPresent(Spec.finish_result(context, None{}, None{})), original_present)
    case None{} Some{value}:
      Empty.absurd(Spec.QueryPresent(Spec.finish_result(context, None{}, Some{value})), original_present)
    case Some{value} None{}:
      Empty.absurd(Spec.QueryPresent(Spec.finish_result(context, Some{value}, None{})), result_present)
    case Some{original} Some{result}:
      Unit{}

def Laws.selected_query_complete(prefix, head256, rows32, context, lane, native_count, count_bound, lane_bound, input_bound):
  finish_present(context, Transport.lookup(Spec.entering(context), lane),
    Laws.selected(prefix, head256, rows32, Spec.entering(context), lane),
    TransportProof.lookup_complete(Spec.entering(context), lane,
      NumericalProof.le_trans(1n+lane, 256n, List.length(&2, Attention.Expr, Spec.entering(context)), lane_bound, input_bound)),
    Laws.selected_complete(prefix, head256, rows32, Spec.entering(context), lane, native_count, count_bound, lane_bound, input_bound))
