# Closed finite certificates plus structural elimination and prefix induction.
# No unsafe declarations, native axioms, expression-tree expansion or checks.
import Base
import ./inverse_partner.bend as Impl
import ./inverse_partner_spec.bend as Spec
import ./inverse_partner_laws.bend as Laws
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

def Laws.transport_chain(row, group, high, offset):
  {==}

def Laws.split_join_planes(row, group, offset):
  ({==}, {==})

def Laws.reference_bit_chain(stage, lane):
  ({==}, {==})

def Laws.one_hot_mask(stage, bounded):
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
              match r:
                case 0n:
                  {==}
                case 1n+s:
                  match s:
                    case 0n:
                      {==}
                    case 1n+t:
                      match t:
                        case 0n:
                          {==}
                        case 1n+u:
                          match u:
                            case 0n:
                              {==}
                            case 1n+v:
                              match v:
                                case 0n:
                                  {==}
                                case 1n+rest:
                                  Empty.absurd({Order.value(Spec.one_hot(8n, 8n+rest, 0n)) ==
                                    Order.power2(8n+rest) : Nat}, bounded)

# Exhaustive constructor cases: every declared property checks all 2048
# (stage,lane) coordinates. Arbitrary-index elimination below consumes these.
def Laws.coordinate_table(kind):
  match kind:
    case Spec.Recompose{}:
      {==}
    case Spec.BitCoverage{}:
      {==}
    case Spec.GroupBound{}:
      {==}
    case Spec.OffsetBound{}:
      {==}
    case Spec.Partner{}:
      {==}
    case Spec.Branch{}:
      {==}
    case Spec.PartnerBound{}:
      {==}
    case Spec.Involution{}:
      {==}

def true_left(+a: Bool, +b: Bool, accepted: {Bool.and(a, b) == True{} : Bool})
    -> {a == True{} : Bool}:
  Pair.fst({a == True{} : Bool}, {b == True{} : Bool}, NumericalProof.and_true(a, b, accepted))

def true_right(+a: Bool, +b: Bool, accepted: {Bool.and(a, b) == True{} : Bool})
    -> {b == True{} : Bool}:
  Pair.snd({a == True{} : Bool}, {b == True{} : Bool}, NumericalProof.and_true(a, b, accepted))

def lane_at(+count: Nat, +index: Nat, +start: Nat, +kind: Spec.Check, +stage: Nat,
    bounded: Order.Le(1n+index, count),
    accepted: {Spec.lane_checks(count, start, kind, stage) == True{} : Bool})
    -> {Spec.check(kind, stage, Nat.add(start, index)) == True{} : Bool}:
  match count index:
    case 0n _:
      Empty.absurd({Spec.check(kind, stage, Nat.add(start, index)) == True{} : Bool}, bounded)
    case 1n+p 0n:
      Equal.trans(Bool, Spec.check(kind, stage, Nat.add(start, 0n)),
        Spec.check(kind, stage, start), True{},
        Equal.cong(Nat, Bool, lane => Spec.check(kind, stage, lane),
          Nat.add(start, 0n), start, MarlinProof.add_zero(start)),
        true_left(Spec.check(kind, stage, start), Spec.lane_checks(p, 1n+start, kind, stage), accepted))
    case 1n+p 1n+q:
      Equal.trans(Bool, Spec.check(kind, stage, Nat.add(start, 1n+q)),
        Spec.check(kind, stage, 1n+Nat.add(start, q)), True{},
        Equal.cong(Nat, Bool, lane => Spec.check(kind, stage, lane),
          Nat.add(start, 1n+q), 1n+Nat.add(start, q), NumericalProof.add_succ(start, q)),
        lane_at(p, q, 1n+start, kind, stage, bounded,
          true_right(Spec.check(kind, stage, start), Spec.lane_checks(p, 1n+start, kind, stage), accepted)))

def stage_at(+count: Nat, +index: Nat, +start: Nat, +kind: Spec.Check,
    bounded: Order.Le(1n+index, count),
    accepted: {Spec.stage_checks(count, start, kind) == True{} : Bool})
    -> {Spec.lane_checks(256n, 0n, kind, Nat.add(start, index)) == True{} : Bool}:
  match count index:
    case 0n _:
      Empty.absurd({Spec.lane_checks(256n, 0n, kind, Nat.add(start, index)) == True{} : Bool}, bounded)
    case 1n+p 0n:
      Equal.trans(Bool, Spec.lane_checks(256n, 0n, kind, Nat.add(start, 0n)),
        Spec.lane_checks(256n, 0n, kind, start), True{},
        Equal.cong(Nat, Bool, stage => Spec.lane_checks(256n, 0n, kind, stage),
          Nat.add(start, 0n), start, MarlinProof.add_zero(start)),
        true_left(Spec.lane_checks(256n, 0n, kind, start), Spec.stage_checks(p, 1n+start, kind), accepted))
    case 1n+p 1n+q:
      Equal.trans(Bool, Spec.lane_checks(256n, 0n, kind, Nat.add(start, 1n+q)),
        Spec.lane_checks(256n, 0n, kind, 1n+Nat.add(start, q)), True{},
        Equal.cong(Nat, Bool, stage => Spec.lane_checks(256n, 0n, kind, stage),
          Nat.add(start, 1n+q), 1n+Nat.add(start, q), NumericalProof.add_succ(start, q)),
        stage_at(p, q, 1n+start, kind, bounded,
          true_right(Spec.lane_checks(256n, 0n, kind, start), Spec.stage_checks(p, 1n+start, kind), accepted)))

def Laws.bounded_coordinate(kind, stage, lane, stage_bound, lane_bound):
  lane_at(256n, lane, 0n, kind, stage, lane_bound,
    stage_at(8n, stage, 0n, kind, stage_bound, Laws.coordinate_table(kind)))

def Laws.coordinate_coverage(stage, row, lane, stage_bound, lane_bound):
  (NumericalProof.nat_eq_sound(Spec.flatten(stage, Spec.reshape(stage, row, lane)), lane,
    Laws.bounded_coordinate(Spec.Recompose{}, stage, lane, stage_bound, lane_bound)),
   (NumericalProof.nat_eq_sound(Order.value(Spec.bits(8n, lane)), lane,
      Laws.bounded_coordinate(Spec.BitCoverage{}, stage, lane, stage_bound, lane_bound)),
    (NumericalProof.lt_sound(Spec.coordinate_group(Spec.reshape(stage, row, lane)),
      Nat.div(256n, Nat.double(Order.power2(stage))),
      Laws.bounded_coordinate(Spec.GroupBound{}, stage, lane, stage_bound, lane_bound)),
     NumericalProof.lt_sound(Spec.coordinate_offset(Spec.reshape(stage, row, lane)), Order.power2(stage),
      Laws.bounded_coordinate(Spec.OffsetBound{}, stage, lane, stage_bound, lane_bound)))))

def Laws.row_and_axes_preserved(stage, row, lane):
  ({==}, ({==}, ({==}, {==})))

def Laws.partner_exact(stage, lane, stage_bound, lane_bound):
  NumericalProof.nat_eq_sound(Spec.selected_partner(stage, lane), Spec.reference_partner(stage, lane),
    Laws.bounded_coordinate(Spec.Partner{}, stage, lane, stage_bound, lane_bound))

def bool_code_sound(+left: Bool, +right: Bool,
    accepted: {Nat.is_eq(Bool.pick(Nat, left, 1n, 0n), Bool.pick(Nat, right, 1n, 0n)) == True{} : Bool})
    -> {left == right : Bool}:
  match left right:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, NumericalProof.false_true(accepted))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, NumericalProof.false_true(accepted))
    case True{} True{}:
      {==}

def Laws.branch_bit(stage, lane, stage_bound, lane_bound):
  bool_code_sound(Spec.selected_low(stage, lane), Spec.reference_low(stage, lane),
    Laws.bounded_coordinate(Spec.Branch{}, stage, lane, stage_bound, lane_bound))

def Laws.partner_bound(stage, lane, stage_bound, lane_bound):
  NumericalProof.lt_sound(Spec.selected_partner(stage, lane), 256n,
    Laws.bounded_coordinate(Spec.PartnerBound{}, stage, lane, stage_bound, lane_bound))

def Laws.partner_involution(stage, lane, stage_bound, lane_bound):
  NumericalProof.nat_eq_sound(Spec.selected_partner(stage, Spec.selected_partner(stage, lane)), lane,
    Laws.bounded_coordinate(Spec.Involution{}, stage, lane, stage_bound, lane_bound))

def Laws.partner_surjective(stage, lane, stage_bound, lane_bound):
  (Spec.selected_partner(stage, lane),
    (Laws.partner_bound(stage, lane, stage_bound, lane_bound),
      Laws.partner_involution(stage, lane, stage_bound, lane_bound)))

def Laws.partner_injective(stage, left, right, stage_bound, left_bound, right_bound, same):
  Equal.trans(Nat, left, Spec.selected_partner(stage, Spec.selected_partner(stage, left)), right,
    Equal.sym(Nat, Spec.selected_partner(stage, Spec.selected_partner(stage, left)), left,
      Laws.partner_involution(stage, left, stage_bound, left_bound)),
    Equal.trans(Nat, Spec.selected_partner(stage, Spec.selected_partner(stage, left)),
      Spec.selected_partner(stage, Spec.selected_partner(stage, right)), right,
      Equal.cong(Nat, Nat, lane => Spec.selected_partner(stage, lane),
        Spec.selected_partner(stage, left), Spec.selected_partner(stage, right), same),
      Laws.partner_involution(stage, right, stage_bound, right_bound)))

def Laws.butterfly_operands(low, current, partner):
  {==}

def Laws.selected_stage_source(stage, lane, values, stage_bound, lane_bound):
  Equal.cong(Bool, Maybe<&2, Attention.Expr>,
    low => Spec.lift(low, Spec.lookup(values, lane), Spec.lookup(values, Spec.selected_partner(stage, lane))),
    Spec.selected_low(stage, lane), Spec.reference_low(stage, lane),
    Laws.branch_bit(stage, lane, stage_bound, lane_bound))

def Laws.stage_refinement(stage, lane, values, stage_bound, lane_bound):
  Equal.trans(Maybe<&2, Attention.Expr>,
    Spec.lift(Spec.selected_low(stage, lane), Spec.lookup(values, lane),
      Spec.lookup(values, Spec.selected_partner(stage, lane))),
    Spec.lift(Spec.reference_low(stage, lane), Spec.lookup(values, lane),
      Spec.lookup(values, Spec.selected_partner(stage, lane))),
    Spec.lift(Spec.reference_low(stage, lane), Spec.lookup(values, lane),
      Spec.lookup(values, Spec.reference_partner(stage, lane))),
    Laws.selected_stage_source(stage, lane, values, stage_bound, lane_bound),
    Equal.cong(Nat, Maybe<&2, Attention.Expr>,
      partner => Spec.lift(Spec.reference_low(stage, lane), Spec.lookup(values, lane), Spec.lookup(values, partner)),
      Spec.selected_partner(stage, lane), Spec.reference_partner(stage, lane),
      Laws.partner_exact(stage, lane, stage_bound, lane_bound)))

def Laws.exact_stage_order():
  ({==}, {==})

def Laws.native_stage_count():
  ({==}, {==})

# Congruence retains the whole ordered Where term, including both branches.
def lift_equal(+left_low: Bool, +right_low: Bool,
    +left_current: Maybe<&2, Attention.Expr>, +right_current: Maybe<&2, Attention.Expr>,
    +left_partner: Maybe<&2, Attention.Expr>, +right_partner: Maybe<&2, Attention.Expr>,
    low: {left_low == right_low : Bool},
    current: {left_current == right_current : Maybe<&2, Attention.Expr>},
    partner: {left_partner == right_partner : Maybe<&2, Attention.Expr>})
    -> {Spec.lift(left_low, left_current, left_partner) ==
      Spec.lift(right_low, right_current, right_partner) : Maybe<&2, Attention.Expr>}:
  %low : {Spec.lift(left_low, left_current, left_partner) ==
    Spec.lift(_, right_current, right_partner) : Maybe<&2, Attention.Expr>}
  %current : {Spec.lift(left_low, left_current, left_partner) ==
    Spec.lift(left_low, _, right_partner) : Maybe<&2, Attention.Expr>}
  %partner : {Spec.lift(left_low, left_current, left_partner) ==
    Spec.lift(left_low, left_current, _) : Maybe<&2, Attention.Expr>}
  {==}

def Laws.action0_recurrence(count, values, lane):
  match count:
    case 0n:
      {==}
    case 1n+p:
      lift_equal(Spec.reference_low(p, lane), Spec.reference_low(p, lane),
        Spec.scheduled(p, 0n, values, lane), Spec.reference(p, values, lane),
        Spec.scheduled(p, 0n, values, Spec.reference_partner(p, lane)),
        Spec.reference(p, values, Spec.reference_partner(p, lane)), {==},
        Laws.action0_recurrence(p, values, lane),
        Laws.action0_recurrence(p, values, Spec.reference_partner(p, lane)))

def Laws.ordered_recurrence(count, values, lane, count_bound, lane_bound):
  match count:
    case 0n:
      {==}
    case 1n+p:
      lift_equal(Spec.selected_low(p, lane), Spec.reference_low(p, lane),
        Spec.scheduled(p, 1n, values, lane), Spec.reference(p, values, lane),
        Spec.scheduled(p, 1n, values, Spec.selected_partner(p, lane)),
        Spec.reference(p, values, Spec.reference_partner(p, lane)),
        Laws.branch_bit(p, lane, count_bound, lane_bound),
        Laws.ordered_recurrence(p, values, lane, NumericalProof.le_drop(p, 8n, count_bound), lane_bound),
        Equal.trans(Maybe<&2, Attention.Expr>,
          Spec.scheduled(p, 1n, values, Spec.selected_partner(p, lane)),
          Spec.reference(p, values, Spec.selected_partner(p, lane)),
          Spec.reference(p, values, Spec.reference_partner(p, lane)),
          Laws.ordered_recurrence(p, values, Spec.selected_partner(p, lane),
            NumericalProof.le_drop(p, 8n, count_bound), Laws.partner_bound(p, lane, count_bound, lane_bound)),
          Equal.cong(Nat, Maybe<&2, Attention.Expr>, partner => Spec.reference(p, values, partner),
            Spec.selected_partner(p, lane), Spec.reference_partner(p, lane),
            Laws.partner_exact(p, lane, count_bound, lane_bound))))

def lookup_complete(+values: List<&2, Attention.Expr>, +lane: Nat,
    bounded: Order.Le(1n+lane, List.length(&2, Attention.Expr, values)))
    -> Spec.Present(Spec.lookup(values, lane)):
  match values lane:
    case Nil{} _:
      Empty.absurd(Spec.Present(Spec.lookup(Nil{}, lane)), bounded)
    case value <> rest 0n:
      Unit{}
    case value <> rest 1n+p:
      lookup_complete(rest, p, bounded)

def lift_present(low: Bool, +current: Maybe<&2, Attention.Expr>, +partner: Maybe<&2, Attention.Expr>,
    current_present: Spec.Present(current), partner_present: Spec.Present(partner))
    -> Spec.Present(Spec.lift(low, current, partner)):
  match current partner:
    case None{} None{}:
      Empty.absurd(Spec.Present(Spec.lift(low, None{}, None{})), current_present)
    case None{} Some{value}:
      Empty.absurd(Spec.Present(Spec.lift(low, None{}, Some{value})), current_present)
    case Some{value} None{}:
      Empty.absurd(Spec.Present(Spec.lift(low, Some{value}, None{})), partner_present)
    case Some{current} Some{partner}:
      Unit{}

def reference_partner_bound(+stage: Nat, +lane: Nat,
    +stage_bound: Order.Le(1n+stage, 8n), +lane_bound: Order.Le(1n+lane, 256n))
    -> Order.Le(1n+Spec.reference_partner(stage, lane), 256n):
  %Laws.partner_exact(stage, lane, stage_bound, lane_bound) : Order.Le(1n+_, 256n)
  Laws.partner_bound(stage, lane, stage_bound, lane_bound)

def Laws.reference_complete(count, values, lane, count_bound, lane_bound, input_bound):
  match count:
    case 0n:
      lookup_complete(values, lane,
        NumericalProof.le_trans(1n+lane, 256n, List.length(&2, Attention.Expr, values), lane_bound, input_bound))
    case 1n+p:
      lift_present(Spec.reference_low(p, lane), Spec.reference(p, values, lane),
        Spec.reference(p, values, Spec.reference_partner(p, lane)),
        Laws.reference_complete(p, values, lane, NumericalProof.le_drop(p, 8n, count_bound), lane_bound, input_bound),
        Laws.reference_complete(p, values, Spec.reference_partner(p, lane),
          NumericalProof.le_drop(p, 8n, count_bound), reference_partner_bound(p, lane, count_bound, lane_bound), input_bound))

# Keep the prefix symbolic while eliminating the finite action. Matching the
# shape here would specialize the evaluator to seven/eight stages inside the
# checker and expand its nested lane expressions before congruence can apply.
def action_refinement(action: Nat, +count: Nat, +values: List<&2, Attention.Expr>, +lane: Nat,
    valid: Spec.Action(action), count_bound: Order.Le(count, 8n), lane_bound: Order.Le(1n+lane, 256n))
    -> {Spec.scheduled(count, action, values, lane) ==
      Spec.reference(count, values, lane) : Maybe<&2, Attention.Expr>}:
  match action:
    case 0n:
      Laws.action0_recurrence(count, values, lane)
    case 1n+p:
      match p:
        case 0n:
          Laws.ordered_recurrence(count, values, lane, count_bound, lane_bound)
        case 1n+q:
          Empty.absurd({Spec.scheduled(count, 2n+q, values, lane) ==
            Spec.reference(count, values, lane) : Maybe<&2, Attention.Expr>}, valid)


def Laws.selected_inverse_refinement(prefix, head256, rows32, values, lane, native_count, count_bound, lane_bound):
  action_refinement(Impl.inverse_partner(head256, rows32), prefix, values, lane,
    Laws.action_range(head256, rows32), count_bound, lane_bound)

def Laws.selected_complete(prefix, values, lane, native_count, count_bound, lane_bound, input_bound):
  %Equal.sym(Maybe<&2, Attention.Expr>, Laws.selected(prefix, True{}, True{}, values, lane),
    Spec.reference(prefix, values, lane),
    Laws.selected_inverse_refinement(prefix, True{}, True{}, values, lane, native_count, count_bound, lane_bound)) :
      Spec.Present(_)
  Laws.reference_complete(prefix, values, lane, count_bound, lane_bound, input_bound)

def Laws.selected_head_fallback(prefix, rows32, values, lane, native_count, count_bound):
  Laws.action0_recurrence(prefix, values, lane)

def Laws.selected_rows_fallback(prefix, head256, values, lane, native_count, count_bound):
  match head256:
    case False{}:
      Laws.action0_recurrence(prefix, values, lane)
    case True{}:
      Laws.action0_recurrence(prefix, values, lane)

def Laws.finish_operands(input, keys, values, softmax, maximum, denominator, raw, rotated, status, inverse):
  {==}

def Laws.finish_refinement(prefix, head256, rows32, input, state, values, lane, native_count, count_bound, lane_bound):
  Equal.cong(Maybe<&2, Attention.Expr>, Maybe<&2, Attention.Stored>,
    inverse => Spec.finish_result(input, state, inverse),
    Laws.selected(prefix, head256, rows32, values, lane), Spec.reference(prefix, values, lane),
    Laws.selected_inverse_refinement(prefix, head256, rows32, values, lane, native_count, count_bound, lane_bound))

def finish_present(+input: Attention.Input, +state: Attention.State,
    +inverse: Maybe<&2, Attention.Expr>, present: Spec.Present(inverse))
    -> Spec.StoredPresent(Spec.finish_result(input, state, inverse)):
  match inverse:
    case None{}:
      Empty.absurd(Spec.StoredPresent(Spec.finish_result(input, state, None{})), present)
    case Some{value}:
      Unit{}

def Laws.selected_output_refinement(prefix, kind, stage, row, input, state, values, lane,
    native_count, count_bound, stage_bound, row_bound, lane_bound, input_bound):
  (Laws.bounded_coordinate(kind, stage, lane, stage_bound, lane_bound),
    ({==}, (row_bound,
      (Laws.finish_refinement(prefix, True{}, True{}, input, state, values, lane, native_count, count_bound, lane_bound),
        finish_present(input, state, Laws.selected(prefix, True{}, True{}, values, lane),
          Laws.selected_complete(prefix, values, lane, native_count, count_bound, lane_bound, input_bound))))))

def Laws.partition_outputs_refinement(partitions, prefix, head256, rows32, native_count, count_bound, domain):
  match partitions:
    case Nil{}:
      {==}
    case Spec.Partition{input, state, values, lane} <> rest:
      (bounds, rest_domain) = domain
      (input_bound, lane_bound) = bounds
      Equal.trans(List<&2, Maybe<&2, Attention.Stored>>,
        Laws.selected_outputs(Spec.Partition{input, state, values, lane} <> rest, prefix, head256, rows32),
        Spec.finish_result(input, state, Spec.reference(prefix, values, lane)) <>
          Laws.selected_outputs(rest, prefix, head256, rows32),
        Spec.reference_outputs(Spec.Partition{input, state, values, lane} <> rest, prefix),
        Equal.cong(Maybe<&2, Attention.Stored>, List<&2, Maybe<&2, Attention.Stored>>,
          stored => stored <> Laws.selected_outputs(rest, prefix, head256, rows32),
          Spec.finish_result(input, state, Laws.selected(prefix, head256, rows32, values, lane)),
          Spec.finish_result(input, state, Spec.reference(prefix, values, lane)),
          Laws.finish_refinement(prefix, head256, rows32, input, state, values, lane, native_count, count_bound, lane_bound)),
        Equal.cong(List<&2, Maybe<&2, Attention.Stored>>, List<&2, Maybe<&2, Attention.Stored>>,
          stored => Spec.finish_result(input, state, Spec.reference(prefix, values, lane)) <> stored,
          Laws.selected_outputs(rest, prefix, head256, rows32), Spec.reference_outputs(rest, prefix),
          Laws.partition_outputs_refinement(rest, prefix, head256, rows32, native_count, count_bound, rest_domain)))

def Laws.partition_outputs_complete(partitions, prefix, native_count, count_bound, domain):
  match partitions:
    case Nil{}:
      Unit{}
    case Spec.Partition{input, state, values, lane} <> rest:
      (bounds, rest_domain) = domain
      (input_bound, lane_bound) = bounds
      (finish_present(input, state, Laws.selected(prefix, True{}, True{}, values, lane),
        Laws.selected_complete(prefix, values, lane, native_count, count_bound, lane_bound, input_bound)),
        Laws.partition_outputs_complete(rest, prefix, native_count, count_bound, rest_domain))
