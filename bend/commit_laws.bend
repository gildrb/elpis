# Laws concern provenance and index/length decisions, not numerical GPU,
# KV contents, recurrent state, or host/device execution correctness.
import Base
import ./commit.bend as Commit
import ./commit_spec.bend as Spec

law row_refinement:
  for +accepted: Nat
  {Commit.row(accepted) == Spec.row(accepted) : Commit.Plan}

law plan_refinement:
  for +accepted: Nat
  {Commit.plan(accepted) == Spec.plan(accepted) : Maybe<&2, Commit.Plan>}

law committed_length:
  for +accepted: Nat
  {Spec.length(Spec.committed(accepted)) == Commit.commit_length(Commit.row(accepted)) : Nat}

law emitted_length:
  for +accepted: Nat
  {Spec.length(Spec.emitted(accepted)) == Commit.commit_length(Commit.row(accepted)) : Nat}

law bonus_position:
  for +accepted: Nat
  {Spec.length(Spec.proposals(accepted, 1n)) == Commit.bonus_index(Commit.row(accepted)) : Nat}

# Arbitrary suffix and unbounded accepted count: changing any rejected input
# cannot change the committed prefix selected by the planned length.
law rejected_suffix_excluded:
  for +accepted: Nat
  for rejected: List<&2, Spec.Source>
  {Spec.take(Commit.commit_length(Commit.row(accepted)), Spec.materialized(accepted, rejected)) == Spec.committed(accepted) : List<&2, Spec.Source>}

law bonus_not_materialized:
  for accepted: Nat
  {Spec.inputs_only(Spec.committed(accepted)) == True{} : Bool}

law valid_plan:
  for +accepted: Nat
  for valid: {Nat.is_le(accepted, 7n) == True{} : Bool}
  {Commit.plan(accepted) == Some{Commit.row(accepted)} : Maybe<&2, Commit.Plan>}

law commit_upper_bound:
  for +accepted: Nat
  for valid: {Nat.is_le(accepted, 7n) == True{} : Bool}
  {Nat.is_le(Commit.commit_length(Commit.row(accepted)), 8n) == True{} : Bool}

law bonus_upper_bound:
  for +accepted: Nat
  for valid: {Nat.is_le(accepted, 7n) == True{} : Bool}
  {Nat.is_le(Commit.bonus_index(Commit.row(accepted)), 7n) == True{} : Bool}

law anchor_lower_bound:
  for accepted: Nat
  {Nat.is_lt(0n, Commit.commit_length(Commit.row(accepted))) == True{} : Bool}

law out_of_domain_rejected:
  for extra: Nat
  {Commit.plan(8n+extra) == None{} : Maybe<&2, Commit.Plan>}

law zero_acceptance:
  {Commit.plan(0n) == Some{Commit.Plan{1n, 0n}} : Maybe<&2, Commit.Plan>} &
  {Spec.committed(0n) == [Spec.Input{0n}] : List<&2, Spec.Source>} &
  {Spec.emitted(0n) == [Spec.Bonus{0n}] : List<&2, Spec.Source>}

law all_acceptance:
  {Commit.plan(7n) == Some{Commit.Plan{8n, 7n}} : Maybe<&2, Commit.Plan>} &
  {Spec.length(Spec.committed(7n)) == 8n : Nat} &
  {Spec.length(Spec.emitted(7n)) == 8n : Nat}

law table_order:
  {Commit.table() == Some{[Commit.row(0n), Commit.row(1n), Commit.row(2n), Commit.row(3n), Commit.row(4n), Commit.row(5n), Commit.row(6n), Commit.row(7n)]} : Maybe<&2, List<&2, Commit.Plan>>}
