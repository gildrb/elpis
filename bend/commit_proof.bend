# Live structural proofs over arbitrary counts and rejected suffixes.
# The finite wire boundary is separate from the generic semantic argument.
import Base
import ./commit.bend as Commit
import ./commit_spec.bend as Spec
import ./commit_laws.bend as Laws

def proposals_length(count: Nat, start: Nat)
  -> {Spec.length(Spec.proposals(count, start)) == count : Nat}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      %proposals_length(p, 1n+start) : {1n+Spec.length(Spec.proposals(p, 1n+start)) == 1n+_ : Nat}
      {==}

def output_length(count: Nat, start: Nat, bonus: Nat)
  -> {Spec.length(List.append(&2, Spec.Source, Spec.proposals(count, start), [Spec.Bonus{bonus}])) == 1n+count : Nat}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      %output_length(p, 1n+start, bonus) : {1n+Spec.length(List.append(&2, Spec.Source, Spec.proposals(p, 1n+start), [Spec.Bonus{bonus}])) == 1n+_ : Nat}
      {==}

# This is a generic prefix theorem, not an eight-row enumeration: even an
# arbitrarily long or differently tagged suffix is entirely excluded.
def take_proposals(count: Nat, start: Nat, rejected: List<&2, Spec.Source>)
  -> {Spec.take(count, List.append(&2, Spec.Source, Spec.proposals(count, start), rejected)) == Spec.proposals(count, start) : List<&2, Spec.Source>}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      %take_proposals(p, 1n+start, rejected) : {Spec.Input{start} <> Spec.take(p, List.append(&2, Spec.Source, Spec.proposals(p, 1n+start), rejected)) == Spec.Input{start} <> _ : List<&2, Spec.Source>}
      {==}

def proposals_materialized(count: Nat, start: Nat)
  -> {Spec.inputs_only(Spec.proposals(count, start)) == True{} : Bool}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      proposals_materialized(p, 1n+start)

def Laws.row_refinement(accepted):
  %proposals_length(accepted, 1n) : {Commit.Plan{1n+_, accepted} == Spec.row(accepted) : Commit.Plan}
  %proposals_length(accepted, 1n) : {Commit.Plan{1n+Spec.length(Spec.proposals(accepted, 1n)), _} == Spec.row(accepted) : Commit.Plan}
  {==}

def choose_refinement(valid: Bool, +accepted: Nat)
  -> {Commit.choose(valid, Commit.row(accepted)) == Spec.choose(valid, Spec.row(accepted)) : Maybe<&2, Commit.Plan>}:
  match valid:
    case False{}:
      {==}
    case True{}:
      %Laws.row_refinement(accepted) : {Some{Commit.row(accepted)} == Some{_} : Maybe<&2, Commit.Plan>}
      {==}

def Laws.plan_refinement(accepted):
  choose_refinement(Nat.is_le(accepted, 7n), accepted)

def Laws.committed_length(accepted):
  %proposals_length(accepted, 1n) : {1n+Spec.length(Spec.proposals(accepted, 1n)) == 1n+_ : Nat}
  {==}

def Laws.emitted_length(accepted):
  output_length(accepted, 1n, accepted)

def Laws.bonus_position(accepted):
  proposals_length(accepted, 1n)

def Laws.rejected_suffix_excluded(accepted, rejected):
  %take_proposals(accepted, 1n, rejected) : {Spec.Input{0n} <> Spec.take(accepted, List.append(&2, Spec.Source, Spec.proposals(accepted, 1n), rejected)) == Spec.Input{0n} <> _ : List<&2, Spec.Source>}
  {==}

def Laws.bonus_not_materialized(accepted):
  proposals_materialized(accepted, 1n)

def Laws.valid_plan(accepted, valid):
  %Equal.sym(Bool, Nat.is_le(accepted, 7n), True{}, valid) : {Commit.choose(_, Commit.row(accepted)) == Some{Commit.row(accepted)} : Maybe<&2, Commit.Plan>}
  {==}

# Successor comparison cancels one materialized anchor on both sides.
def Laws.commit_upper_bound(accepted, valid):
  valid

def Laws.bonus_upper_bound(accepted, valid):
  valid

def Laws.anchor_lower_bound(accepted):
  {==}

def Laws.out_of_domain_rejected(extra):
  {==}

def Laws.zero_acceptance():
  ({==}, {==}, {==})

def Laws.all_acceptance():
  ({==}, {==}, {==})

def Laws.table_order():
  {==}
