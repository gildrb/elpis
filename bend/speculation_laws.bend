# Semantic obligations for the actual unified decisions, independent of the
# retired tree reducer and standalone eight-row commit API.
import Base
import ./speculation.bend as Impl
import ./speculation_spec.bend as Spec

law decision_refinement:
  for +accepted: Nat
  {Impl.decision(accepted) == Spec.decision(accepted) : Spec.Decision}

law prefix_bound:
  for +flags: List<&2, Bool>
  {Nat.is_le(Spec.accepted_count(Impl.decide(flags)), List.length(&2, Bool, flags)) == True{} : Bool}

# The entire decision ignores every comparison after the first mismatch.
law first_mismatch:
  for +accepted: Nat
  for +suffix: List<&2, Bool>
  {Impl.decide(List.append(&2, Bool, List.replicate(Bool, accepted, True{}),
    False{} <> suffix)) == Impl.decision(accepted) : Spec.Decision}

law seven_bound:
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  for b5: Bool
  for b6: Bool
  {Nat.is_le(Spec.accepted_count(Impl.decide([b0, b1, b2, b3, b4, b5, b6])), 7n) == True{} : Bool}

law native_bound:
  for +mask: Nat
  {Nat.is_le(Spec.accepted_count(Impl.decide(Spec.flags(7n, mask))), 7n) == True{} : Bool}

law committed_length:
  for +accepted: Nat
  {Spec.length(Spec.committed(accepted)) == Spec.commit_count(Impl.decision(accepted)) : Nat}

law emitted_length:
  for +accepted: Nat
  {Spec.length(Spec.emitted(accepted)) == Spec.commit_count(Impl.decision(accepted)) : Nat}

law bonus_position:
  for +accepted: Nat
  {Spec.length(Spec.proposals(accepted, 1n)) == Spec.bonus_index(Impl.decision(accepted)) : Nat}

law rejected_suffix_excluded:
  for +accepted: Nat
  for rejected: List<&2, Spec.Source>
  {Spec.take(Spec.commit_count(Impl.decision(accepted)), Spec.materialized(accepted, rejected)) == Spec.committed(accepted) : List<&2, Spec.Source>}

law committed_inputs_only:
  for accepted: Nat
  {Spec.inputs_only(Spec.committed(accepted)) == True{} : Bool}

# No bonus is materialized in the prefix selected by the actual decision,
# regardless of arbitrary tags or values in the rejected suffix.
law bonus_not_materialized:
  for +accepted: Nat
  for rejected: List<&2, Spec.Source>
  {Spec.inputs_only(Spec.take(Spec.commit_count(Impl.decision(accepted)),
    Spec.materialized(accepted, rejected))) == True{} : Bool}

law anchor_lower_bound:
  for accepted: Nat
  {Nat.is_lt(0n, Spec.commit_count(Impl.decision(accepted))) == True{} : Bool}

law commit_upper_bound:
  for +accepted: Nat
  for valid: {Nat.is_le(accepted, 7n) == True{} : Bool}
  {Nat.is_le(Spec.commit_count(Impl.decision(accepted)), 8n) == True{} : Bool}

law bonus_upper_bound:
  for +accepted: Nat
  for valid: {Nat.is_le(accepted, 7n) == True{} : Bool}
  {Nat.is_le(Spec.bonus_index(Impl.decision(accepted)), 7n) == True{} : Bool}

law advance_committed:
  for +accepted: Nat
  {Spec.advance_count(Impl.decision(accepted)) == Spec.commit_count(Impl.decision(accepted)) : Nat}

law zero_acceptance:
  {Impl.decision(0n) == Spec.Decision{0n, 1n, 0n, 1n} : Spec.Decision} &
  {Spec.committed(0n) == [Spec.Input{0n}] : List<&2, Spec.Source>} &
  {Spec.emitted(0n) == [Spec.Bonus{0n}] : List<&2, Spec.Source>}

law all_acceptance:
  {Impl.decision(7n) == Spec.Decision{7n, 8n, 7n, 8n} : Spec.Decision} &
  {Spec.length(Spec.committed(7n)) == 8n : Nat} &
  {Spec.length(Spec.emitted(7n)) == 8n : Nat}
