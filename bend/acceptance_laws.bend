# Pure acceptance laws only: no GPU arithmetic, inference quality or speed claim.
# The seven equality bits correspond to candidates[i+1] == target_top1[i].
import Base
import ./acceptance.bend as Acceptance
import ./acceptance_spec.bend as Spec
import ./spec.bend as Sequence
import ./ACCEPT.bend as Wire

# Structural theorem for every finite tree, not just the 128 native masks.
law tree_semantics:
  for +tree: Acceptance.Tree
  {Acceptance.accepted(tree) == Spec.prefix(Spec.flatten(tree)) : Nat}

law tree_bound:
  for +tree: Acceptance.Tree
  {Nat.is_le(Acceptance.accepted(tree), List.length(&2, Bool, Spec.flatten(tree))) == True{} : Bool}

# Every first mismatch is a hard boundary, regardless of the rejected suffix.
# The equality premise is live proof evidence describing the actual tree input.
law first_mismatch:
  for +tree: Acceptance.Tree
  for +n: Nat
  for +suffix: List<&2, Bool>
  for layout: {Spec.flatten(tree) == List.append(&2, Bool,
    List.replicate(Bool, n, True{}), False{} <> suffix) : List<&2, Bool>}
  {Acceptance.accepted(tree) == n : Nat}

law seven_semantics:
  for +b0: Bool
  for +b1: Bool
  for +b2: Bool
  for +b3: Bool
  for +b4: Bool
  for +b5: Bool
  for +b6: Bool
  {Acceptance.accepted(Acceptance.seven(b0, b1, b2, b3, b4, b5, b6)) ==
    Spec.prefix([b0, b1, b2, b3, b4, b5, b6]) : Nat}

law mask_inputs:
  for +mask: Nat
  {Spec.flatten(Acceptance.mask_tree(mask)) == Spec.bits(7n, mask) : List<&2, Bool>}

law mask_semantics:
  for +mask: Nat
  {Acceptance.accept_mask(mask) == Spec.prefix(Spec.bits(7n, mask)) : Nat}

# Nat is nonnegative; this upper bound closes the complete acceptance domain.
law native_bound:
  for +mask: Nat
  {Nat.is_le(Acceptance.accept_mask(mask), 7n) == True{} : Bool}

# Exact ascending mask order and domain, not permutation or membership alone.
law emitter_domain:
  {Acceptance.masks() == Sequence.seq(128n, 0n) : List<&2, Nat>}

law emitter_values:
  {Acceptance.values() == Spec.table(128n, 0n) : List<&2, Nat>}

law emitter_count:
  {List.length(&2, Nat, Acceptance.values()) == 128n : Nat}

law rows_semantics:
  for +values: List<&2, Nat>
  {Wire.rows(values) == Spec.rows(values) : String}

# Header, order, exact row count and terminal marker are all bound above.
# The sole final newline is the trusted IO.print boundary in ACCEPT.main.
law acceptance_wire:
  {Wire.protocol() == Spec.protocol() : String}
