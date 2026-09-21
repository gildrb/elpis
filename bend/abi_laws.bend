# Abstract scalar/tensor obligations only. None assert that a native pointer,
# generated C function, CUDA event, or host observation has these semantics.
import Base
import ./abi.bend as Impl
import ./abi_spec.bend as Spec

law index_refinement:
  for +n: Nat
  {Impl.decode(n) == Spec.decode(n) : Maybe<&2, Spec.Slot>}

law index_progress:
  for +slot: Spec.Slot
  {Impl.decode(Spec.index(slot)) == Some{slot} : Maybe<&2, Spec.Slot>}

law index_rejected:
  for n: Nat
  {Impl.decode(8n+n) == None{} : Maybe<&2, Spec.Slot>}

law index_bound:
  for slot: Spec.Slot
  {Nat.is_lt(Spec.index(slot), 8n) == True{} : Bool}

law four_word_refinement:
  for +accepted: Spec.Slot
  {Impl.words(accepted) == Spec.words(accepted) : List<&2, Nat>}

law four_word_arity:
  for accepted: Spec.Slot
  {List.length(&2, Nat, Impl.words(accepted)) == 4n : Nat}

law four_word_projection:
  for +accepted: Spec.Slot
  {Spec.at(0n, Impl.words(accepted)) == Some{Spec.index(accepted)} : Maybe<&2, Nat>} &
  {Spec.at(1n, Impl.words(accepted)) == Some{1n+Spec.index(accepted)} : Maybe<&2, Nat>} &
  {Spec.at(2n, Impl.words(accepted)) == Some{Spec.index(accepted)} : Maybe<&2, Nat>} &
  {Spec.at(3n, Impl.words(accepted)) == Some{1n+Spec.index(accepted)} : Maybe<&2, Nat>}

law word_out_of_range:
  for accepted: Spec.Slot
  for n: Nat
  {Spec.at(4n+n, Impl.words(accepted)) == None{} : Maybe<&2, Nat>}

law word_scalar_bounds:
  for +accepted: Spec.Slot
  {Nat.is_le(1n+Spec.index(accepted), 8n) == True{} : Bool} &
  {Spec.Fits(48n, 1n+Spec.index(accepted)) == True{} : Bool}

# All 8x8 accepted/output indices, including cells beyond the emitted prefix.
law transport_refinement:
  for +accepted: Spec.Slot
  for +slot: Spec.Slot
  {Some{Impl.project(accepted, slot)} ==
    Spec.source_at(Spec.index(slot), Spec.transport(accepted)) : Maybe<&2, Spec.Source>}

law bonus_provenance:
  for +accepted: Spec.Slot
  {Impl.project(accepted, accepted) == Spec.TargetBonus{Spec.index(accepted)} : Spec.Source}

law committed_count:
  for +accepted: Spec.Slot
  {List.length(&2, Nat, Spec.committed(accepted)) == 1n+Spec.index(accepted) : Nat}

law address_within_row:
  for +row: Nat
  for +slot: Spec.Slot
  {Nat.is_lt(Nat.add(Nat.mul(row, 8n), Spec.index(slot)),
    Nat.add(Nat.mul(row, 8n), 8n)) == True{} : Bool}

law prefix_stride_units:
  for +width: Spec.Width
  for +row: Nat
  for +stride: Nat
  {Impl.prefix_element(row, stride) == Spec.prefix_element(row, stride) : Spec.ElementOffset} &
  {Impl.prefix_byte(width, row, stride) ==
    Spec.element_bytes(width, Spec.prefix_element(row, stride)) : Spec.ByteOffset}

law broadcast_stride:
  for +width: Spec.Width
  for +row: Nat
  {Impl.prefix_byte(width, row, 0n) == Spec.Bytes{0n} : Spec.ByteOffset}

# Full arbitrary signed-input transport, with explicit malformed/absent/cancelled
# states. This law does not impose the nonnegative logical-sequence contract.
law signed_transport:
  for +source: Spec.Width
  for +dest: Spec.Width
  for +raw: Spec.Raw
  {Impl.transfer(source, dest, raw) == Spec.transfer(source, dest, raw) : Spec.Transfer}

law converted_width:
  for +dest: Spec.Width
  for +xs: List<&2, Bool>
  {List.length(&2, Bool, Impl.converted(dest, xs)) == Spec.bits(dest) : Nat}

law narrow_low_bits:
  for +low: List<&2, Bool>
  for +high: List<&2, Bool>
  for exact: {List.length(&2, Bool, low) == 32n : Nat}
  {Impl.converted(Spec.I32{}, List.append(&2, Bool, low, high)) == low : List<&2, Bool>}

law signed_widen:
  for +low: List<&2, Bool>
  for +negative: Bool
  for exact: {List.length(&2, Bool, low) == 31n : Nat}
  {Impl.converted(Spec.I64{}, List.append(&2, Bool, low, [negative])) ==
    List.append(&2, Bool, low, List.replicate(Bool, 33n, negative)) : List<&2, Bool>}

law ripple_reference:
  for +xs: List<&2, Bool>
  {Impl.carry(xs, True{}) == Spec.bump(xs) : List<&2, Bool>}

law advance_reference:
  for +delta: Nat
  for +xs: List<&2, Bool>
  {Impl.advance(delta, xs) == Spec.advance(delta, xs) : List<&2, Bool>}

law advance_width:
  for delta: Nat
  for +xs: List<&2, Bool>
  {List.length(&2, Bool, Impl.advance(delta, xs)) == List.length(&2, Bool, xs) : Nat}

law wrapping_sequence:
  for +source: Spec.Width
  for +dest: Spec.Width
  for +delta: Nat
  for +raw: Spec.Raw
  {Impl.sequence(source, dest, delta, raw) == Spec.sequence(source, dest, delta, raw) : Spec.Transfer}

# SafeAdvance is independent bit-level evidence, not a conclusion from delta<=8.
# Native does not check it; absent value instrumentation leaves this conditional.
law semantic_advance:
  for +delta: Nat
  for +xs: List<&2, Bool>
  for safe: Spec.SafeAdvance(delta, xs)
  {Spec.unsigned(Impl.advance(delta, xs)) == Nat.add(delta, Spec.unsigned(xs)) : Nat}

law nonnegative_advance:
  for +delta: Nat
  for +xs: List<&2, Bool>
  for safe: Spec.SafeAdvance(delta, xs)
  {Spec.sign(Impl.advance(delta, xs)) == False{} : Bool}

law admission_refinement:
  for +observations: List<&2, Spec.Observation>
  {Impl.admit(observations) == Spec.admit(observations) : Spec.Admission}

law invalid_classification:
  for +check: Spec.Check
  for +rest: List<&2, Spec.Observation>
  {Impl.admit(Spec.Unknown{check} <> rest) == Spec.Unobserved{check} : Spec.Admission} &
  {Impl.admit(Spec.Failed{check} <> rest) == Spec.Rejected{check} : Spec.Admission} &
  {Impl.admit(Spec.Stopped{} <> rest) == Spec.CancelLaunch{} : Spec.Admission}

law passed_progress:
  for check: Spec.Check
  for +rest: List<&2, Spec.Observation>
  {Impl.admit(Spec.Passed{check} <> rest) == Impl.admit(rest) : Spec.Admission}

# Concrete successful native-width witness and signed-overflow counterexample:
# int32 max+1 widens as a NEGATIVE int64, not as the Nat successor.
law sequence_progress:
  {Impl.sequence(Spec.I32{}, Spec.I64{}, 8n,
    Spec.Bits{List.replicate(Bool, 32n, False{})}) ==
    Spec.Value{False{} <> False{} <> False{} <> True{} <>
      List.replicate(Bool, 60n, False{})} : Spec.Transfer}

law signed_overflow_preserved:
  {Impl.sequence(Spec.I32{}, Spec.I64{}, 1n,
    Spec.Bits{List.append(&2, Bool, List.replicate(Bool, 31n, True{}), [False{}])}) ==
    Spec.Value{List.append(&2, Bool, List.replicate(Bool, 31n, False{}),
      List.replicate(Bool, 33n, True{}))} : Spec.Transfer}

law comparison_refinement:
  for +slot: Spec.Slot
  {Impl.comparison(slot) == Spec.comparison(slot) : Maybe<&2, Spec.ComparisonPair>}

law prefix_broadcast_extent:
  for batch_predecessor: Nat
  {Spec.prefix_extent(1n+batch_predecessor, 0n) == 1n : Nat}

law missing_cancelled:
  for +source: Spec.Width
  for +dest: Spec.Width
  for +delta: Nat
  {Impl.sequence(source, dest, delta, Spec.Missing{}) == Spec.Absent{} : Spec.Transfer} &
  {Impl.sequence(source, dest, delta, Spec.Cancelled{}) == Spec.Aborted{} : Spec.Transfer}

law malformed_classification:
  for +source: Spec.Width
  for +dest: Spec.Width
  for +delta: Nat
  for +xs: List<&2, Bool>
  for invalid: {Spec.valid_width(source, xs) == False{} : Bool}
  {Impl.sequence(source, dest, delta, Spec.Bits{xs}) == Spec.Malformed{} : Spec.Transfer}

# Output int32 is a semantic length only when the discarded high bits are zero
# AND the retained sign bit is nonnegative. This premise cannot be replaced by
# delta<=8. This composes with semantic_advance at the post-addition bit vector.
law logical_narrow:
  for +low: List<&2, Bool>
  for +padding: Nat
  for exact: {List.length(&2, Bool, low) == 32n : Nat}
  for nonnegative: {Spec.sign(low) == False{} : Bool}
  {Spec.unsigned(Impl.converted(Spec.I32{},
    List.append(&2, Bool, low, List.replicate(Bool, padding, False{})))) ==
    Spec.unsigned(List.append(&2, Bool, low, List.replicate(Bool, padding, False{}))) : Nat} &
  {Spec.sign(Impl.converted(Spec.I32{},
    List.append(&2, Bool, low, List.replicate(Bool, padding, False{})))) == False{} : Bool}

# Nonnegative int32 -> int64 preserves the mathematical value after addition.
law logical_widen:
  for +low: List<&2, Bool>
  for exact: {List.length(&2, Bool, low) == 31n : Nat}
  {Spec.unsigned(Impl.converted(Spec.I64{},
    List.append(&2, Bool, low, [False{}]))) ==
    Spec.unsigned(List.append(&2, Bool, low, [False{}])) : Nat}

# Constructive witness inhabits the no-overflow premises at the actual native
# width and maximal native delta. Thus semantic_advance is not vacuous.
law native_safe_progress:
  Spec.SafeAdvance(8n, List.replicate(Bool, 32n, False{}))
