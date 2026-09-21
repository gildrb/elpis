# Universal pure-domain theorems. No theorem here certifies GPU operations,
# NumPy threshold equivalence, loaded-model recurrence, task quality or RNG.
import Base
import ./numerical_spec.bend as Spec
import ./numerical.bend as Numerical

law classification:
  for +negative: Bool
  for +exponent: Nat
  for +fraction: Nat
  for +maximum: Nat
  {Numerical.classify(negative, exponent, fraction, maximum) ==
    Spec.classify(negative, exponent, fraction, maximum) : Spec.Class}

law finite_sound:
  for +value: Spec.Class
  for accepted: {Numerical.finite(value) == True{} : Bool}
  Spec.IsFinite(value)

law rounding:
  for +mode: Spec.Mode
  for +negative: Bool
  for +q: Nat
  for +r: Nat
  for +d: Nat
  {Numerical.round_parts(mode, negative, q, r, d) == Spec.rounding(mode, negative, q, r, d) : Spec.Rounded}

# Genuine universal halfway cases: arbitrary integer k and either sign.
# Even lower magnitude stays even; away increases. Odd lower increases in both.
law even_halfway:
  for +k: Nat
  for +negative: Bool
  {Numerical.round_parts(Spec.TiesEven{}, negative, Nat.double(k), 1n, 2n) == Spec.Rounded{negative, Nat.double(k)} : Spec.Rounded}

law away_halfway:
  for +q: Nat
  for +negative: Bool
  {Numerical.round_parts(Spec.TiesAway{}, negative, q, 1n, 2n) == Spec.Rounded{negative, 1n+q} : Spec.Rounded}

law odd_halfway:
  for +k: Nat
  for +negative: Bool
  {Numerical.round_parts(Spec.TiesEven{}, negative, 1n+Nat.double(k), 1n, 2n) == Spec.Rounded{negative, 2n+Nat.double(k)} : Spec.Rounded}

law zero_denominator:
  for mode: Spec.Mode
  for negative: Bool
  for magnitude: Nat
  {Numerical.round(mode, negative, magnitude, 0n) == None{} : Maybe<&2, Spec.Rounded>}

law pack_value:
  for +bits: List<&2, Bool>
  Spec.Packed(bits, Numerical.pack(bits))

law pack_safe:
  for +bits: List<&2, Bool>
  Spec.SafeCode(List.length(&2, Bool, bits), Numerical.pack(bits))

law pack_unpack:
  for +bits: List<&2, Bool>
  {Numerical.unpack(List.length(&2, Bool, bits), Numerical.pack(bits)) == Some{bits} : Maybe<&2, List<&2, Bool>>}

law overflow_rejected:
  for p: Nat
  {Numerical.unpack(0n, 1n+p) == None{} : Maybe<&2, List<&2, Bool>>}

# A code-range representation theorem applies to arbitrary widths, including
# the 2-bit V, 4-bit K, and 8-bit embedding fields. Width/order extraction is
# still a native refinement obligation, not established by this theorem.
law representation:
  for +bits: List<&2, Bool>
  Spec.Representation(bits, Numerical.pack(bits))

law safe_sound:
  for +width: Nat
  for +code: Nat
  for accepted: {Numerical.safe(width, code) == True{} : Bool}
  Spec.SafeCode(width, code)

law separation_sound:
  for +lower: Nat
  for +upper: Nat
  for accepted: {Numerical.separated(lower, upper) == True{} : Bool}
  Spec.Le(1n+upper, lower)

# For each competitor j, exact upper_j < exact lower_w together with
# candidate_j <= upper_j and lower_w <= candidate_w implies strict argmax.
# With lower_w = reference_w-error_w and upper_j = reference_j+error_j,
# this is precisely the strict gap > error_w+error_j certificate. Shared
# epsilon gives gap>2epsilon. The offset avoids saturating subtraction.
# No current native report supplies these full-vocabulary per-step witnesses.
law strict_argmax:
  for +winner: Nat
  for +lower: Nat
  for +competitors: List<&2, Nat>
  for +uppers: List<&2, Nat>
  for +winner_bound: Spec.Le(lower, winner)
  for margins: Spec.Margin(lower, competitors, uppers)
  Spec.Winner(winner, competitors)

law identity_reflexive:
  for +identity: List<&2, Nat>
  {Numerical.same(identity, identity) == True{} : Bool}

law identity_sound:
  for +actual: List<&2, Nat>
  for +expected: List<&2, Nat>
  for accepted: {Numerical.same(actual, expected) == True{} : Bool}
  {actual == expected : List<&2, Nat>}

law complete_sound:
  for +expected: List<&2, Nat>
  for +identity: List<&2, Nat>
  for +rows: List<&2, Spec.Observation>
  for accepted: {Numerical.complete(expected, identity, rows) == True{} : Bool}
  Spec.Complete(expected, identity, rows)

law observed_progress:
  for +expected: List<&2, Nat>
  for +identity: List<&2, Nat>
  {Numerical.complete(expected, identity, Numerical.observed(expected, identity)) == True{} : Bool}

law missing_rejected:
  for member: Nat
  for expected: List<&2, Nat>
  for identity: List<&2, Nat>
  for rest: List<&2, Spec.Observation>
  {Numerical.complete(member <> expected, identity, Spec.Missing{} <> rest) == False{} : Bool}

law unsupported_rejected:
  for member: Nat
  for expected: List<&2, Nat>
  for identity: List<&2, Nat>
  for rest: List<&2, Spec.Observation>
  {Numerical.complete(member <> expected, identity, Spec.Unsupported{} <> rest) == False{} : Bool}

law cancelled_rejected:
  for member: Nat
  for expected: List<&2, Nat>
  for identity: List<&2, Nat>
  for rest: List<&2, Spec.Observation>
  {Numerical.complete(member <> expected, identity, Spec.Cancelled{} <> rest) == False{} : Bool}

law bounded_error_sound:
  for +candidate: Nat
  for +reference: Nat
  for +error: Nat
  for accepted: {Numerical.bounded_error(candidate, reference, error) == True{} : Bool}
  Spec.Approximate(candidate, reference, error)

# A zero-error approximation has a genuine successful witness at every value.
law exact_error_progress:
  for +value: Nat
  {Numerical.bounded_error(value, value, 0n) == True{} : Bool}
