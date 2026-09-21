# Structural induction and constructor proofs only. No testing-as-proof,
# imported native facts, compiler assertions, floating axioms or holes.
import Base
import ./numerical_spec.bend as Spec
import ./numerical.bend as Numerical
import ./numerical_laws.bend as Laws

def false_true(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : Spec.Truth(_)
  Unit{}

def and_true(+a: Bool, +b: Bool, e: {Bool.and(a, b) == True{} : Bool})
  -> {a == True{} : Bool} & {b == True{} : Bool}:
  match a:
    case False{}:
      Empty.absurd({False{} == True{} : Bool} & {b == True{} : Bool}, false_true(e))
    case True{}:
      ({==}, e)

def nat_eq(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_eq(p)

def nat_eq_sound(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool})
  -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, false_true(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, false_true(e))
    case 1n+p 1n+q:
      %nat_eq_sound(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def double_not(+b: Bool) -> {Bool.not(Bool.not(b)) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def odd_semantics(+n: Nat) -> {Numerical.odd(n) == Spec.odd(n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          %Equal.sym(Bool, Bool.not(Bool.not(Spec.odd(q))), Spec.odd(q), double_not(Spec.odd(q))) : {Numerical.odd(q) == _ : Bool}
          odd_semantics(q)

def bump_semantics(+parity: Bool, +q: Nat)
  -> {Numerical.bump(parity, q) == Spec.nearest_even(parity, q) : Nat}:
  match parity:
    case False{}:
      {==}
    case True{}:
      {==}

def nearest_semantics(+mode: Spec.Mode, +q: Nat, +position: Cmp)
  -> {Numerical.nearest(mode, q, position) == Spec.nearest(mode, q, position) : Nat}:
  match mode position:
    case rounding_mode LT{}:
      {==}
    case rounding_mode GT{}:
      {==}
    case Spec.TiesAway{} EQ{}:
      {==}
    case Spec.TiesEven{} EQ{}:
      Equal.trans(Nat, Numerical.bump(Numerical.odd(q), q),
        Numerical.bump(Spec.odd(q), q), Spec.nearest_even(Spec.odd(q), q),
        Equal.cong(Bool, Nat, parity => Numerical.bump(parity, q),
          Numerical.odd(q), Spec.odd(q), odd_semantics(q)),
        bump_semantics(Spec.odd(q), q))

def Laws.rounding(mode, negative, q, r, d):
  Equal.cong(Nat, Spec.Rounded, n => Spec.Rounded{negative, n},
    Numerical.nearest(mode, q, Nat.cmp(Nat.double(r), d)),
    Spec.nearest(mode, q, Nat.cmp(Nat.double(r), d)),
    nearest_semantics(mode, q, Nat.cmp(Nat.double(r), d)))

def even_parity(k: Nat) -> {Numerical.odd(Nat.double(k)) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      even_parity(p)

def odd_parity(k: Nat) -> {Numerical.odd(1n+Nat.double(k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      odd_parity(p)

def Laws.even_halfway(k, negative):
  %Equal.sym(Bool, Numerical.odd(Nat.double(k)), False{}, even_parity(k)) :
    {Spec.Rounded{negative, Numerical.bump(_, Nat.double(k))} == Spec.Rounded{negative, Nat.double(k)} : Spec.Rounded}
  {==}

def Laws.away_halfway(q, negative):
  {==}

def Laws.odd_halfway(k, negative):
  %Equal.sym(Bool, Numerical.odd(1n+Nat.double(k)), True{}, odd_parity(k)) :
    {Spec.Rounded{negative, Numerical.bump(_, 1n+Nat.double(k))} == Spec.Rounded{negative, 2n+Nat.double(k)} : Spec.Rounded}
  {==}

def Laws.zero_denominator(mode, negative, magnitude):
  {==}

def classification_order(+negative: Bool, +order: Cmp, +fraction: Nat)
  -> {Numerical.classify_order(negative, order, fraction) == Spec.finite_class(negative, order, fraction) : Spec.Class}:
  match negative order fraction:
    case False{} LT{} mantissa:
      {==}
    case True{} LT{} mantissa:
      {==}
    case False{} GT{} mantissa:
      {==}
    case True{} GT{} mantissa:
      {==}
    case False{} EQ{} 0n:
      {==}
    case True{} EQ{} 0n:
      {==}
    case False{} EQ{} 1n+p:
      {==}
    case True{} EQ{} 1n+p:
      {==}

def Laws.classification(negative, exponent, fraction, maximum):
  classification_order(negative, Nat.cmp(exponent, maximum), fraction)

def Laws.finite_sound(value, accepted):
  match value:
    case Spec.Finite{}:
      Unit{}
    case Spec.PositiveInfinity{}:
      false_true(accepted)
    case Spec.NegativeInfinity{}:
      false_true(accepted)
    case Spec.NotANumber{}:
      false_true(accepted)
    case Spec.InvalidEncoding{}:
      false_true(accepted)

def add_succ(n: Nat, -m: Nat) -> {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, m) : {1n+Nat.add(p, 1n+m) == 1n+_ : Nat}
      {==}

def double_add(+n: Nat) -> {Nat.double(n) == Nat.add(n, n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), add_succ(p, p)) : {2n+Nat.double(p) == 1n+_ : Nat}
      %double_add(p) : {2n+Nat.double(p) == 2n+_ : Nat}
      {==}

def Laws.pack_value(bits):
  match bits:
    case Nil{}:
      {==}
    case False{} <> rest:
      %double_add(Spec.value(rest)) : {Nat.double(Numerical.pack(rest)) == _ : Nat}
      Equal.cong(Nat, Nat, Nat.double, Numerical.pack(rest), Spec.value(rest), Laws.pack_value(rest))
    case True{} <> rest:
      %double_add(Spec.value(rest)) : {1n+Nat.double(Numerical.pack(rest)) == 1n+_ : Nat}
      Equal.cong(Nat, Nat, n => 1n+Nat.double(n), Numerical.pack(rest), Spec.value(rest), Laws.pack_value(rest))

def le_zero(n: Nat) -> Spec.Le(0n, n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      Unit{}

def le_trans(+a: Nat, +b: Nat, +c: Nat, ab: Spec.Le(a, b), bc: Spec.Le(b, c)) -> Spec.Le(a, c):
  match a b:
    case 0n 0n:
      le_zero(c)
    case 0n 1n+q:
      le_zero(c)
    case 1n+p 0n:
      Empty.absurd(Spec.Le(1n+p, c), ab)
    case 1n+p 1n+q:
      match c:
        case 0n:
          Empty.absurd(Spec.Le(1n+p, 0n), bc)
        case 1n+r:
          le_trans(p, q, r, ab, bc)

def le_drop(+a: Nat, +b: Nat, p: Spec.Le(1n+a, b)) -> Spec.Le(a, b):
  match a b:
    case 0n 0n:
      Empty.absurd(Spec.Le(0n, 0n), p)
    case 0n 1n+q:
      Unit{}
    case 1n+r 0n:
      p
    case 1n+r 1n+q:
      le_drop(r, q, p)

def double_le(+a: Nat, +b: Nat, p: Spec.Le(a, b)) -> Spec.Le(Nat.double(a), Nat.double(b)):
  match a b:
    case 0n 0n:
      Unit{}
    case 0n 1n+q:
      Unit{}
    case 1n+r 0n:
      p
    case 1n+r 1n+q:
      double_le(r, q, p)

def Laws.pack_safe(bits):
  match bits:
    case Nil{}:
      Unit{}
    case False{} <> rest:
      le_drop(1n+Nat.double(Numerical.pack(rest)), Nat.double(Spec.power2(List.length(&2, Bool, rest))),
        double_le(1n+Numerical.pack(rest), Spec.power2(List.length(&2, Bool, rest)), Laws.pack_safe(rest)))
    case True{} <> rest:
      double_le(1n+Numerical.pack(rest), Spec.power2(List.length(&2, Bool, rest)), Laws.pack_safe(rest))

def split_even(+n: Nat) -> {Numerical.split(Nat.double(n)) == Numerical.Split{n, False{}} : Numerical.Split}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Numerical.Split, Numerical.Split, Numerical.split_step,
        Numerical.split(Nat.double(p)), Numerical.Split{p, False{}}, split_even(p))

def split_odd(+n: Nat) -> {Numerical.split(1n+Nat.double(n)) == Numerical.Split{n, True{}} : Numerical.Split}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Numerical.Split, Numerical.Split,
        pair => Numerical.split_step(pair),
        Numerical.split(1n+Nat.double(p)), Numerical.Split{p, True{}}, split_odd(p))

def Laws.pack_unpack(bits):
  match bits:
    case Nil{}:
      {==}
    case False{} <> rest:
      Equal.trans(Maybe<&2, List<&2, Bool>>,
        Numerical.unpack(1n+List.length(&2, Bool, rest), Nat.double(Numerical.pack(rest))),
        Numerical.prepend(False{}, Numerical.unpack(List.length(&2, Bool, rest), Numerical.pack(rest))),
        Some{False{} <> rest},
        Equal.cong(Numerical.Split, Maybe<&2, List<&2, Bool>>,
          pair => Numerical.unpack_step(List.length(&2, Bool, rest), pair),
          Numerical.split(Nat.double(Numerical.pack(rest))), Numerical.Split{Numerical.pack(rest), False{}},
          split_even(Numerical.pack(rest))),
        Equal.cong(Maybe<&2, List<&2, Bool>>, Maybe<&2, List<&2, Bool>>,
          xs => Numerical.prepend(False{}, xs),
          Numerical.unpack(List.length(&2, Bool, rest), Numerical.pack(rest)),
          Some{rest}, Laws.pack_unpack(rest)))
    case True{} <> rest:
      Equal.trans(Maybe<&2, List<&2, Bool>>,
        Numerical.unpack(1n+List.length(&2, Bool, rest), 1n+Nat.double(Numerical.pack(rest))),
        Numerical.prepend(True{}, Numerical.unpack(List.length(&2, Bool, rest), Numerical.pack(rest))),
        Some{True{} <> rest},
        Equal.cong(Numerical.Split, Maybe<&2, List<&2, Bool>>,
          pair => Numerical.unpack_step(List.length(&2, Bool, rest), pair),
          Numerical.split(1n+Nat.double(Numerical.pack(rest))), Numerical.Split{Numerical.pack(rest), True{}},
          split_odd(Numerical.pack(rest))),
        Equal.cong(Maybe<&2, List<&2, Bool>>, Maybe<&2, List<&2, Bool>>,
          xs => Numerical.prepend(True{}, xs),
          Numerical.unpack(List.length(&2, Bool, rest), Numerical.pack(rest)),
          Some{rest}, Laws.pack_unpack(rest)))

def Laws.overflow_rejected(p):
  {==}

def Laws.representation(bits):
  (Laws.pack_value(bits), Laws.pack_safe(bits))

def lt_sound(+a: Nat, +b: Nat, p: {Nat.is_lt(a, b) == True{} : Bool}) -> Spec.Le(1n+a, b):
  match a b:
    case 0n 0n:
      false_true(p)
    case 0n 1n+q:
      le_zero(q)
    case 1n+r 0n:
      false_true(p)
    case 1n+r 1n+q:
      lt_sound(r, q, p)

def Laws.safe_sound(width, code, accepted):
  lt_sound(code, Spec.power2(width), accepted)

def Laws.separation_sound(lower, upper, accepted):
  lt_sound(upper, lower, accepted)

def Laws.strict_argmax(winner, lower, competitors, uppers, winner_bound, margins):
  match competitors uppers:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} h <> t:
      Empty.absurd(Spec.Winner(winner, Nil{}), margins)
    case h <> t Nil{}:
      Empty.absurd(Spec.Winner(winner, h <> t), margins)
    case h <> t u <> us:
      ((bound, gap), rest) = margins
      (le_trans(1n+h, lower, winner,
        le_trans(1n+h, 1n+u, lower, bound, gap), winner_bound),
        Laws.strict_argmax(winner, lower, t, us, winner_bound, rest))

def Laws.identity_reflexive(identity):
  match identity:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(Bool, Nat.is_eq(h, h), True{}, nat_eq(h)) : {Bool.and(_, Numerical.same(t, t)) == True{} : Bool}
      Laws.identity_reflexive(t)

def identity_join(+h: Nat, +t: List<&2, Nat>, +j: Nat, +rest: List<&2, Nat>,
    tail_proof: {Numerical.same(t, rest) == True{} : Bool} -> {t == rest : List<&2, Nat>},
    proofs: {Nat.is_eq(h, j) == True{} : Bool} & {Numerical.same(t, rest) == True{} : Bool})
  -> {h <> t == j <> rest : List<&2, Nat>}:
  (heads, tails) = proofs
  %nat_eq_sound(h, j, heads) : {h <> t == _ <> rest : List<&2, Nat>}
  %tail_proof(tails) : {h <> t == h <> _ : List<&2, Nat>}
  {==}

def Laws.identity_sound(actual, expected, accepted):
  match actual expected:
    case Nil{} Nil{}:
      {==}
    case Nil{} h <> t:
      Empty.absurd({Nil{} == h <> t : List<&2, Nat>}, false_true(accepted))
    case h <> t Nil{}:
      Empty.absurd({h <> t == Nil{} : List<&2, Nat>}, false_true(accepted))
    case h <> t j <> rest:
      identity_join(h, t, j, rest, tail_ok => Laws.identity_sound(t, rest, tail_ok),
        and_true(Nat.is_eq(h, j), Numerical.same(t, rest), accepted))

def complete_tail(+h: Nat, +t: List<&2, Nat>, +identity: List<&2, Nat>,
    +member: Nat, +actual: List<&2, Nat>, +rest: List<&2, Spec.Observation>,
    member_ok: {Nat.is_eq(member, h) == True{} : Bool},
    tail_proof: {Numerical.complete(t, identity, rest) == True{} : Bool} -> Spec.Complete(t, identity, rest),
    proofs: {Numerical.same(actual, identity) == True{} : Bool} &
      {Numerical.complete(t, identity, rest) == True{} : Bool})
  -> Spec.Complete(h <> t, identity, Spec.Observed{member, actual} <> rest):
  (identity_ok, rest_ok) = proofs
  ((nat_eq_sound(member, h, member_ok), Laws.identity_sound(actual, identity, identity_ok)),
    tail_proof(rest_ok))

def complete_join(+h: Nat, +t: List<&2, Nat>, +identity: List<&2, Nat>,
    +member: Nat, +actual: List<&2, Nat>, +rest: List<&2, Spec.Observation>,
    tail_proof: {Numerical.complete(t, identity, rest) == True{} : Bool} -> Spec.Complete(t, identity, rest),
    proofs: {Nat.is_eq(member, h) == True{} : Bool} &
      {Bool.and(Numerical.same(actual, identity), Numerical.complete(t, identity, rest)) == True{} : Bool})
  -> Spec.Complete(h <> t, identity, Spec.Observed{member, actual} <> rest):
  (member_ok, remaining) = proofs
  complete_tail(h, t, identity, member, actual, rest, member_ok, tail_proof,
    and_true(Numerical.same(actual, identity), Numerical.complete(t, identity, rest), remaining))

def Laws.complete_sound(expected, identity, rows, accepted):
  match expected rows:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} h <> t:
      false_true(accepted)
    case h <> t Nil{}:
      false_true(accepted)
    case h <> t Spec.Observed{member, actual} <> rest:
      complete_join(h, t, identity, member, actual, rest,
        tail_ok => Laws.complete_sound(t, identity, rest, tail_ok),
        and_true(Nat.is_eq(member, h),
          Bool.and(Numerical.same(actual, identity), Numerical.complete(t, identity, rest)), accepted))
    case h <> t Spec.Missing{} <> rest:
      false_true(accepted)
    case h <> t Spec.Unsupported{} <> rest:
      false_true(accepted)
    case h <> t Spec.Cancelled{} <> rest:
      false_true(accepted)
    case h <> t Spec.Invalid{} <> rest:
      false_true(accepted)

def Laws.observed_progress(expected, identity):
  match expected:
    case Nil{}:
      {==}
    case h <> t:
      %Equal.sym(Bool, Nat.is_eq(h, h), True{}, nat_eq(h)) : {Bool.and(_, Bool.and(Numerical.same(identity, identity), Numerical.complete(t, identity, Numerical.observed(t, identity)))) == True{} : Bool}
      %Equal.sym(Bool, Numerical.same(identity, identity), True{}, Laws.identity_reflexive(identity)) : {Bool.and(_, Numerical.complete(t, identity, Numerical.observed(t, identity))) == True{} : Bool}
      Laws.observed_progress(t, identity)

def Laws.missing_rejected(member, expected, identity, rest):
  {==}

def Laws.unsupported_rejected(member, expected, identity, rest):
  {==}

def Laws.cancelled_rejected(member, expected, identity, rest):
  {==}

def le_sound(+a: Nat, +b: Nat, p: {Nat.is_le(a, b) == True{} : Bool}) -> Spec.Le(a, b):
  match a b:
    case 0n 0n:
      Unit{}
    case 0n 1n+q:
      Unit{}
    case 1n+r 0n:
      false_true(p)
    case 1n+r 1n+q:
      le_sound(r, q, p)

def le_reflexive(+n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_reflexive(p)

def bounded_error_join(+candidate: Nat, +reference: Nat, +error: Nat,
    proofs: {Nat.is_le(candidate, Nat.add(error, reference)) == True{} : Bool} &
      {Nat.is_le(reference, Nat.add(error, candidate)) == True{} : Bool})
  -> Spec.Approximate(candidate, reference, error):
  (upper, lower) = proofs
  (le_sound(candidate, Nat.add(error, reference), upper),
    le_sound(reference, Nat.add(error, candidate), lower))

def Laws.bounded_error_sound(candidate, reference, error, accepted):
  bounded_error_join(candidate, reference, error,
    and_true(Nat.is_le(candidate, Nat.add(error, reference)),
      Nat.is_le(reference, Nat.add(error, candidate)), accepted))

def Laws.exact_error_progress(value):
  %Equal.sym(Bool, Nat.is_le(value, value), True{}, le_reflexive(value)) :
    {Bool.and(_, Nat.is_le(value, value)) == True{} : Bool}
  le_reflexive(value)
