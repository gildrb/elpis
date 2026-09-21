# Pure executable arithmetic and coverage checks. No native invocation.
# Production mapping is a CONTRACT ONLY: no existing host gate is replaced.
# _compare: retain same shape/dtype/finite checks and binary64 tolerances.
# _replay_event: native/prefill RMSE <= 2^-11; flash rtol=2^-7+2^-8,
# RMSE <= 0.0005 and max_abs <= 0.02; default atol=2^-10, rtol=2^-7.
# Dead/padded rows remain zero, graph gather bit-exact, commit metadata exact.
# verify_report: exact 576-event fixture plan and reference identity binding.
# serve.numerical_gate: attention/storage/embedding/commit/sampler coverage;
# A8 additionally needs marlin_a8, which the current replay cannot provide.
# Prime scorers, all replay gates, tolerances and graders stay unchanged.
import Base
import ./numerical_spec.bend as Spec

def odd(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match p:
        case 0n:
          True{}
        case 1n+q:
          odd(q)

def increment(mode: Spec.Mode, parity: Bool) -> Bool:
  match mode:
    case Spec.TiesEven{}:
      parity
    case Spec.TiesAway{}:
      True{}

def bump(bit: Bool, q: Nat) -> Nat:
  match bit:
    case False{}:
      q
    case True{}:
      1n+q

def nearest(mode: Spec.Mode, +q: Nat, position: Cmp) -> Nat:
  match position:
    case LT{}:
      q
    case EQ{}:
      bump(increment(mode, odd(q)), q)
    case GT{}:
      1n+q

def round_parts(mode: Spec.Mode, negative: Bool, q: Nat, r: Nat, d: Nat) -> Spec.Rounded:
  Spec.Rounded{negative, nearest(mode, q, Nat.cmp(Nat.double(r), d))}

def round_divided(mode: Spec.Mode, negative: Bool, denominator: Nat, qr: Nat & Nat) -> Maybe<&2, Spec.Rounded>:
  (q, r) = qr
  Some{round_parts(mode, negative, q, r, denominator)}

# The independently typed Division premise is needed when interpreting these
# quotient/remainder operations as rational rounding. Zero fails explicitly.
def round(mode: Spec.Mode, negative: Bool, magnitude: Nat, denominator: Nat) -> Maybe<&2, Spec.Rounded>:
  match denominator:
    case 0n:
      None{}
    case 1n++d:
      round_divided(mode, negative, 1n+d, Nat.divmod(magnitude, 1n+d))

def exceptional(negative: Bool, fraction: Nat) -> Spec.Class:
  match negative fraction:
    case False{} 0n:
      Spec.PositiveInfinity{}
    case True{} 0n:
      Spec.NegativeInfinity{}
    case sign 1n+p:
      Spec.NotANumber{}

def classify_order(negative: Bool, order: Cmp, fraction: Nat) -> Spec.Class:
  match order:
    case LT{}:
      Spec.Finite{}
    case EQ{}:
      exceptional(negative, fraction)
    case GT{}:
      Spec.InvalidEncoding{}

def classify(negative: Bool, exponent: Nat, fraction: Nat, max_exponent: Nat) -> Spec.Class:
  classify_order(negative, Nat.cmp(exponent, max_exponent), fraction)

def finite(value: Spec.Class) -> Bool:
  match value:
    case Spec.Finite{}:
      True{}
    case Spec.PositiveInfinity{}:
      False{}
    case Spec.NegativeInfinity{}:
      False{}
    case Spec.NotANumber{}:
      False{}
    case Spec.InvalidEncoding{}:
      False{}

def pack(bits: List<&2, Bool>) -> Nat:
  match bits:
    case Nil{}:
      0n
    case bit <> rest:
      bump(bit, Nat.double(pack(rest)))

type Split is Data:
  Split{high: Nat, bit: Bool}

def split_step(pair: Split) -> Split:
  match pair:
    case Split{high, bit}:
      Split{1n+high, bit}

def split_high(pair: Split) -> Nat:
  match pair:
    case Split{high, bit}:
      high

def split_bit(pair: Split) -> Bool:
  match pair:
    case Split{high, bit}:
      bit

# Euclidean division by two, with explicit remainder bit.
def split(code: Nat) -> Split:
  match code:
    case 0n:
      Split{0n, False{}}
    case 1n+p:
      match p:
        case 0n:
          Split{0n, True{}}
        case 1n+q:
          split_step(split(q))

def prepend(bit: Bool, rest: Maybe<&2, List<&2, Bool>>) -> Maybe<&2, List<&2, Bool>>:
  match rest:
    case None{}:
      None{}
    case Some{bits}:
      Some{bit <> bits}

# No modulo truncation: a code exceeding the supplied width is rejected.
def unpack(width: Nat, code: Nat) -> Maybe<&2, List<&2, Bool>>:
  match width:
    case 0n:
      match code:
        case 0n:
          Some{Nil{}}
        case 1n+p:
          None{}
    case 1n+p:
      +qr = split(code)
      prepend(split_bit(qr), unpack(p, split_high(qr)))

def unpack_step(width: Nat, +pair: Split) -> Maybe<&2, List<&2, Bool>>:
  prepend(split_bit(pair), unpack(width, split_high(pair)))

def safe(width: Nat, code: Nat) -> Bool:
  Nat.is_lt(code, Spec.power2(width))

# Exact common-frame dyadic strict margin, not RMSE or token logprobs.
def separated(lower: Nat, upper: Nat) -> Bool:
  Nat.is_lt(upper, lower)

def same(+xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} h <> t:
      False{}
    case h <> t Nil{}:
      False{}
    case h <> t j <> rest:
      Bool.and(Nat.is_eq(h, j), same(t, rest))

def complete(expected: List<&2, Nat>, +identity: List<&2, Nat>, rows: List<&2, Spec.Observation>) -> Bool:
  match expected rows:
    case Nil{} Nil{}:
      True{}
    case Nil{} h <> t:
      False{}
    case h <> t Nil{}:
      False{}
    case h <> t Spec.Observed{member, actual} <> rest:
      Bool.and(Nat.is_eq(member, h), Bool.and(same(actual, identity), complete(t, identity, rest)))
    case h <> t Spec.Missing{} <> rest:
      False{}
    case h <> t Spec.Unsupported{} <> rest:
      False{}
    case h <> t Spec.Cancelled{} <> rest:
      False{}
    case h <> t Spec.Invalid{} <> rest:
      False{}

def observed(expected: List<&2, Nat>, +identity: List<&2, Nat>) -> List<&2, Spec.Observation>:
  match expected:
    case Nil{}:
      Nil{}
    case h <> t:
      Spec.Observed{h, identity} <> observed(t, identity)

# Exact common-frame residual certificate, independent of binary64 metrics.
def bounded_error(+candidate: Nat, +reference: Nat, +error: Nat) -> Bool:
  Bool.and(Nat.is_le(candidate, Nat.add(error, reference)),
    Nat.is_le(reference, Nat.add(error, candidate)))
