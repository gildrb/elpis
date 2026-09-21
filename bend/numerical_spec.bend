# Exact mathematical contracts, NOT replacements for NumPy binary64 replay.
# Sources: bench/numerical.py _compare/_replay_event/verify_report;
# patches/kvarn-candidate.patch, kvarn-pack-layout.patch; vendored Marlin A8.
# KVarN nearbyint is ties-even; A8 libdevice.round is ties-away from zero.
# Bit packing is exact relative to quantized codes; KV quantization is lossy.
# Compiler/Base, native floating instructions, metadata fidelity and producer
# authenticity remain external. No native arithmetic refinement is asserted.
import Base

type Mode is Data:
  TiesEven{}
  TiesAway{}

type Rounded is Data:
  Rounded{negative: Bool, magnitude: Nat}

type Class is Data:
  Finite{}
  PositiveInfinity{}
  NegativeInfinity{}
  NotANumber{}
  InvalidEncoding{}

type Category is Data:
  ExactRepresentation{}
  Approximation{}

type Observation is Data:
  Observed{member: Nat, identity: List<&2, Nat>}
  Missing{}
  Unsupported{}
  Cancelled{}
  Invalid{}

# Identity is the canonical sequence of ALL reference identity fields, not
# a rounded metric: checkpoint/derived weights, tokenizer/template/special
# tokens, draft vocabulary, cache recipe, numerics and sampling transforms.
# Bytes/hashes must be decoded injectively and authenticated by the host.
# Equal canonical lists prove consistency, NOT authenticity or hash security.

def Truth(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

# Structural integer order, independent of the executable comparison.
def Le(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n 0n:
      Unit
    case 0n 1n+q:
      Unit
    case 1n+p 0n:
      Empty
    case 1n+p 1n+q:
      Le(p, q)

# Common-frame dyadics represent (integer - offset) / 2^exponent.
# Every finite dyadic family can use a shared offset/exponent, including
# negative logits. The host must supply that exact common-frame embedding;
# infinity/NaN have no such embedding. No rounded subtraction is used here.
def Enclosed(value: Nat, lower: Nat, upper: Nat) -> Type:
  Le(lower, value) & Le(value, upper)

def Winner(value: Nat, competitors: List<&2, Nat>) -> Type:
  match competitors:
    case Nil{}:
      Unit
    case h <> t:
      Le(1n+h, value) & Winner(value, t)

# Per-competitor upper bounds. Missing/extra bounds make this uninhabited.
def Margin(lower: Nat, competitors: List<&2, Nat>, uppers: List<&2, Nat>) -> Type:
  match competitors uppers:
    case Nil{} Nil{}:
      Unit
    case Nil{} h <> t:
      Empty
    case h <> t Nil{}:
      Empty
    case h <> t u <> us:
      (Le(h, u) & Le(1n+u, lower)) & Margin(lower, t, us)

# Exact rational division witness required to interpret q,r as n/d.
# d=0 is not an admissible denominator. Implementations may not silently
# use Base's totalized division-by-zero as numerical evidence.
def Division(n: Nat, d: Nat, q: Nat, r: Nat) -> Type:
  Le(1n, d) & ({n == Nat.add(Nat.mul(q, d), r) : Nat} & Le(1n+r, d))

def odd(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      Bool.not(odd(p))

def nearest_even(parity: Bool, q: Nat) -> Nat:
  match parity:
    case False{}:
      q
    case True{}:
      1n+q

def nearest_tie(rounding_mode: Mode, +q: Nat) -> Nat:
  match rounding_mode:
    case TiesAway{}:
      1n+q
    case TiesEven{}:
      nearest_even(odd(q), q)

def nearest(mode: Mode, +q: Nat, twice_remainder: Cmp) -> Nat:
  match twice_remainder:
    case LT{}:
      q
    case GT{}:
      1n+q
    case EQ{}:
      nearest_tie(mode, q)

# Sign-magnitude rounding preserves the sign, including signed zero. Applying
# TiesAway to magnitude then restoring sign is away from zero for BOTH signs.
def rounding(mode: Mode, negative: Bool, q: Nat, r: Nat, d: Nat) -> Rounded:
  Rounded{negative, nearest(mode, q, Nat.cmp(Nat.double(r), d))}

def finite_class(negative: Bool, exponent: Cmp, fraction: Nat) -> Class:
  match negative exponent fraction:
    case sign LT{} mantissa:
      Finite{}
    case sign GT{} mantissa:
      InvalidEncoding{}
    case False{} EQ{} 0n:
      PositiveInfinity{}
    case True{} EQ{} 0n:
      NegativeInfinity{}
    case sign EQ{} 1n+p:
      NotANumber{}

# max_exponent is the all-ones field of a separately bound IEEE format.
# Fraction width and sign/exponent extraction are additional encoding facts.
def classify(negative: Bool, exponent: Nat, fraction: Nat, max_exponent: Nat) -> Class:
  finite_class(negative, Nat.cmp(exponent, max_exponent), fraction)

def IsFinite(value: Class) -> Type:
  match value:
    case Finite{}:
      Unit
    case PositiveInfinity{}:
      Empty
    case NegativeInfinity{}:
      Empty
    case NotANumber{}:
      Empty
    case InvalidEncoding{}:
      Empty

# Independent positional bit interpretation. LSB first, arbitrary width.
def value(bits: List<&2, Bool>) -> Nat:
  match bits:
    case Nil{}:
      0n
    case False{} <> rest:
      +high = value(rest)
      Nat.add(high, high)
    case True{} <> rest:
      +high = value(rest)
      1n+Nat.add(high, high)

def power2(width: Nat) -> Nat:
  match width:
    case 0n:
      1n
    case 1n+p:
      Nat.double(power2(p))

def Packed(bits: List<&2, Bool>, code: Nat) -> Type:
  {code == value(bits) : Nat}

def SafeCode(width: Nat, code: Nat) -> Type:
  Le(1n+code, power2(width))

# Exact representation and approximate arithmetic are different obligations.
# Approximate residual budgets here are exact integer/dyadic certificates;
# they neither implement nor change existing float64 atol/rtol/RMSE gates.
def Representation(bits: List<&2, Bool>, code: Nat) -> Type:
  Packed(bits, code) & SafeCode(List.length(&2, Bool, bits), code)

def Approximate(candidate: Nat, reference: Nat, error: Nat) -> Type:
  Le(candidate, Nat.add(error, reference)) & Le(reference, Nat.add(error, candidate))

# Order, multiplicity and absence are explicit. Unknown/unsupported/cancelled
# records never count as observed, even when expected identity is unchanged.
def Complete(expected: List<&2, Nat>, +identity: List<&2, Nat>, rows: List<&2, Observation>) -> Type:
  match expected rows:
    case Nil{} Nil{}:
      Unit
    case Nil{} h <> t:
      Empty
    case h <> t Nil{}:
      Empty
    case h <> t Observed{member, actual} <> rest:
      ({member == h : Nat} & {actual == identity : List<&2, Nat>}) & Complete(t, identity, rest)
    case h <> t Missing{} <> rest:
      Empty
    case h <> t Unsupported{} <> rest:
      Empty
    case h <> t Cancelled{} <> rest:
      Empty
    case h <> t Invalid{} <> rest:
      Empty

# Required full-model simulation relations, deliberately NOT laws/axioms.
# State must include KV, recurrent Mamba/GDN/conv state, committed prefix,
# stopping/cancellation and RNG/scheduler state. Callers supply semantics.
# State witnesses below are erased, not copied runtime values. S remains Type,
# so these obligations admit affine state and handles as well as Data.
def Initialization(-S: Type, related: @-x: S -> @-y: S -> Type, -r: S, -c: S) -> Type:
  related(r, c)

def CommittedStep(-S: Type, related: @-x: S -> @-y: S -> Type,
    -reference: S -> Nat -> S, -candidate: S -> Nat -> S,
    -r: S, -c: S, -token: Nat) -> Type:
  related(r, c) -> related(reference(r, token), candidate(c, token))

def OutputConsistency(-S: Type, related: @-x: S -> @-y: S -> Type,
    -output: S -> List<&2, Nat>, -r: S, -c: S) -> Type:
  related(r, c) -> {output(r) == output(c) : List<&2, Nat>}

# A finite natural rank must decrease on EACH silent internal transition;
# this is a requirement, not a claim about native scheduler fairness.
def InternalProgress(before: Nat, after: Nat) -> Type:
  Le(1n+after, before)

def total(masses: List<&2, Nat>) -> Nat:
  match masses:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(h, total(t))

def SameMass(+rd: Nat, +cd: Nat, reference: List<&2, Nat>, candidate: List<&2, Nat>) -> Type:
  match reference candidate:
    case Nil{} Nil{}:
      Unit
    case Nil{} h <> t:
      Empty
    case h <> t Nil{}:
      Empty
    case r <> rs c <> cs:
      {Nat.mul(r, cd) == Nat.mul(c, rd) : Nat} & SameMass(rd, cd, rs, cs)

# Same declared exhaustive support, positive denominators, normalized masses,
# equal per-outcome probabilities. NOT equality of one seed or one output.
# draw_relation must specify native RNG state, draw consumption/order, and
# finite randomized execution correspondence; rounded sampler probabilities
# need their own bit semantics. Greedy native paths do not support this domain.
def DistributionRefinement(-draw_relation: Type, +rd: Nat, +cd: Nat,
    +reference: List<&2, Nat>, +candidate: List<&2, Nat>) -> Type:
  draw_relation & ((Le(1n, rd) & Le(1n, cd)) &
    (({total(reference) == rd : Nat} & {total(candidate) == cd : Nat}) &
      SameMass(rd, cd, reference, candidate)))

# Termination and cancellation must also be related observations, not omitted
# by proving only successful token-producing transitions.
def TerminationConsistency(-S: Type, related: @-x: S -> @-y: S -> Type,
    -stopped: S -> Bool, -r: S, -c: S) -> Type:
  related(r, c) -> {stopped(r) == stopped(c) : Bool}

def CancellationConsistency(-S: Type, related: @-x: S -> @-y: S -> Type,
    -cancelled: S -> Bool, -r: S, -c: S) -> Type:
  related(r, c) -> {cancelled(r) == cancelled(c) : Bool}
