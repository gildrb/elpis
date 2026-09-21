# Abstract specification of native.cu's fixed block8 scalar/tensor boundary.
# This is NOT a proof of C/NVRTC lowering, Bool discriminants, CUDA execution,
# actual pointer storage, stream lifetime, or that the admitted leaf returned.
# native_build.py must still establish its seven-u32/four-Term binding, Term=64,
# u32=32 and bounded Nat-immediate execution (48 bits). Tensor words are NOT Nat.
import Base

type Slot is Data:
  S0{}
  S1{}
  S2{}
  S3{}
  S4{}
  S5{}
  S6{}
  S7{}

def index(slot: Slot) -> Nat:
  match slot:
    case S0{}:
      0n
    case S1{}:
      1n
    case S2{}:
      2n
    case S3{}:
      3n
    case S4{}:
      4n
    case S5{}:
      5n
    case S6{}:
      6n
    case S7{}:
      7n

def at(n: Nat, xs: List<&2, Nat>) -> Maybe<&2, Nat>:
  match n xs:
    case 0n Nil{}:
      None{}
    case 0n h <> t:
      Some{h}
    case 1n+p Nil{}:
      None{}
    case 1n+p h <> t:
      at(p, t)

def slot_at(n: Nat, xs: List<&2, Slot>) -> Maybe<&2, Slot>:
  match n xs:
    case 0n Nil{}:
      None{}
    case 0n h <> t:
      Some{h}
    case 1n+p Nil{}:
      None{}
    case 1n+p h <> t:
      slot_at(p, t)

def decode(n: Nat) -> Maybe<&2, Slot>:
  slot_at(n, [S0{}, S1{}, S2{}, S3{}, S4{}, S5{}, S6{}, S7{}])

def inputs(count: Nat, +start: Nat) -> List<&2, Nat>:
  match count:
    case 0n:
      Nil{}
    case 1n+p:
      start <> inputs(p, 1n+start)

# Four flat Term outputs, in native.cu words[0..3] order. Counts arise from
# the materialized anchor plus accepted inputs, not from an emitted bonus.
def words(+accepted: Slot) -> List<&2, Nat>:
  +a = index(accepted)
  [a, List.length(&2, Nat, 0n <> inputs(a, 1n)), a,
    List.length(&2, Nat, inputs(1n+a, 0n))]

type Source is Data:
  Input{slot: Nat}
  TargetBonus{slot: Nat}
  ZeroFill{}

# The whole tensor is transported, including rejected/padding cells. Only
# slots 0..accepted of this output are semantically emitted. Source tags keep
# a bonus distinct from a materialized input even when their signed IDs agree.
def source_at(n: Nat, xs: List<&2, Source>) -> Maybe<&2, Source>:
  match n xs:
    case 0n Nil{}:
      None{}
    case 0n h <> t:
      Some{h}
    case 1n+p Nil{}:
      None{}
    case 1n+p h <> t:
      source_at(p, t)

def replace(n: Nat, value: Source, xs: List<&2, Source>) -> List<&2, Source>:
  match n xs:
    case 0n Nil{}:
      Nil{}
    case 0n h <> t:
      value <> t
    case 1n+p Nil{}:
      Nil{}
    case 1n+p h <> t:
      h <> replace(p, value, t)

def transport(+accepted: Slot) -> List<&2, Source>:
  replace(index(accepted), TargetBonus{index(accepted)},
    [Input{1n}, Input{2n}, Input{3n}, Input{4n}, Input{5n},
      Input{6n}, Input{7n}, ZeroFill{}])

def committed(accepted: Slot) -> List<&2, Nat>:
  0n <> inputs(index(accepted), 1n)

# Two address units cannot be accidentally equated by a theorem. prefix_stride
# in native.py/native.cu is ELEMENTS (including stride 0). KVarNOffsets and
# packed tile offsets are BYTES; fp16 parameter pointers separately divide by 2.
type ElementOffset is Data:
  Elements{value: Nat}
type ByteOffset is Data:
  Bytes{value: Nat}
type Width is Data:
  I32{}
  I64{}

def bits(width: Width) -> Nat:
  match width:
    case I32{}:
      32n
    case I64{}:
      64n

def bytes(width: Width) -> Nat:
  match width:
    case I32{}:
      4n
    case I64{}:
      8n

def prefix_element(row: Nat, stride: Nat) -> ElementOffset:
  Elements{Nat.mul(row, stride)}

def element_bytes(width: Width, offset: ElementOffset) -> ByteOffset:
  Elements{value} = offset
  Bytes{Nat.mul(value, bytes(width))}

def packed_bytes(base: ByteOffset, offset: ByteOffset) -> ByteOffset:
  Bytes{b} = base
  Bytes{o} = offset
  Bytes{Nat.add(b, o)}

# Little-endian two's-complement bits cover EVERY signed int32/int64 value.
# No signed tensor is coerced to Nat. Malformed representations, absent and
# cancelled work are distinct from zero. Width validation is not pointer truth.
type Raw is Data:
  Missing{}
  Cancelled{}
  Bits{value: List<&2, Bool>}
type Transfer is Data:
  Absent{}
  Aborted{}
  Malformed{}
  Value{value: List<&2, Bool>}

def last(xs: List<&2, Bool>, value: Bool) -> Bool:
  match xs:
    case Nil{}:
      value
    case h <> t:
      last(t, h)

def sign(xs: List<&2, Bool>) -> Bool:
  last(xs, False{})

def take(n: Nat, xs: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case h <> t:
          h <> take(p, t)

def resize(+n: Nat, +xs: List<&2, Bool>) -> List<&2, Bool>:
  take(n, List.append(&2, Bool, xs, List.replicate(Bool, n, sign(xs))))

def valid_width(width: Width, +xs: List<&2, Bool>) -> Bool:
  Nat.is_eq(List.length(&2, Bool, xs), bits(width))

def transfer_valid(ok: Bool, dest: Width, value: List<&2, Bool>) -> Transfer:
  match ok:
    case False{}:
      Malformed{}
    case True{}:
      Value{resize(bits(dest), value)}

def transfer(source: Width, dest: Width, raw: Raw) -> Transfer:
  match raw:
    case Missing{}:
      Absent{}
    case Cancelled{}:
      Aborted{}
    case Bits{+value}:
      transfer_valid(valid_width(source, value), dest, value)

# Succession in the finite binary ring: overflow discards the carry. Reference
# semantics flips an initial run of ones, independently of the ripple adder.
def bump(xs: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case False{} <> t:
      True{} <> t
    case True{} <> t:
      False{} <> bump(t)

def advance(delta: Nat, xs: List<&2, Bool>) -> List<&2, Bool>:
  match delta:
    case 0n:
      xs
    case 1n+p:
      advance(p, bump(xs))

# Native int32 prefix wraps in 32 bits BEFORE sign extension to an int64
# destination. A wide prefix wraps in 64 bits; output int32 keeps low32.
def sequence_valid(ok: Bool, dest: Width, delta: Nat, value: List<&2, Bool>) -> Transfer:
  match ok:
    case False{}:
      Malformed{}
    case True{}:
      Value{resize(bits(dest), advance(delta, value))}

def sequence(source: Width, dest: Width, delta: Nat, raw: Raw) -> Transfer:
  match raw:
    case Missing{}:
      Absent{}
    case Cancelled{}:
      Aborted{}
    case Bits{+value}:
      sequence_valid(valid_width(source, value), dest, delta, value)

# unsigned is a mathematical interpretation, NOT a compiled 64-bit Nat API.
# Original emitted Nat supports only 48 immediate bits. Do not execute this
# interpretation on arbitrary int64 words; executable transport stays Boolean.
def unsigned(xs: List<&2, Bool>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case False{} <> t:
      Nat.double(unsigned(t))
    case True{} <> t:
      1n+Nat.double(unsigned(t))

# A constructive no-carry witness, not an assumed native overflow flag.
def CarryRoom(xs: List<&2, Bool>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case False{} <> t:
      Unit
    case True{} <> t:
      CarryRoom(t)

# Every intermediate and final sign is nonnegative, and each increment has
# room. This is the exact separate logical-length contract. Native launch does
# NOT check it. It must be supplied from actual prefix values/length bounds.
def SafeAdvance(delta: Nat, +xs: List<&2, Bool>) -> Type:
  match delta:
    case 0n:
      {sign(xs) == False{} : Bool}
    case 1n+p:
      {sign(xs) == False{} : Bool} & CarryRoom(xs) & SafeAdvance(p, bump(xs))

# Scalar representability is expressed without normalizing 2^64 in Nat.
# Fits(w,n) means n has a w-bit unsigned encoding. Pointer arithmetic uses
# w=64; signed nonnegative lengths use w=31 or 63; Bend immediate w=48.
def Fits(width: Nat, value: Nat) -> Bool:
  match width:
    case 0n:
      Nat.is_eq(value, 0n)
    case 1n+p:
      Fits(p, Nat.div(value, 2n))

# Mathematical host preconditions. The real host uses arbitrary-precision Python
# integers for these predicates; compiling them over unrestricted Nat inputs is
# NOT a replacement (original Bend's Nat immediate range is smaller than u64).
# Extent is exclusive; native.py deliberately rejects end == 2^64 as well.
def span_safe(+start: Nat, extent: Nat) -> Bool:
  Bool.and(Nat.is_lt(0n, start), Fits(64n, Nat.add(start, extent)))

def block_safe(+width: Width, +row: Nat, +batch: Nat, start: Nat) -> Bool:
  Bool.and(Nat.is_lt(row, batch),
    span_safe(start, Nat.mul(Nat.mul(batch, 8n), bytes(width))))

# Prefix extent contains strided holes; stride0 still owns one element.
def prefix_extent(batch: Nat, +stride: Nat) -> Nat:
  match batch:
    case 0n:
      0n
    case 1n+p:
      1n+Nat.mul(p, stride)

def prefix_safe(width: Width, +row: Nat, +batch: Nat, +stride: Nat,
    start: Nat) -> Bool:
  Bool.and(Nat.is_lt(row, batch), Bool.and(Fits(64n, stride),
    span_safe(start, Nat.mul(prefix_extent(batch, stride), bytes(width)))))

# ceil(batch/128) <= signed31 maximum, without constructing that maximum.
def launch_geometry(batch: Nat) -> Bool:
  Fits(31n, Nat.div(Nat.add(batch, 127n), 128n))

# These seven pairs are native.cu m0..m6. Input slot0 is the anchor, never
# compared; target slot7 is read only when all seven comparisons succeeded.
type ComparisonPair is Data:
  ComparisonPair{candidate: Nat, target: Nat}

def pair_at(n: Nat, xs: List<&2, ComparisonPair>) -> Maybe<&2, ComparisonPair>:
  match n xs:
    case 0n Nil{}:
      None{}
    case 0n h <> t:
      Some{h}
    case 1n+p Nil{}:
      None{}
    case 1n+p h <> t:
      pair_at(p, t)

def comparison(slot: Slot) -> Maybe<&2, ComparisonPair>:
  pair_at(index(slot), [ComparisonPair{1n, 0n}, ComparisonPair{2n, 1n},
    ComparisonPair{3n, 2n}, ComparisonPair{4n, 3n}, ComparisonPair{5n, 4n},
    ComparisonPair{6n, 5n}, ComparisonPair{7n, 6n}])

# These are explicit external observations, NOT invented runtime witnesses.
# native.py checks tensor metadata, uint64 stride/extents, launch geometry,
# output-vs-all disjointness and context. Cancellation/missing observations
# are preserved by the abstract boundary; they cannot authorize a launch.
type Check is Data:
  TensorKind{}
  DeviceLayout{}
  IntegerWidth{}
  Shape{}
  Contiguity{}
  OrdinaryView{}
  LaunchGeometry{}
  PrefixStride{}
  StorageExtent{}
  OutputDisjoint{}
  ContextIdentity{}
type Observation is Data:
  Unknown{check: Check}
  Failed{check: Check}
  Passed{check: Check}
  Stopped{}
type Admission is Data:
  Unobserved{check: Check}
  Rejected{check: Check}
  CancelLaunch{}
  Ready{}

# Caller supplies the COMPLETE native check sequence; Ready does not attest
# that observations came from actual tensors. Empty batch still has metadata
# checks, but native.py intentionally skips pointers/context/launch afterwards.
def admit(observations: List<&2, Observation>) -> Admission:
  match observations:
    case Nil{}:
      Ready{}
    case Unknown{check} <> rest:
      Unobserved{check}
    case Failed{check} <> rest:
      Rejected{check}
    case Stopped{} <> rest:
      CancelLaunch{}
    case Passed{check} <> rest:
      admit(rest)
