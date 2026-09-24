# Proof-only ordered expression/state model, never imported by RUNTIME.
# Expressions are free constructors, NOT an IEEE emulator or algebraic quotient.
# Equal terms preserve operand/cast/reduction nesting under the SAME native
# interpretation; no reassociation, exp identity or alpha telescoping is used.
import Base

def late_value(head256: Bool, rows32: Bool) -> Nat:
  match head256 rows32:
    case True{} True{}:
      1n
    case _ _:
      0n

def bit(index: Nat) -> Bool:
  Nat.is_ne(Nat.mod(index, 2n), 0n)

def row(+index: Nat) -> Nat:
  late_value(bit(index), bit(Nat.div(index, 2n)))

def Action(value: Nat) -> Type:
  match value:
    case 0n:
      Unit
    case 1n+p:
      match p:
        case 0n:
          Unit
        case 1n+q:
          Empty

def protocol() -> String:
  "QWEN_RUNTIME_CONTROL_V7\nFREE_MIRROR\n8\n0\n0\n0\n0\n1\n0\n1\n1\nSTATUS\n8\n0\n2\n0\n1\n0\n2\n0\n1\nMARLIN_EIGHT_STAGE\n8\n0\n0\n0\n0\n0\n0\n0\n1\nMARLIN_SCALE_REFRESH\n8\n1\n0\n1\n0\n1\n0\n1\n0\nPACKED_LATE_VALUE\n4\n0\n0\n0\n1\nPACKED_INVERSE_PARTNER\n4\n0\n0\n0\n1\nPACKED_FORWARD_PARTNER_STAGES\n4\n0\n0\n0\n3\nMARLIN_SELECTED_SHARED_BYTES\n1\n43008\nEND_QWEN_RUNTIME_CONTROL"

# identity names one immutable read snapshot, including allocation/generation,
# query/metadata and all read buffers. It does NOT assert native lease ownership.
# Separate page/head/logical/block/query/split identities prevent silent operand
# substitution or page/block/query partition permutation. Repeated IDs are legal.
# Both schedules receive exactly this same snapshot; a concurrent write/reuse
# would require a different snapshot and is OUTSIDE the theorem.
type Input is Data:
  Input{identity: Nat, page: Nat, head: Nat, logical: Nat, block: Nat,
    query_tile: Nat, split: Nat, dimension: Nat}

# Leaves designate the original tensor operands, including their lane layout.
# K/V addresses retain their own representation, token and channel identities:
# KC/KZ: halves+K_SCALE/2+d, halves+K_ZERO/2+d; KT: halves+K_TOKEN/2+tok;
# KB: Packed+base+d[:,None]*64+tok[None,:]//2;
# VC: halves+V_CHANNEL/2+d; VS/VZ: halves+V_SCALE/2+tok, halves+V_ZERO/2+tok;
# VB: Packed+base+V_PACKED+tok[:,None]*(D//4)+d[None,:]//4.
# RawK/RawV use the unchanged safe_slot/head/token/channel addresses. These
# identities do NOT prove pointer arithmetic, bounds, initialization or aliasing.
type Operand is Data:
  KChannel{}
  KZero{}
  KToken{}
  KByte{}
  VChannel{}
  VScale{}
  VZero{}
  VByte{}
  RawKey{}
  RawValue{}
  Token{}
  Channel{}
  Query{}
  RotatedQuery{}
  Scale{}
  Normalize{}
  Valid{}
  UseRaw{}
  PageOK{}
  RawOK{}
  Written{}
  RowReal{}

type Expr is Data:
  Initial{identity: Nat}
  Zero{}
  One{}
  Number{value: Nat}
  NegInfinity{}
  Ref{input: Input, operand: Operand}
  Load{input: Input, address: Operand, mask: Expr, other: Expr}
  F16{value: Expr}
  F32{value: Expr}
  I32{value: Expr}
  Row{value: Expr}
  Column{value: Expr}
  Add{left: Expr, right: Expr}
  Mul{left: Expr, right: Expr}
  Sub{left: Expr, right: Expr}
  Div{left: Expr, right: Expr}
  Mod{left: Expr, right: Expr}
  Shift{left: Expr, right: Expr}
  Bits{left: Expr, right: Expr}
  And{left: Expr, right: Expr}
  Not{value: Expr}
  Greater{left: Expr, right: Expr}
  Where{condition: Expr, yes: Expr, no: Expr}
  Dot{left: Expr, right: Expr}
  Maximum{left: Expr, right: Expr}
  RowMax{value: Expr}
  RowSum{value: Expr}
  AllSum{value: Expr}
  Exp{value: Expr}
  Log{value: Expr}
  InverseHadamard{input: Input, value: Expr}

def packed_selector(+input: Input) -> Expr:
  And{Ref{input, Valid{}}, Not{Column{Ref{input, UseRaw{}}}}}

def raw_selector(+input: Input) -> Expr:
  And{Column{Ref{input, UseRaw{}}}, Ref{input, Valid{}}}

def packed_guard(input: Input) -> Expr:
  Greater{AllSum{I32{packed_selector(input)}}, Zero{}}

def raw_guard(input: Input) -> Expr:
  Greater{AllSum{I32{raw_selector(input)}}, Zero{}}

def packed_keys(+input: Input) -> Expr:
  ks = {F32{Load{input, KChannel{}, Ref{input, PageOK{}}, Zero{}}} : Expr}
  kz = {F32{Load{input, KZero{}, Ref{input, PageOK{}}, Zero{}}} : Expr}
  kt = {F32{Load{input, KToken{}, Ref{input, PageOK{}}, Zero{}}} : Expr}
  kb = {I32{Load{input, KByte{}, Ref{input, PageOK{}}, Zero{}}} : Expr}
  code = {F32{Bits{Shift{kb, Mul{Mod{Row{Ref{input, Token{}}}, Number{2n}}, Number{4n}}}, Number{15n}}} : Expr}
  Mul{Add{Mul{code, Column{ks}}, Column{kz}}, Row{kt}}

# Keep all four ordered load/cast results, not just a schedule tag or V identity.
# The native vc,vs,vz,vbyte chain is copied verbatim, and its mathematical field
# order is fixed here; no theorem licenses reordering those four native loads.
type Values is Data:
  Values{channel: Expr, scale: Expr, zero: Expr, byte: Expr, dequantized: Expr}

def packed_values(+input: Input) -> Values:
  +vc = {F32{Load{input, VChannel{}, Ref{input, PageOK{}}, Zero{}}} : Expr}
  +vs = {F32{Load{input, VScale{}, Ref{input, PageOK{}}, Zero{}}} : Expr}
  +vz = {F32{Load{input, VZero{}, Ref{input, PageOK{}}, Zero{}}} : Expr}
  +vb = {I32{Load{input, VByte{}, Ref{input, PageOK{}}, Zero{}}} : Expr}
  code = {F32{Bits{Shift{vb, Mul{Mod{Row{Ref{input, Channel{}}}, Number{4n}}, Number{2n}}}, Number{3n}}} : Expr}
  Values{vc, vs, vz, vb, Mul{Add{Mul{code, Column{vs}}, Column{vz}}, Row{vc}}}

def dequantized(values: Values) -> Expr:
  match values:
    case Values{channel, scale, zero, byte, value}:
      value

type Softmax is Data:
  Softmax{scores: Expr, maximum: Expr, live: Expr, alpha: Expr, probability: Expr}

# maximum is the ENTERING maximum (post-raw for mixed blocks), never max_packed.
# The probability mask retains the source's left-associated live & valid & ~raw.
def packed_softmax(+input: Input, keys: Expr, +maximum: Expr) -> Softmax:
  +scores = {Where{packed_selector(input),
    Mul{Dot{F16{Ref{input, RotatedQuery{}}}, F16{keys}}, Ref{input, Scale{}}}, NegInfinity{}} : Expr}
  +next = {Maximum{maximum, RowMax{scores}} : Expr}
  +live = {Greater{next, NegInfinity{}} : Expr}
  alpha = {Where{live, Exp{Sub{maximum, next}}, Zero{}} : Expr}
  probability = {Where{And{And{Column{live}, Ref{input, Valid{}}}, Not{Column{Ref{input, UseRaw{}}}}},
    Exp{Sub{scores, Column{next}}}, Zero{}} : Expr}
  Softmax{scores, next, live, alpha, probability}

def scores(softmax: Softmax) -> Expr:
  match softmax:
    case Softmax{scores, maximum, live, alpha, probability}:
      scores

def next_maximum(softmax: Softmax) -> Expr:
  match softmax:
    case Softmax{scores, maximum, live, alpha, probability}:
      maximum

def live(softmax: Softmax) -> Expr:
  match softmax:
    case Softmax{scores, maximum, live, alpha, probability}:
      live

def alpha(softmax: Softmax) -> Expr:
  match softmax:
    case Softmax{scores, maximum, live, alpha, probability}:
      alpha

def probability(softmax: Softmax) -> Expr:
  match softmax:
    case Softmax{scores, maximum, live, alpha, probability}:
      probability

# The temporary fields are retained, so commutation compares the complete state,
# not only the final accumulator. Masks/snapshot live in the immutable Input.
# status is an arbitrary sticky entering value: neither crossed operation writes
# it. Unchanged native atomic_or calls occur BEFORE these transitions.
type State is Data:
  State{keys: Expr, values: Values, softmax: Softmax, maximum: Expr,
    denominator: Expr, raw: Expr, rotated: Expr, status: Expr}

def prepare_keys(input: Input, state: State) -> State:
  match state:
    case State{keys, values, softmax, maximum, denominator, raw, rotated, status}:
      State{packed_keys(input), values, softmax, maximum, denominator, raw, rotated, status}

def load_value(input: Input, state: State) -> State:
  match state:
    case State{keys, values, softmax, maximum, denominator, raw, rotated, status}:
      State{keys, packed_values(input), softmax, maximum, denominator, raw, rotated, status}

def score_softmax(input: Input, state: State) -> State:
  match state:
    case State{+keys, values, softmax, +maximum, denominator, raw, rotated, status}:
      State{keys, values, packed_softmax(input, keys, maximum), maximum, denominator, raw, rotated, status}

# Same PV, raw rescale, denominator and maximum assignments in both schedules.
# Every old accumulator remains the LEFT operand of its original ordered term.
def packed_update(state: State) -> State:
  match state:
    case State{keys, +values, Softmax{+scores, +next, +live, +alpha, +probability}, maximum, denominator, raw, rotated, status}:
      State{keys, values, Softmax{scores, next, live, alpha, probability}, next,
        Add{Mul{denominator, alpha}, RowSum{probability}},
        Mul{raw, Column{alpha}},
        Add{Mul{rotated, Column{alpha}}, Dot{F16{probability}, F16{dequantized(values)}}}, status}

def early_packed(+input: Input, state: State) -> State:
  packed_update(score_softmax(input, load_value(input, prepare_keys(input, state))))

def late_packed(+input: Input, state: State) -> State:
  packed_update(load_value(input, score_softmax(input, prepare_keys(input, state))))

# Raw remains a distinct, FIRST pass. It rescales rotated even on a row whose
# raw probabilities are zero. We do not fuse the two passes or their alphas.
def raw_step(+input: Input, state: State) -> State:
  match state:
    case State{keys, values, softmax, +maximum, denominator, raw, rotated, status}:
      +raw_cols = {And{Ref{input, RawOK{}}, Ref{input, Written{}}} : Expr}
      rk = {F16{Load{input, RawKey{}, Row{raw_cols}, Zero{}}} : Expr}
      rv = {F16{Load{input, RawValue{}, Column{raw_cols}, Zero{}}} : Expr}
      +scores = {Where{raw_selector(input),
        Mul{Dot{F16{Ref{input, Query{}}}, rk}, Ref{input, Scale{}}}, NegInfinity{}} : Expr}
      +next = {Maximum{maximum, RowMax{scores}} : Expr}
      +live = {Greater{next, NegInfinity{}} : Expr}
      +alpha = {Where{live, Exp{Sub{maximum, next}}, Zero{}} : Expr}
      +probability = {Where{And{Column{live}, raw_selector(input)},
        Exp{Sub{scores, Column{next}}}, Zero{}} : Expr}
      State{keys, values, softmax, next,
        Add{Mul{denominator, alpha}, RowSum{probability}},
        Add{Mul{raw, Column{alpha}}, Dot{F16{probability}, rv}},
        Mul{rotated, Column{alpha}}, status}

def raw_if(enabled: Bool, input: Input, state: State) -> State:
  match enabled:
    case False{}:
      state
    case True{}:
      raw_step(input, state)

def reference_packed_if(enabled: Bool, input: Input, state: State) -> State:
  match enabled:
    case False{}:
      state
    case True{}:
      early_packed(input, state)

# Native must refine raw_any/packed_any to the exact guard expressions above.
# They are arbitrary observations here: all four combinations, including a
# wholly inactive block, are covered. False really SKIPS the entire pass; it is
# never replaced by a zero-probability dot over potentially uninitialized bytes.
type Block is Data:
  Block{input: Input, raw_any: Bool, packed_any: Bool}

def reference_block(block: Block, state: State) -> State:
  match block:
    case Block{+input, raw_any, packed_any}:
      reference_packed_if(packed_any, input, raw_if(raw_any, input, state))

# Ordered descriptors retain page/start order, partial tails, repeats, split
# membership and q_base identity. No sorting, padding, fusion or repartitioning.
def reference_run(blocks: List<&2, Block>, state: State) -> State:
  match blocks:
    case Nil{}:
      state
    case block <> rest:
      reference_run(rest, reference_block(block, state))

# Unchanged postprocessing is a congruence boundary, not a proof of Hadamard or
# the native reducer. InverseHadamard denotes the SAME ordered butterfly loop.
# Native Partial/Lse stores retain row_real (not row_ok) and the same addresses.
type Stored is Data:
  Stored{input: Input, mask: Expr, partial: Expr, lse: Expr, status: Expr}

def finish(+input: Input, state: State) -> Stored:
  match state:
    case State{keys, values, softmax, maximum, +denominator, raw, rotated, status}:
      numerator = {Add{raw, Mul{InverseHadamard{input, rotated}, Ref{input, Normalize{}}}} : Expr}
      +nonempty = {Greater{denominator, Zero{}} : Expr}
      +safe = {Where{nonempty, denominator, One{}} : Expr}
      Stored{input, Ref{input, RowReal{}}, Div{numerator, Column{safe}},
        Where{nonempty, Add{maximum, Log{safe}}, NegInfinity{}}, status}

# Each partition explicitly provides its own entering state. This includes the
# original fresh query/split reset; no preceding partition's state is inherited.
type Partition is Data:
  Partition{input: Input, blocks: List<&2, Block>, initial: State}

def reference_outputs(partitions: List<&2, Partition>) -> List<&2, Stored>:
  match partitions:
    case Nil{}:
      Nil{}
    case Partition{input, blocks, initial} <> rest:
      finish(input, reference_run(blocks, initial)) <> reference_outputs(rest)

type Reduced is Data:
  Reduced{ordered_partials: List<&2, Stored>}

# Native obligations: stable initialized read snapshots and truthful masks;
# no independent writer, repacker, preview publication or page/slot reuse before
# GPU completion; Status/Partial/Lse must not alias live read operands. Read-read
# K/V overlap is permitted. Leases/refcounts in the ownership MODEL do not prove
# native leases exist. Retain raw slots and all Q/Table/metadata/packed lifetimes.
# Native integer/pointer refinement, masked-load/branch behavior, atomics,
# allocation/output ownership, launch order, same FMA/dot/reduction/exp/log/cast
# semantics and rounding/fusion, source/patch application, compiler and hardware
# correctness are external. No NaN-payload, signed-zero, speed or GPU claim.
