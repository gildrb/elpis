# Proof-only model of the selected 32x256 transport, not a generic power-of-two
# or compiler theorem. Expr and Stored are the existing free constructors.
import Base
import ./attention_schedule_spec.bend as Attention
import ./numerical_spec.bend as Order

# Independent policy specification, not an alias of either production policy.
def inverse_partner(head256: Bool, rows32: Bool) -> Nat:
  match head256 rows32:
    case True{} True{}:
      1n
    case _ _:
      0n

def bit(index: Nat) -> Bool:
  Nat.is_ne(Nat.mod(index, 2n), 0n)

def row(+index: Nat) -> Nat:
  inverse_partner(bit(index), bit(Nat.div(index, 2n)))

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

# Original d XOR (1 << stage), and d AND (1 << stage), independently
# interpreted as LSB-first Boolean vectors. No reshape helper appears here.
def bits(width: Nat, +value: Nat) -> List<&2, Bool>:
  match width:
    case 0n:
      Nil{}
    case 1n+p:
      bit(value) <> bits(p, Nat.div(value, 2n))

def one_hot(width: Nat, +stage: Nat, +position: Nat) -> List<&2, Bool>:
  match width:
    case 0n:
      Nil{}
    case 1n+p:
      Nat.is_eq(stage, position) <> one_hot(p, stage, 1n+position)

def xor_bits(left: List<&2, Bool>, right: List<&2, Bool>) -> List<&2, Bool>:
  match left right:
    case a <> as b <> bs:
      Bool.xor(a, b) <> xor_bits(as, bs)
    case _ _:
      Nil{}

def and_bits(left: List<&2, Bool>, right: List<&2, Bool>) -> List<&2, Bool>:
  match left right:
    case a <> as b <> bs:
      Bool.and(a, b) <> and_bits(as, bs)
    case _ _:
      Nil{}

def reference_partner(stage: Nat, lane: Nat) -> Nat:
  Order.value(xor_bits(bits(8n, lane), one_hot(8n, stage, 0n)))

def reference_mask(stage: Nat, lane: Nat) -> Nat:
  Order.value(and_bits(bits(8n, lane), one_hot(8n, stage, 0n)))

def reference_low(stage: Nat, lane: Nat) -> Bool:
  Nat.is_eq(reference_mask(stage, lane), 0n)

# Inverse read-coordinate maps of:
# [ROWS,256] -> [ROWS,256/(2*s),2,s] -> [ROWS,256/(2*s),s,2]
# -> split(lo,hi), join(hi,lo) -> transpose back -> [ROWS,256].
# ROWS is universally carried and never participates in channel arithmetic.
type Coord is Data:
  Coord{row: Nat, group: Nat, high: Bool, offset: Nat}

type Transposed is Data:
  Transposed{row: Nat, group: Nat, offset: Nat, high: Bool}

def reshape(+stage: Nat, row: Nat, +lane: Nat) -> Coord:
  Coord{row, Nat.div(lane, Nat.double(Order.power2(stage))),
    bit(Nat.div(lane, Order.power2(stage))), Nat.mod(lane, Order.power2(stage))}

def flatten(stage: Nat, coordinate: Coord) -> Nat:
  match coordinate:
    case Coord{row, group, high, offset}:
      Nat.add(Nat.mul(Nat.add(Nat.double(group), Bool.pick(Nat, high, 1n, 0n)),
        Order.power2(stage)), offset)

def transpose(coordinate: Coord) -> Transposed:
  match coordinate:
    case Coord{row, group, high, offset}:
      Transposed{row, group, offset, high}

# Split has two source planes; reversed join selects hi for output plane0,
# lo for output plane1. Only this final axis changes.
def split_join(coordinate: Transposed) -> Transposed:
  match coordinate:
    case Transposed{row, group, offset, high}:
      Transposed{row, group, offset, Bool.not(high)}

def transpose_back(coordinate: Transposed) -> Coord:
  match coordinate:
    case Transposed{row, group, offset, high}:
      Coord{row, group, high, offset}

def transport(coordinate: Coord) -> Coord:
  transpose_back(split_join(transpose(coordinate)))

def coordinate_row(coordinate: Coord) -> Nat:
  match coordinate:
    case Coord{row, group, high, offset}:
      row

def coordinate_group(coordinate: Coord) -> Nat:
  match coordinate:
    case Coord{row, group, high, offset}:
      group

def coordinate_high(coordinate: Coord) -> Bool:
  match coordinate:
    case Coord{row, group, high, offset}:
      high

def coordinate_offset(coordinate: Coord) -> Nat:
  match coordinate:
    case Coord{row, group, high, offset}:
      offset

def selected_partner(+stage: Nat, lane: Nat) -> Nat:
  flatten(stage, transport(reshape(stage, 0n, lane)))

def selected_low(stage: Nat, lane: Nat) -> Bool:
  Bool.not(coordinate_high(reshape(stage, 0n, lane)))

# Each finite check is independently reduced, then eliminated at ARBITRARY
# bounded stage/lane. There are exactly eight stages and 256 lanes, no samples.
type Check is Data:
  Recompose{}
  BitCoverage{}
  GroupBound{}
  OffsetBound{}
  Partner{}
  Branch{}
  PartnerBound{}
  Involution{}

def check(kind: Check, +stage: Nat, +lane: Nat) -> Bool:
  match kind:
    case Recompose{}:
      Nat.is_eq(flatten(stage, reshape(stage, 0n, lane)), lane)
    case BitCoverage{}:
      Nat.is_eq(Order.value(bits(8n, lane)), lane)
    case GroupBound{}:
      Nat.is_lt(coordinate_group(reshape(stage, 0n, lane)),
        Nat.div(256n, Nat.double(Order.power2(stage))))
    case OffsetBound{}:
      Nat.is_lt(coordinate_offset(reshape(stage, 0n, lane)), Order.power2(stage))
    case Partner{}:
      Nat.is_eq(selected_partner(stage, lane), reference_partner(stage, lane))
    case Branch{}:
      Nat.is_eq(Bool.pick(Nat, selected_low(stage, lane), 1n, 0n),
        Bool.pick(Nat, reference_low(stage, lane), 1n, 0n))
    case PartnerBound{}:
      Nat.is_lt(selected_partner(stage, lane), 256n)
    case Involution{}:
      Nat.is_eq(selected_partner(stage, selected_partner(stage, lane)), lane)

def lane_checks(count: Nat, +start: Nat, +kind: Check, +stage: Nat) -> Bool:
  match count:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(check(kind, stage, start), lane_checks(p, 1n+start, kind, stage))

def stage_checks(count: Nat, +start: Nat, +kind: Check) -> Bool:
  match count:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(lane_checks(256n, 0n, kind, start), stage_checks(p, 1n+start, kind))

# Missing input is EXPLICIT, never silently zero-filled. Completeness is proved
# separately from equality, requiring at least the full 256 entering lanes.
def lookup(values: List<&2, Attention.Expr>, lane: Nat) -> Maybe<&2, Attention.Expr>:
  match values lane:
    case Nil{} _:
      None{}
    case value <> rest 0n:
      Some{value}
    case value <> rest 1n+p:
      lookup(rest, p)

def Present(value: Maybe<&2, Attention.Expr>) -> Type:
  match value:
    case None{}:
      Empty
    case Some{expression}:
      Unit

def butterfly(low: Bool, +current: Attention.Expr, +partner: Attention.Expr) -> Attention.Expr:
  Attention.Where{Bool.pick(Attention.Expr, low, Attention.One{}, Attention.Zero{}),
    Attention.Add{current, partner}, Attention.Sub{partner, current}}

def lift(low: Bool, current: Maybe<&2, Attention.Expr>, partner: Maybe<&2, Attention.Expr>)
    -> Maybe<&2, Attention.Expr>:
  match current partner:
    case Some{a} Some{b}:
      Some{butterfly(low, a, b)}
    case _ _:
      None{}

# Count is a PREFIX LENGTH: successor p+1 executes stage p after prefix p.
# Both reads therefore observe the previous stage, never the initial values.
def reference(count: Nat, +values: List<&2, Attention.Expr>, +lane: Nat)
    -> Maybe<&2, Attention.Expr>:
  match count:
    case 0n:
      lookup(values, lane)
    case 1n++p:
      lift(reference_low(p, lane), reference(p, values, lane),
        reference(p, values, reference_partner(p, lane)))

def scheduled(count: Nat, +action: Nat, +values: List<&2, Attention.Expr>, +lane: Nat)
    -> Maybe<&2, Attention.Expr>:
  match count:
    case 0n:
      lookup(values, lane)
    case 1n++p:
      match action:
        case 0n:
          lift(reference_low(p, lane), scheduled(p, 0n, values, lane),
            scheduled(p, 0n, values, reference_partner(p, lane)))
        case 1n++a:
          lift(selected_low(p, lane), scheduled(p, 1n+a, values, lane),
            scheduled(p, 1n+a, values, selected_partner(p, lane)))

def count(head256: Bool) -> Nat:
  Bool.pick(Nat, head256, 8n, 7n)

def stages(count: Nat) -> List<&2, Nat>:
  match count:
    case 0n:
      Nil{}
    case 1n++p:
      List.append(&2, Nat, stages(p), [p])

# An explicit expanded-loop context. This does NOT equate the existing opaque
# InverseHadamard constructor with an expression tree. values are the actual
# lane expressions entering that loop, under the same immutable Input identity.
def finish(+input: Attention.Input, state: Attention.State, inverse: Attention.Expr) -> Attention.Stored:
  match state:
    case Attention.State{keys, values, softmax, maximum, +denominator, raw, rotated, status}:
      numerator = {Attention.Add{raw, Attention.Mul{inverse, Attention.Ref{input, Attention.Normalize{}}}} : Attention.Expr}
      +nonempty = {Attention.Greater{denominator, Attention.Zero{}} : Attention.Expr}
      +safe = {Attention.Where{nonempty, denominator, Attention.One{}} : Attention.Expr}
      Attention.Stored{input, Attention.Ref{input, Attention.RowReal{}},
        Attention.Div{numerator, Attention.Column{safe}},
        Attention.Where{nonempty, Attention.Add{maximum, Attention.Log{safe}}, Attention.NegInfinity{}}, status}

def finish_result(input: Attention.Input, state: Attention.State, inverse: Maybe<&2, Attention.Expr>)
    -> Maybe<&2, Attention.Stored>:
  match inverse:
    case None{}:
      None{}
    case Some{value}:
      Some{finish(input, state, value)}

def StoredPresent(value: Maybe<&2, Attention.Stored>) -> Type:
  match value:
    case None{}:
      Empty
    case Some{stored}:
      Unit

# Each item is one observed lane of an existing ordered query/split partition;
# all snapshot, row-real, status, raw/max/denominator identities remain explicit.
type Partition is Data:
  Partition{input: Attention.Input, state: Attention.State,
    values: List<&2, Attention.Expr>, lane: Nat}

def Domain(partitions: List<&2, Partition>) -> Type:
  match partitions:
    case Nil{}:
      Unit
    case Partition{input, state, values, lane} <> rest:
      (Order.Le(256n, List.length(&2, Attention.Expr, values)) & Order.Le(1n+lane, 256n)) & Domain(rest)

def reference_outputs(partitions: List<&2, Partition>, +prefix: Nat)
    -> List<&2, Maybe<&2, Attention.Stored>>:
  match partitions:
    case Nil{}:
      Nil{}
    case Partition{input, state, values, lane} <> rest:
      finish_result(input, state, reference(prefix, values, lane)) <>
        reference_outputs(rest, prefix)

def OutputsPresent(outputs: List<&2, Maybe<&2, Attention.Stored>>) -> Type:
  match outputs:
    case Nil{}:
      Unit
    case value <> rest:
      StoredPresent(value) & OutputsPresent(rest)

# Integer overflow, pointer/layout lowering, IEEE behavior, compiler fusion,
# launch/lifetime refinement and emitted instructions remain external. In
# particular no theorem here repairs the failed PTX .loc line0 location gate.
