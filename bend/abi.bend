# Executable abstract counterpart of native.cu, NOT another native entry point.
# Transport uses bits so every signed int32/int64 pattern is representable even
# though original Bend Nat immediates have only 48 bits. All external observations
# and bit arrays must be populated from real tensors to refine a native launch.
import Base
import ./abi_spec.bend as Spec

def decode(n: Nat) -> Maybe<&2, Spec.Slot>:
  match n:
    case 0n:
      Some{Spec.S0{}}
    case 1n+p:
      match p:
        case 0n:
          Some{Spec.S1{}}
        case 1n+q:
          match q:
            case 0n:
              Some{Spec.S2{}}
            case 1n+r:
              match r:
                case 0n:
                  Some{Spec.S3{}}
                case 1n+s:
                  match s:
                    case 0n:
                      Some{Spec.S4{}}
                    case 1n+t:
                      match t:
                        case 0n:
                          Some{Spec.S5{}}
                        case 1n+u:
                          match u:
                            case 0n:
                              Some{Spec.S6{}}
                            case 1n+v:
                              match v:
                                case 0n:
                                  Some{Spec.S7{}}
                                case 1n+w:
                                  None{}

# native.cu words: accepted, committed, target bonus index, sequence delta.
def words(accepted: Spec.Slot) -> List<&2, Nat>:
  +a = Spec.index(accepted)
  [a, 1n+a, a, 1n+a]

def checked_words(value: Maybe<&2, Spec.Slot>) -> Maybe<&2, List<&2, Nat>>:
  match value:
    case None{}:
      None{}
    case Some{slot}:
      Some{words(slot)}

def project_words(accepted: Nat) -> Maybe<&2, List<&2, Nat>>:
  checked_words(decode(accepted))

# native.cu j<7 ? candidates[base+j+1] : 0, prior to the bonus overwrite.
def ordinary(slot: Spec.Slot) -> Spec.Source:
  match slot:
    case Spec.S0{}:
      Spec.Input{1n}
    case Spec.S1{}:
      Spec.Input{2n}
    case Spec.S2{}:
      Spec.Input{3n}
    case Spec.S3{}:
      Spec.Input{4n}
    case Spec.S4{}:
      Spec.Input{5n}
    case Spec.S5{}:
      Spec.Input{6n}
    case Spec.S6{}:
      Spec.Input{7n}
    case Spec.S7{}:
      Spec.ZeroFill{}

def overwrite(equal: Bool, accepted: Spec.Slot, slot: Spec.Slot) -> Spec.Source:
  match equal:
    case True{}:
      Spec.TargetBonus{Spec.index(accepted)}
    case False{}:
      ordinary(slot)

def project(+accepted: Spec.Slot, +slot: Spec.Slot) -> Spec.Source:
  overwrite(Nat.is_eq(Spec.index(slot), Spec.index(accepted)), accepted, slot)

# Row stride is eight ELEMENTS, independently of each tensor's element width.
def block_element(row: Nat, slot: Spec.Slot) -> Spec.ElementOffset:
  Spec.Elements{Nat.add(Nat.mul(row, 8n), Spec.index(slot))}

def prefix_element(row: Nat, stride: Nat) -> Spec.ElementOffset:
  Spec.Elements{Nat.mul(row, stride)}

def prefix_byte(width: Spec.Width, row: Nat, stride: Nat) -> Spec.ByteOffset:
  Spec.element_bytes(width, prefix_element(row, stride))

# Exact signed load plus output conversion. The sign bit is copied only when
# widening; narrowing discards high bits. Neither operation rejects negatives.
def resize(n: Nat, +fill: Bool, xs: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          fill <> resize(p, fill, Nil{})
        case h <> t:
          h <> resize(p, fill, t)

def converted(dest: Spec.Width, +xs: List<&2, Bool>) -> List<&2, Bool>:
  resize(Spec.bits(dest), Spec.sign(xs), xs)

def transfer_valid(ok: Bool, dest: Spec.Width, xs: List<&2, Bool>) -> Spec.Transfer:
  match ok:
    case False{}:
      Spec.Malformed{}
    case True{}:
      Spec.Value{converted(dest, xs)}

def transfer(source: Spec.Width, dest: Spec.Width, raw: Spec.Raw) -> Spec.Transfer:
  match raw:
    case Spec.Missing{}:
      Spec.Absent{}
    case Spec.Cancelled{}:
      Spec.Aborted{}
    case Spec.Bits{+value}:
      transfer_valid(Spec.valid_width(source, value), dest, value)

# Ripple carry over little-endian bits. Carry leaving the fixed list is dropped.
def carry(xs: List<&2, Bool>, +c: Bool) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      Bool.xor(c, h) <> carry(t, Bool.and(c, h))

def advance(delta: Nat, xs: List<&2, Bool>) -> List<&2, Bool>:
  match delta:
    case 0n:
      xs
    case 1n+p:
      advance(p, carry(xs, True{}))

def sequence_valid(ok: Bool, dest: Spec.Width, delta: Nat,
    xs: List<&2, Bool>) -> Spec.Transfer:
  match ok:
    case False{}:
      Spec.Malformed{}
    case True{}:
      Spec.Value{converted(dest, advance(delta, xs))}

def sequence(source: Spec.Width, dest: Spec.Width, delta: Nat,
    raw: Spec.Raw) -> Spec.Transfer:
  match raw:
    case Spec.Missing{}:
      Spec.Absent{}
    case Spec.Cancelled{}:
      Spec.Aborted{}
    case Spec.Bits{+value}:
      sequence_valid(Spec.valid_width(source, value), dest, delta, value)

# Validate one observed host condition at a time; successful checks preserve
# order and cannot erase an earlier missing/failed/cancelled condition.
def next(observation: Spec.Observation, rest: Spec.Admission) -> Spec.Admission:
  match observation:
    case Spec.Unknown{check}:
      Spec.Unobserved{check}
    case Spec.Failed{check}:
      Spec.Rejected{check}
    case Spec.Passed{check}:
      rest
    case Spec.Stopped{}:
      Spec.CancelLaunch{}

def admit(observations: List<&2, Spec.Observation>) -> Spec.Admission:
  match observations:
    case Nil{}:
      Spec.Ready{}
    case h <> t:
      next(h, admit(t))

def comparison_valid(ok: Bool, +index: Nat) -> Maybe<&2, Spec.ComparisonPair>:
  match ok:
    case False{}:
      None{}
    case True{}:
      Some{Spec.ComparisonPair{1n+index, index}}

def comparison(slot: Spec.Slot) -> Maybe<&2, Spec.ComparisonPair>:
  +index = Spec.index(slot)
  comparison_valid(Nat.is_lt(index, 7n), index)
