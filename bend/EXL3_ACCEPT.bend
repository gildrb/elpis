# Production program: its unchanged emitted C is compiled into the serving
# shared library, whose glue calls only the scalar leaf Impl.accept. main
# renders the canonical table of EXL3_ACCEPT_SPEC.bend through that leaf:
# section A by a balanced fork-join register tree (most significant pattern
# bit first, shifted through fifteen scalar registers; filler id 17 marks
# unused registers), section B by ascending enumeration. It must be
# byte-identical to the reference program's output.
import Base
import ./exl3_accept.bend as Impl
import ./exl3_accept_spec.bend as Spec

def glyph(value: Spec.Verdict) -> Char:
  match value:
    case Spec.Verdict{count, eos}:
      match eos:
        case False{}:
          Char.from_u32((U32.from_nat(count) + 64 : U32))
        case True{}:
          Char.from_u32((U32.from_nat(count) + 96 : U32))

# Registers r0..r14 hold pattern bits 0..14: t_i = r(2i), p_i = r(2i+1).
def tree_a(+depth: Nat, +k: Nat, +budget: Nat, +checkpoint: Nat, +r0: U32,
    +r1: U32, +r2: U32, +r3: U32, +r4: U32, +r5: U32, +r6: U32, +r7: U32,
    +r8: U32, +r9: U32, +r10: U32, +r11: U32, +r12: U32, +r13: U32,
    +r14: U32) -> String:
  match depth:
    case 0n:
      SCon{glyph(Impl.accept(k, budget, checkpoint, 1n, 248046, 17, 17, 17,
        r0, r2, r4, r6, r8, r10, r12, r14, r1, r3, r5, r7, r9, r11, r13)),
        SNil{}}
    case 1n+p:
      left right = tree_a(p, k, budget, checkpoint, 17, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13) tree_a(p, k, budget, checkpoint, 248046, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13)
      String.append(left, right)

def row_a(+k: Nat, +budget: Nat, +checkpoint: Nat) -> String:
  "A " ++ Nat.show(k) ++ " " ++ Nat.show(budget) ++ " " ++
    Nat.show(checkpoint) ++ " " ++
    tree_a(1n+Nat.double(k), k, budget, checkpoint, 17, 17, 17, 17, 17, 17,
      17, 17, 17, 17, 17, 17, 17, 17, 17)

def emit_checkpoints(count: Nat, +checkpoint: Nat, +k: Nat,
    +budget: Nat) -> IO(Unit):
  match count:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+rest:
      do IO<Unit>:
        IO.print(row_a(k, budget, checkpoint))
        emit_checkpoints(rest, 1n+checkpoint, k, budget)

def emit_budgets(count: Nat, +budget: Nat, +k: Nat) -> IO(Unit):
  match count:
    case 0n:
      emit_checkpoints(1n+k, 0n, k, 262144n)
    case 1n+rest:
      do IO<Unit>:
        emit_checkpoints(1n+k, 0n, k, budget)
        emit_budgets(rest, 1n+budget, k)

def emit_a(count: Nat, +k: Nat) -> IO(Unit):
  match count:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+rest:
      do IO<Unit>:
        emit_budgets(2n+k, 1n, k)
        emit_a(rest, 1n+k)

def quaternary(digit: Nat) -> U32:
  match digit:
    case 0n:
      0
    case 1n+a:
      match a:
        case 0n:
          1
        case 1n+b:
          match b:
            case 0n:
              248046
            case 1n+c:
              4294967295

def pick_filler(bit: Nat, here: U32, later: U32) -> U32:
  match bit:
    case 0n:
      here
    case 1n+one:
      later

# Stop slots for a mask over [0, 1, 248046, 4294967295]: set ids ascending
# in s0.., unused slots hold the smallest unselected id (0 when all four are
# selected), so a leaf reading an unused slot would misclassify a target.
def filler(width: Nat, +mask: Nat, +place: Nat) -> U32:
  match width:
    case 0n:
      0
    case 1n+rest:
      pick_filler(Nat.mod(mask, 2n), quaternary(place),
        filler(rest, Nat.div(mask, 2n), 1n+place))

type Slots is Data:
  Slots{ns: Nat, s0: U32, s1: U32, s2: U32, s3: U32}

# A selected id is shifted in at s0; applying digits 3..0 in that order
# leaves the selected ids ascending from s0.
def shift(bit: Nat, id: U32, slots: Slots) -> Slots:
  match bit:
    case 0n:
      slots
    case 1n+one:
      match slots:
        case Slots{ns, s0, s1, s2, s3}:
          Slots{1n+ns, id, s0, s1, s2}

def bit_at(+mask: Nat, place: Nat) -> Nat:
  Nat.mod(Nat.div(mask, Nat.pow(2n, place)), 2n)

def slots(+mask: Nat) -> Slots:
  +fill = filler(4n, mask, 0n)
  shift(bit_at(mask, 0n), quaternary(0n),
    shift(bit_at(mask, 1n), quaternary(1n),
      shift(bit_at(mask, 2n), quaternary(2n),
        shift(bit_at(mask, 3n), quaternary(3n),
          Slots{0n, fill, fill, fill, fill}))))

def cell_b(+x: Nat, stops: Slots) -> Spec.Verdict:
  match stops:
    case Slots{ns, s0, s1, s2, s3}:
      Impl.accept(1n, 3n, 0n, ns, s0, s1, s2, s3,
        quaternary(Nat.mod(x, 4n)), quaternary(Nat.mod(Nat.div(x, 16n), 4n)),
        17, 17, 17, 17, 17, 17, quaternary(Nat.mod(Nat.div(x, 4n), 4n)), 17,
        17, 17, 17, 17, 17)

def cells_b(count: Nat, +x: Nat, +stops: Slots) -> String:
  match count:
    case 0n:
      ""
    case 1n+rest:
      SCon{glyph(cell_b(x, stops)), cells_b(rest, 1n+x, stops)}

def emit_b(count: Nat, +mask: Nat) -> IO(Unit):
  match count:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+rest:
      do IO<Unit>:
        IO.print("B " ++ Nat.show(mask) ++ " " ++ cells_b(64n, 0n, slots(mask)))
        emit_b(rest, 1n+mask)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("EXL3_GREEDY_ACCEPT_V1")
    emit_a(7n, 1n)
    emit_b(16n, 0n)
    IO.print("END_EXL3_GREEDY_ACCEPT")
