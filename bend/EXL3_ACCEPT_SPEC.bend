# Finite differential checker: the canonical EXL3 greedy acceptance table,
# computed by the independent list reference (exl3_accept_spec.bend) with
# plain forward enumeration and arithmetic bit decoding.
#
# Section A, for k = 1..7, budgets 1..k+2 and 262144, checkpoints 0..k:
# one glyph per pattern x in 0..2^(2k+1)-1, ascending. Target t_i is bit 2i
# of x and proposal p_i is bit 2i+1 (i < k); bit 0 is id 17 and bit 1 is id
# 248046; the stop set is [248046]. Every (stop, match) combination per
# position occurs, so the core decision domain is covered exhaustively.
# Section B, k = 1, budget 3, checkpoint 0: every sorted stop subset (mask
# 0..15 over [0, 1, 248046, 4294967295]) and every t0, p0, t1 in that
# alphabet (x: t0 = bits 0-1, p0 = bits 2-3, t1 = bits 4-5).
# Glyph: count 1..8 is A..H without eos and a..h with eos.
import Base
import ./exl3_accept_spec.bend as Spec

def glyph(value: Spec.Verdict) -> Char:
  match value:
    case Spec.Verdict{count, eos}:
      match eos:
        case False{}:
          Char.from_u32((U32.from_nat(count) + 64 : U32))
        case True{}:
          Char.from_u32((U32.from_nat(count) + 96 : U32))

def binary(bit: Nat) -> U32:
  match bit:
    case 0n:
      17
    case 1n+rest:
      248046

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

def targets(k: Nat, +x: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      [binary(Nat.mod(x, 2n))]
    case 1n+rest:
      binary(Nat.mod(x, 2n)) <> targets(rest, Nat.div(x, 4n))

def proposals(k: Nat, +x: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+rest:
      binary(Nat.mod(Nat.div(x, 2n), 2n)) <> proposals(rest, Nat.div(x, 4n))

def cells_a(count: Nat, +x: Nat, +k: Nat, +budget: Nat,
    +checkpoint: Nat) -> String:
  match count:
    case 0n:
      ""
    case 1n+rest:
      SCon{glyph(Spec.accept(targets(k, x), proposals(k, x), [248046], budget,
        checkpoint)), cells_a(rest, 1n+x, k, budget, checkpoint)}

def row_a(+k: Nat, +budget: Nat, +checkpoint: Nat) -> String:
  "A " ++ Nat.show(k) ++ " " ++ Nat.show(budget) ++ " " ++
    Nat.show(checkpoint) ++ " " ++
    cells_a(Nat.pow(2n, 1n+Nat.double(k)), 0n, k, budget, checkpoint)

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

def keep(bit: Nat, id: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match bit:
    case 0n:
      rest
    case 1n+one:
      id <> rest

# Ascending subset of the quaternary alphabet selected by the mask bits.
def stops(width: Nat, +mask: Nat, +digit: Nat) -> List<&2, U32>:
  match width:
    case 0n:
      Nil{}
    case 1n+rest:
      keep(Nat.mod(mask, 2n), quaternary(digit),
        stops(rest, Nat.div(mask, 2n), 1n+digit))

def cells_b(count: Nat, +x: Nat, +mask: Nat) -> String:
  match count:
    case 0n:
      ""
    case 1n+rest:
      SCon{glyph(Spec.accept(
        [quaternary(Nat.mod(x, 4n)), quaternary(Nat.mod(Nat.div(x, 16n), 4n))],
        [quaternary(Nat.mod(Nat.div(x, 4n), 4n))],
        stops(4n, mask, 0n), 3n, 0n)), cells_b(rest, 1n+x, mask)}

def emit_b(count: Nat, +mask: Nat) -> IO(Unit):
  match count:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+rest:
      do IO<Unit>:
        IO.print("B " ++ Nat.show(mask) ++ " " ++ cells_b(64n, 0n, mask))
        emit_b(rest, 1n+mask)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("EXL3_GREEDY_ACCEPT_V1")
    emit_a(7n, 1n)
    emit_b(16n, 0n)
    IO.print("END_EXL3_GREEDY_ACCEPT")
