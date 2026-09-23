# Independent query-tile specification. Deliberately written WITHOUT importing
# or calling the executed planner: the laws compare the two definitions, so a
# spec that reuses the implementation would prove nothing.
import Base

# Sequential reference: tile t covers rows [4t, 4t+4) and valid tiles count 2.
def spec_tile_tokens() -> Nat:
  4n

def spec_tile_count() -> Nat:
  2n

def spec_start(tile: Nat) -> Nat:
  match tile:
    case 0n:
      0n
    case 1n+p:
      Nat.add(spec_tile_tokens(), spec_start(p))

# One start per tile, in ascending order. This is intentionally distinct from
# spec_tiles, which contains FOUR rows per tile; confusing them is unsatisfiable.
# The reference appends each new start; production uses a countdown accumulator.
def spec_starts(+count: Nat) -> List<&2, Nat>:
  match count:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, Nat, spec_starts(p), [spec_start(p)])

# Sequential ordered row list of length n starting at row r.
def spec_rows(+n: Nat, +row: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      row <> spec_rows(p, 1n+row)

# The verified block is exactly the ascending rows [0..8).
def spec_verified() -> List<&2, Nat>:
  spec_rows(Nat.mul(spec_tile_tokens(), spec_tile_count()), 0n)

# Sequential concatenation of each tile's covered rows, universal over count.
def spec_tiles(+count: Nat) -> List<&2, Nat>:
  match count:
    case 0n:
      Nil{}
    case 1n+p:
      List.append(&2, Nat,
        spec_tiles(p),
        spec_rows(spec_tile_tokens(), Nat.mul(spec_tile_tokens(), p)))
