# Pure target-verify query-tile geometry and startup serialization values.
# No proof models or proof imports belong in this runtime module.
import Base

# Each program of the parallel third grid axis processes TILE_TOKENS query
# rows, and TILE_COUNT programs cover the native eight-token target verify
# block exactly, with no overlap, gap or out-of-range row.
def tile_tokens() -> Nat:
  4n

def tile_count() -> Nat:
  2n

# Mathematical start row. Native consumers load the compiled startup starts.
def start(tile: Nat) -> Nat:
  Nat.mul(tile, tile_tokens())

# Like Base.List.range.go: count down and prepend into one owned accumulator.
# This builds ascending starts in linear list work, with no append/reversal.
def starts_go(+count: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match count:
    case 0n:
      acc
    case 1n+p:
      starts_go(p, start(p) <> acc)

# The only list boundary is the tiny startup wire, not an attention hot loop.
def starts(count: Nat) -> List<&2, Nat>:
  starts_go(count, Nil{})

# The native eight-row verify partition: two tiles of four rows.
def native_starts() -> List<&2, Nat>:
  starts(tile_count())

# The reviewed native geometry; integration must bind this to native verify.
def selected() -> Bool:
  Bool.and(Nat.is_eq(tile_count(), 2n), Nat.is_eq(tile_tokens(), 4n))
