# Query-tile contracts and proof-only interpretations of the emitted starts.
# Exact row order includes full coverage, no overlap/omission and logical bounds.
# These models are not imported by the production planner or attention loop.
import Base
import ./query_tiles.bend as QueryTiles
import ./query_tiles_spec.bend as Spec

# The scalar row traversal of a tile; no change to within-row arithmetic is
# modeled or asserted here. CUDA arithmetic and native launch require their
# separate refinement/evidence boundary.
def covered(+n: Nat, +row: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      row <> covered(p, 1n+row)

# Interpret the ACTUAL emitted start sequence, preserving its order and length.
# Returning an empty/reversed/duplicated/omitted startup sequence cannot satisfy
# starts_coverage, even if scalar start() remains correct.
def flatten(starts: List<&2, Nat>) -> List<&2, Nat>:
  match starts:
    case Nil{}:
      Nil{}
    case row <> rest:
      List.append(&2, Nat, covered(QueryTiles.tile_tokens(), row), flatten(rest))

# Original universal scalar bound, relocated out of the runtime import graph.
def in_bounds(+count: Nat) -> Bool:
  match count:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Nat.is_lt(QueryTiles.start(p),
        Nat.mul(QueryTiles.tile_tokens(), Nat.add(p, 1n))), in_bounds(p))

# The executed scalar start agrees with independent multiplication orientation.
law start_semantics:
  for tile: Nat
  {QueryTiles.start(tile) == Nat.mul(QueryTiles.tile_tokens(), tile) : Nat}

# Coverage: tile t plus its three following rows are exactly rows [4t..4t+4).
law tile_block:
  for tile: Nat
  {covered(QueryTiles.tile_tokens(), QueryTiles.start(tile))
    == Spec.spec_rows(QueryTiles.tile_tokens(), Spec.spec_start(tile))
    : List<&2, Nat>}

# Universal row-loop interpretation agrees with the independent ordered rows.
law covered_exact:
  for +n: Nat
  for +row: Nat
  {covered(n, row) == Spec.spec_rows(n, row) : List<&2, Nat>}

# One emitted start per tile, not a list of every covered row.
law starts_semantics:
  for +count: Nat
  {QueryTiles.starts(count) == Spec.spec_starts(count) : List<&2, Nat>}

# Every scalar start is inside the bound for that tile's nonempty prefix.
law starts_bounded:
  for +count: Nat
  {in_bounds(count) == True{} : Bool}

# Universal coverage of the production start sequence, not merely the spec.
# Equality to [0..4*count) excludes gaps, duplicates, reordering and extra rows.
law starts_coverage:
  for +count: Nat
  {flatten(QueryTiles.starts(count))
    == Spec.spec_rows(Nat.mul(Spec.spec_tile_tokens(), count), 0n)
    : List<&2, Nat>}

# The native two-tile partition covers the eight verify rows exactly, in order.
law native_coverage:
  {Spec.spec_tiles(QueryTiles.tile_count()) == Spec.spec_verified() : List<&2, Nat>}

# Direct native production connection, additional to the original reference law.
law native_rows_exact:
  {flatten(QueryTiles.native_starts()) == Spec.spec_verified() : List<&2, Nat>}

# The emitted native start list is exactly [0n, 4n].
law native_starts_exact:
  {QueryTiles.native_starts() == [0n, 4n] : List<&2, Nat>}

# The deployed selection is the reviewed 2x4 geometry.
law native_selected:
  {QueryTiles.selected() == True{} : Bool}
