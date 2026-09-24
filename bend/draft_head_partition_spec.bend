# Independent reference for the tile partition of the draft-only int4 head kernel (ext patch 9001,
# exllamav3_ext/dflash2_head.cu, dflash2_q4_head_topk_kernel): every vocabulary tile x < n_tiles is
# computed by exactly one warp of the grid, and no tile past the end is computed. Membership and hit
# counts are plain list/Nat functions; the impl model is draft_head_partition.bend.
import Base

def bit(value: Bool) -> Nat:
  match value:
    case True{}:
      1n
    case False{}:
      0n

# x occurs in the list.
def member(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), member(rest, x))

# The intended coverage: tile x is real iff x < n_tiles.
def covered(+x: Nat, +n: Nat) -> Nat:
  bit(Nat.is_lt(x, n))

# Per-tile work order of one warp: the 64-deep chunks c = 0, 1, 2, ... in ascending order, and after
# every second chunk the fold of the 128-deep scale group g = 0, 1, 2, ... it closed
# (acc += scale_g * part; part = 0). `c` and `g` count chunks and groups independently.
type Ev is Data:
  Chunk{c: Nat}
  Fold{g: Nat}

def groups_trace(left: Nat, +g: Nat, +c: Nat) -> List<&2, Ev>:
  match left:
    case 0n:
      Nil{}
    case 1n+rest:
      Chunk{c} <> Chunk{1n+c} <> Fold{g} <> groups_trace(rest, 1n+g, 1n+1n+c)
