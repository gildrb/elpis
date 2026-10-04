# Per-tile fp16 run position over a DIET trace (m16_diet_spec.bend Ev, the event lists of the m16g and
# 8202-tail main loops: It{.., fold} = one k16-tile MMA into the fp16 accumulators, then fold() into
# fp32 when `fold`; Seg = fold() + flush at a segment end; Pro / Exit move no accumulator), the leaf
# coordinate tr of bend/err_gemm.bend: the MMAs from a tile's own to its run's fold. Laws:
# bend/err_gemm_runs_laws.bend.
import Base
import ./m16_diet_spec.bend as DSpec

def rem_it(fold: Bool, rem_rest: Nat) -> Nat:
  match fold:
    case True{}:
      1n
    case False{}:
      1n+rem_rest

# MMAs from the head of the trace to the end of the run open there (the head tile included).
def rem(evs: List<&2, DSpec.Ev>) -> Nat:
  match evs:
    case Nil{}:
      0n
    case ev <> rest:
      match ev:
        case DSpec.It{x, w, r, xo, fold}:
          rem_it(fold, rem(rest))
        case DSpec.Seg{g}:
          0n
        case DSpec.Pro{w}:
          rem(rest)
        case DSpec.Exit{st}:
          rem(rest)

def it_head(ev: DSpec.Ev) -> Bool:
  match ev:
    case DSpec.It{x, w, r, xo, fold}:
      True{}
    case DSpec.Seg{g}:
      False{}
    case DSpec.Pro{w}:
      False{}
    case DSpec.Exit{st}:
      False{}

def tr_head(ev: DSpec.Ev, rest: List<&2, DSpec.Ev>) -> Nat:
  match ev:
    case DSpec.It{x, w, r, xo, fold}:
      rem_it(fold, rem(rest))
    case DSpec.Seg{g}:
      0n
    case DSpec.Pro{w}:
      0n
    case DSpec.Exit{st}:
      0n

# Event i is a tile (an MMA).
def it_at(evs: List<&2, DSpec.Ev>, i: Nat) -> Bool:
  match evs:
    case Nil{}:
      False{}
    case ev <> rest:
      match i:
        case 0n:
          it_head(ev)
        case 1n+j:
          it_at(rest, j)

# tr of the tile at event i: its own MMA and every later MMA of its run (0 for a non-tile event).
def tr_at(evs: List<&2, DSpec.Ev>, i: Nat) -> Nat:
  match evs:
    case Nil{}:
      0n
    case ev <> rest:
      match i:
        case 0n:
          tr_head(ev, rest)
        case 1n+j:
          tr_at(rest, j)
