# Independent reference for ext 3013 (bend/kv_compact.bend): what a chain verify of the accepted path leaves in the
# 8-row verify window, and the sequential ascending copy the commit claims to equal (K:44-45 of
# patches/exl3-ext/3013-kv-compact-rows.patch; stock: the chain verify writes path row P[j] at slot base + j directly).
# Window slot r holds the tree verify's row r before the commit.
import Base

type Mv is Data:
  Mv{s: Nat, d: Nat}

# the tree verify's window: slot r holds row r, r < 8
def window() -> List<&2, Nat>:
  [0n, 1n, 2n, 3n, 4n, 5n, 6n, 7n]

# A legal accepted path (exl3_tree_accept: P[0] = 0, strictly increasing, rows < 8) is 0 followed by an ascending subset
# of 1 .. 7; bit r - 1 of m < 128 selects row r
def path_of.keep(c: Bool, +r: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case True{}:
      r <> rest
    case False{}:
      rest

def path_of.go(k: Nat, +r: Nat, +m: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      []
    case 1n+j:
      path_of.keep(Nat.is_eq(Nat.mod(m, 2n), 1n), r, path_of.go(j, 1n+r, Nat.div(m, 2n)))

def path_of(+m: Nat) -> List<&2, Nat>:
  0n <> path_of.go(7n, 1n, m)

def at(xs: List<&2, Nat>, +i: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, rest}:
      match i:
        case 0n:
          x
        case 1n+k:
          at(rest, k)

def put(xs: List<&2, Nat>, +i: Nat, +v: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      match i:
        case 0n:
          v <> rest
        case 1n+k:
          x <> put(rest, k, v)

# K:44-45 the sequential ascending copy: apply the moves one after another, each reading the current contents
def seq_copy(mv: List<&2, Mv>, +mem: List<&2, Nat>) -> List<&2, Nat>:
  match mv:
    case Nil{}:
      mem
    case Con{Mv{+s, +d}, rest}:
      seq_copy(rest, put(mem, d, at(mem, s)))
