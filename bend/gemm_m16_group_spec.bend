# Independent reference for the grouped m16 GEMM (ext patch 2102) bundle maps. A bundle is the
# list of matrix widths n_0, n_1, ... (columns; the launch serves up to 4 matrices sharing k).
# Matrix i owns n_i / 512 column groups; the reference numbers the (matrix, local group) pairs by
# plain recursion over the list (no prefix-sum array, no search loop), numbers the prologue's
# (matrix, token row, 128-column block) cells and the finisher's (matrix, token row, 128-column
# chunk) tasks row-major, and names each by its natural memory offsets.
import Base

# Width of matrix i (0 past the end of the bundle).
def width(ns: List<&2, Nat>, i: Nat) -> Nat:
  match ns:
    case Nil{}:
      0n
    case n <> rest:
      match i:
        case 0n:
          n
        case 1n+j:
          width(rest, j)

# Number of 512-column groups of matrix i.
def ng_at(ns: List<&2, Nat>, i: Nat) -> Nat:
  Nat.div(width(ns, i), 512n)

# Groups of the matrices before matrix i.
def before.go(i: Nat, ns: List<&2, Nat>) -> Nat:
  match i:
    case 0n:
      0n
    case 1n+j:
      match ns:
        case Nil{}:
          0n
        case n <> rest:
          Nat.add(Nat.div(n, 512n), before.go(j, rest))

def before(ns: List<&2, Nat>, +i: Nat) -> Nat:
  before.go(i, ns)

# Groups of the whole bundle.
def ngroups(ns: List<&2, Nat>) -> Nat:
  match ns:
    case Nil{}:
      0n
    case n <> rest:
      Nat.add(Nat.div(n, 512n), ngroups(rest))

# Launch-wide index of local group l of matrix i: the groups of the earlier matrices come first.
def gidx(ns: List<&2, Nat>, i: Nat, l: Nat) -> Nat:
  Nat.add(before(ns, i), l)

# Every width is a positive multiple of 512 (H:102-103 of the patch's shape_ok).
def widths_ok(ns: List<&2, Nat>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case +n <> rest:
      Bool.and(Nat.is_le(512n, n), Bool.and(Nat.is_eq(Nat.mod(n, 512n), 0n), widths_ok(rest)))

# A launchable bundle: 1 .. 4 matrices of admissible widths.
def bundle_ok(+ns: List<&2, Nat>) -> Bool:
  Bool.and(Nat.is_lt(0n, List.length(&2, Nat, ns)),
    Bool.and(Nat.is_le(List.length(&2, Nat, ns), 4n), widths_ok(ns)))

# Prologue cell (matrix i, token row r, 128-column block c) of the input transform: its offset in
# the concatenated per-matrix size_m x size_k scratch (matrix i first, rows of size_k halves).
def xh_cell(+m: Nat, +k: Nat, i: Nat, r: Nat, c: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(i, Nat.mul(m, k)), Nat.mul(r, k)), Nat.mul(c, 128n))

# Its source: the same 128 elements of input row r.
def a_cell(+k: Nat, r: Nat, c: Nat) -> Nat:
  Nat.add(Nat.mul(r, k), Nat.mul(c, 128n))

# Row-major number of the cell: (i * m + r) * (k / 128) + c.
def cell_index(+m: Nat, +k: Nat, i: Nat, r: Nat, c: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(i, m), r), Nat.div(k, 128n)), c)

# A finisher task: 128 output columns starting at col0 of token row r of matrix mat.
type Place is Data:
  Place{mat: Nat, r: Nat, col0: Nat}

def place_mat(p: Place) -> Nat:
  match p:
    case Place{mat, r, col0}:
      mat

def place_r(p: Place) -> Nat:
  match p:
    case Place{mat, r, col0}:
      r

def place_col0(p: Place) -> Nat:
  match p:
    case Place{mat, r, col0}:
      col0
