# Independent reference for the TREE verify attention (attn_tree.bend). A round of 8 verify rows is a
# token tree given by its parents ps = [q1, .., q7] (row r > 0 has parent q_r < r, row 0 is the
# anchor, DESIGN.md 2.1). Row r stands at depth[r] (edges from the root) and must attend exactly as
# the chain row at depth[r] whose rows 0 .. depth[r] hold r's root-to-r path: in-round column
# base + j (j <= depth[r]) holding row r's depth-j ancestor, the columns past it masked. The
# TreeDesc the kernel reads is derived here from its DESIGN.md 2.2 definitions (depth, path,
# leaf_of = the leaf reached by repeatedly taking the lowest-row child, leaves ascending), by
# list walks unrelated to the host's derive (bend/exl3_tree_accept.bend).
import Base
import ./attn_tree.bend as Impl

# The i-th element (0 past the end)
def nth(xs: List<&2, Nat>, i: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      match i:
        case 0n:
          x
        case 1n+k:
          nth(rest, k)

# The parent of row r (the root is its own)
def parent(+ps: List<&2, Nat>, r: Nat) -> Nat:
  match r:
    case 0n:
      0n
    case 1n+k:
      nth(ps, k)

def keep(b: Bool, +c: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      c <> rest
    case False{}:
      rest

def pick(b: Bool, +x: Nat, +y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

def nil(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case c <> rest:
      False{}

# Row r's ancestor k steps up (the root stays)
def up(k: Nat, +ps: List<&2, Nat>, r: Nat) -> Nat:
  match k:
    case 0n:
      r
    case 1n+m:
      up(m, ps, parent(ps, r))

# Edges from row r to the root, fuel >= depth (8 rows: 7 suffice)
def depth.go(fuel: Nat, +ps: List<&2, Nat>, r: Nat) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      match r:
        case 0n:
          0n
        case 1n+k:
          1n+depth.go(f, ps, parent(ps, 1n+k))

def depth(+ps: List<&2, Nat>, +r: Nat) -> Nat:
  depth.go(8n, ps, r)

# Row r's ancestor at depth j <= depth(r) (r itself at j = depth(r), the root at j = 0); anc_d
# takes dr = depth(r)
def anc_d(+ps: List<&2, Nat>, +r: Nat, dr: Nat, +j: Nat) -> Nat:
  up(Nat.sub(dr, j), ps, r)

def anc(+ps: List<&2, Nat>, +r: Nat, +j: Nat) -> Nat:
  anc_d(ps, r, depth(ps, r), j)

# Children of v among rows c .. c + n - 1, in row order
def kids.go(n: Nat, +ps: List<&2, Nat>, +v: Nat, +c: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      keep(Nat.is_eq(parent(ps, c), v), c, kids.go(m, ps, v, 1n+c))

def kids(+ps: List<&2, Nat>, +v: Nat) -> List<&2, Nat>:
  kids.go(7n, ps, v, 1n)

def descend(fuel: Nat, ks: List<&2, Nat>, +ps: List<&2, Nat>, r: Nat) -> Nat:
  match fuel:
    case 0n:
      r
    case 1n+f:
      match ks:
        case Nil{}:
          r
        case +c <> rest:
          descend(f, kids(ps, c), ps, c)

# The leaf reached from r by repeatedly taking the lowest-row child
def leaf_of(+ps: List<&2, Nat>, +r: Nat) -> Nat:
  descend(8n, kids(ps, r), ps, r)

def is_leaf(+ps: List<&2, Nat>, +r: Nat) -> Bool:
  nil(kids(ps, r))

# Leaf rows among r .. r + n - 1, ascending
def leaves.go(n: Nat, +ps: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      keep(is_leaf(ps, r), r, leaves.go(m, ps, 1n+r))

def leaves(+ps: List<&2, Nat>) -> List<&2, Nat>:
  leaves.go(8n, ps, 0n)

# f(0) .. f(n - 1) for f = depth / leaf_of over rows r ..
def depths(n: Nat, +ps: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      depth(ps, r) <> depths(m, ps, 1n+r)

def leafs(n: Nat, +ps: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      leaf_of(ps, r) <> leafs(m, ps, 1n+r)

# n bytes 0xFF
def fill(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      255n <> fill(m)

# The first n bytes of xs, padded to n with 0xFF
def pad(xs: List<&2, Nat>, n: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      fill(n)
    case x <> rest:
      match n:
        case 0n:
          Nil{}
        case 1n+m:
          x <> pad(rest, m)

# path[r][j], j < n from j: the depth-j ancestor for j <= depth(r), 0xFF beyond (dr = depth(r))
def path_row(n: Nat, +ps: List<&2, Nat>, +r: Nat, +dr: Nat, +j: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      pick(Nat.is_le(j, dr), anc_d(ps, r, dr, j), 255n) <> path_row(m, ps, r, dr, 1n+j)

def paths(n: Nat, +ps: List<&2, Nat>, +r: Nat) -> List<&2, List<&2, Nat>>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      path_row(8n, ps, r, depth(ps, r), 0n) <> paths(m, ps, 1n+r)

# The TreeDesc bytes the kernel reads, per DESIGN.md 2.2
def desc(+ps: List<&2, Nat>) -> Impl.TreeDesc:
  +lv = leaves(ps)
  Impl.TreeDesc{84n, 1n, 8n, List.length(&2, Nat, lv), depths(8n, ps, 0n), leafs(8n, ps, 0n), pad(lv, 8n), paths(8n, ps, 0n)}

# The parent list of a legal 8-row shape
def shape(q1: Nat, q2: Nat, q3: Nat, q4: Nat, q5: Nat, q6: Nat, q7: Nat) -> List<&2, Nat>:
  [q1, q2, q3, q4, q5, q6, q7]

# The chain: parent r - 1
def chain() -> List<&2, Nat>:
  shape(0n, 1n, 2n, 3n, 4n, 5n, 6n)

# Legal shapes: q_r < r
def legal(+q1: Nat, +q2: Nat, +q3: Nat, +q4: Nat, +q5: Nat, +q6: Nat, +q7: Nat) -> Bool:
  Bool.and(Nat.is_lt(q1, 1n), Bool.and(Nat.is_lt(q2, 2n), Bool.and(Nat.is_lt(q3, 3n),
    Bool.and(Nat.is_lt(q4, 4n), Bool.and(Nat.is_lt(q5, 5n), Bool.and(Nat.is_lt(q6, 6n), Nat.is_lt(q7, 7n)))))))

def once(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

# The chain row at depth d holding r's path: in-round column base + j is seen iff j <= d, and then
# holds r's depth-j ancestor
def chain_sees(+j: Nat, +d: Nat) -> Bool:
  Nat.is_le(j, d)
