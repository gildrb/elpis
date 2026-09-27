# Independent reference for the ext 5109 GDN tree verify (gdn_tree.bend), written from DESIGN.md 2.2 / 3c / 3e
# without the kernel's byte encoding, index arithmetic or program walker:
#   - the tree of an 8-row parent array (parent[r] < r, row 0 the root): path[r] = r's ancestors by depth;
#   - the GDN program rule (a DFS; prog_bound.py prog_of): ADV 0, then visit(0); at node v with children in
#     row order split into leaves and inner nodes: no inner child -> PEEK every leaf but the last, ADV the
#     last; else PEEK every leaf, then for every inner child but the last: ADV c, visit(c), RELOAD,
#     REPLAY path[v]; finally ADV the last inner child and visit it;
#   - a row's intended state history is path[r]; its conv window is the last K of the committed window
#     (seq 1..K-1) followed by its path's raw inputs (seq K + j for row j);
#   - the commit of the accepted path P = path[last][0..count): the conv window after it is the last K of
#     seq [0..K-1] followed by the path's inputs; the replay applies P's rows in order.
# Proof model only (not shipped).
import Base

# ---- lists
def nth(xs: List<&2, Nat>, +i: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      match i:
        case 0n:
          x
        case 1n+j:
          nth(rest, j)

def cat(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat>:
  List.append(&2, Nat, xs, ys)

def take(+xs: List<&2, Nat>, +n: Nat) -> List<&2, Nat>:
  List.take(&2, Nat, xs, n)

def len(+xs: List<&2, Nat>) -> Nat:
  List.length(&2, Nat, xs)

def last_k(+xs: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  List.drop(&2, Nat, xs, Nat.sub(len(xs), k))
def nat_eq_list(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          True{}
        case _ <> _:
          False{}
    case x <> a:
      match ys:
        case Nil{}:
          False{}
        case y <> b:
          Bool.and(Nat.is_eq(x, y), nat_eq_list(a, b))

def b2n(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def sel_l(b: Bool, +x: List<&2, Nat>, +y: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      x
    case False{}:
      y

def sel_n(b: Bool, +x: Nat, +y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

def range.go(n: Nat, +s: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      s <> range.go(m, 1n+s)

def range(+s: Nat, +e: Nat) -> List<&2, Nat>:
  range.go(Nat.sub(e, s), s)

# ---- the tree (par = [p0, p1, .., p7], p0 unused)
def kids.go(n: Nat, +c: Nat, +par: List<&2, Nat>, +v: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      +rest = kids.go(m, 1n+c, par, v)
      sel_l(Nat.is_eq(nth(par, c), v), c <> rest, rest)

# children of v in row order (rows 1..7)
def kids(+par: List<&2, Nat>, +v: Nat) -> List<&2, Nat>:
  kids.go(7n, 1n, par, v)

def is_nil(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case _ <> _:
      False{}

def is_leaf(+par: List<&2, Nat>, +c: Nat) -> Bool:
  is_nil(kids(par, c))

def split(+par: List<&2, Nat>, xs: List<&2, Nat>, +want_leaf: Bool) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      +tl = split(par, rest, want_leaf)
      sel_l(Nat.is_eq(b2n(is_leaf(par, c)), b2n(want_leaf)), c <> tl, tl)

# path[r]: the root, then r's ancestors by depth, then r (fuel: depth <= 7)
def path.go(fuel: Nat, +par: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  match fuel:
    case 0n:
      [0n]
    case 1n+f:
      match r:
        case 0n:
          [0n]
        case 1n+q:
          cat(path.go(f, par, nth(par, r)), [r])

def path(+par: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  path.go(8n, par, r)

def depth(+par: List<&2, Nat>, +r: Nat) -> Nat:
  Nat.sub(len(path(par, r)), 1n)

# ---- the program rule. op 0 ADV, 1 PEEK, 2 RELOAD, 3 REPLAY
type Op is Data:
  Op{op: Nat, row: Nat}

def cat_ops(+xs: List<&2, Op>, +ys: List<&2, Op>) -> List<&2, Op>:
  List.append(&2, Op, xs, ys)

def peeks(xs: List<&2, Nat>) -> List<&2, Op>:
  match xs:
    case Nil{}:
      Nil{}
    case c <> rest:
      Op{1n, c} <> peeks(rest)

def replays(xs: List<&2, Nat>) -> List<&2, Op>:
  match xs:
    case Nil{}:
      Nil{}
    case c <> rest:
      Op{3n, c} <> replays(rest)

# every leaf but the last as PEEK, the last as ADV
def leaf_run(xs: List<&2, Nat>) -> List<&2, Op>:
  match xs:
    case Nil{}:
      Nil{}
    case c <> rest:
      match rest:
        case Nil{}:
          [Op{0n, c}]
        case _ <> _:
          Op{1n, c} <> leaf_run(rest)

# worklist form of the DFS (op 4 = "visit row"): expand(v) is visit(v) with the recursive visits as items
def inner_items(+par: List<&2, Nat>, +v: Nat, xs: List<&2, Nat>) -> List<&2, Op>:
  match xs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      match rest:
        case Nil{}:
          [Op{0n, c}, Op{4n, c}]
        case _ <> _:
          cat_ops([Op{0n, c}, Op{4n, c}, Op{2n, 0n}], cat_ops(replays(path(par, v)), inner_items(par, v, rest)))

def expand_node(+par: List<&2, Nat>, +v: Nat, +leaves: List<&2, Nat>, inner: List<&2, Nat>) -> List<&2, Op>:
  match inner:
    case Nil{}:
      leaf_run(leaves)
    case +c <> rest:
      cat_ops(peeks(leaves), inner_items(par, v, c <> rest))

def expand(+par: List<&2, Nat>, +v: Nat) -> List<&2, Op>:
  +ks = kids(par, v)
  expand_node(par, v, split(par, ks, True{}), split(par, ks, False{}))

def run_items(fuel: Nat, +par: List<&2, Nat>, xs: List<&2, Op>) -> List<&2, Op>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match xs:
        case Nil{}:
          Nil{}
        case Op{+op, +row} <> rest:
          match op:
            case 0n:
              Op{0n, row} <> run_items(f, par, rest)
            case 1n+o1:
              match o1:
                case 0n:
                  Op{1n, row} <> run_items(f, par, rest)
                case 1n+o2:
                  match o2:
                    case 0n:
                      Op{2n, row} <> run_items(f, par, rest)
                    case 1n+o3:
                      match o3:
                        case 0n:
                          Op{3n, row} <> run_items(f, par, rest)
                        case 1n+o4:
                          run_items(f, par, cat_ops(expand(par, row), rest))

def prog(+par: List<&2, Nat>) -> List<&2, Op>:
  Op{0n, 0n} <> run_items(64n, par, [Op{4n, 0n}])

# ---- windows (K = 4 conv taps; seq = [old0 .. old3, x0 .. x7], seq index K + j = row j's raw input)
def seq_of_rows(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case j <> rest:
      Nat.add(4n, j) <> seq_of_rows(rest)

# row r's verify window: the last 4 of the committed seq 1..3 followed by path[r]'s inputs
def verify_window(+par: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  last_k(cat([1n, 2n, 3n], seq_of_rows(path(par, r))), 4n)

# the conv window after committing P (count rows): the last 4 of seq 0..3 followed by P's inputs
def commit_window(+P: List<&2, Nat>) -> List<&2, Nat>:
  last_k(cat([0n, 1n, 2n, 3n], seq_of_rows(P)), 4n)

# ---- the served shapes: every parent array with parent[r] < r (7! = 5040)
def ext_one(+k: Nat, +pre: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match k:
    case 0n:
      Nil{}
    case 1n+j:
      List.append(&2, List<&2, Nat>, ext_one(j, pre), [cat(pre, [Nat.sub(k, 1n)])])

def ext_all(xs: List<&2, List<&2, Nat>>, +r: Nat) -> List<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      Nil{}
    case p <> rest:
      List.append(&2, List<&2, Nat>, ext_one(r, p), ext_all(rest, r))

def levels(n: Nat, +r: Nat, xs: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match n:
    case 0n:
      xs
    case 1n+m:
      levels(m, 1n+r, ext_all(xs, r))

def shapes() -> List<&2, List<&2, Nat>>:
  levels(7n, 1n, [[0n]])

def chain() -> List<&2, Nat>:
  [0n, 0n, 1n, 2n, 3n, 4n, 5n, 6n]
