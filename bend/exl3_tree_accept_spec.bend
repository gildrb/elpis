# Independent reference for one ExLlamaV3 8-row tree verify round (DESIGN.md
# §2 and §3(d)): the matching-path acceptance and the TreeDesc derivation.
# Rows 0..7 are all verified; row 0 is the anchor; nodes lists rows 1..7 in
# row order as (parent, token); verify lists the target's greedy id of every
# row. Lists are the reference representation only; the production leaf
# (exl3_tree_accept.bend) uses fixed scalar registers and the refinement is
# proved. Model logits, argmax and physical speed are not part of this
# contract.
import Base
import ./exl3_accept_spec.bend as Chain

# count committed tokens, eos ends the job, last is the row of the last
# committed token (the next anchor is verify[last]).
type TreeVerdict is Data:
  TreeVerdict{count: Nat, eos: Bool, last: Nat}

type Node is Data:
  Node{parent: Nat, token: U32}

# The verify id of row i (0 past the end).
def id_at(xs: List<&2, U32>, i: Nat) -> U32:
  match xs:
    case Nil{}:
      0
    case x <> rest:
      match i:
        case 0n:
          x
        case 1n+j:
          id_at(rest, j)

# The row at position i of a row list (0 past the end).
def row_at(xs: List<&2, Nat>, i: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      match i:
        case 0n:
          x
        case 1n+j:
          row_at(rest, j)

# First choice when b holds.
def pick(b: Bool, +r: Nat, rest: Nat) -> Nat:
  match b:
    case True{}:
      r
    case False{}:
      rest

def pick_u32(b: Bool, +x: U32, rest: U32) -> U32:
  match b:
    case True{}:
      x
    case False{}:
      rest

# A node with parent p and token x continues a path ending at cur whose
# verify id is want.
def hit(+p: Nat, +x: U32, +cur: Nat, +want: U32) -> Bool:
  Bool.and(Nat.is_eq(p, cur), U32.is_eq(x, want))

# The lowest row (numbered from row) that is a child of cur carrying want;
# 0 when there is none (row 0 is never a child).
def child(nodes: List<&2, Node>, +row: Nat, +cur: Nat, +want: U32) -> Nat:
  match nodes:
    case Nil{}:
      0n
    case Node{p, x} <> rest:
      pick(hit(p, x, cur, want), row, child(rest, 1n+row, cur, want))

# The token of row r (rows numbered from row; 0 when absent).
def token_at(nodes: List<&2, Node>, +row: Nat, +r: Nat) -> U32:
  match nodes:
    case Nil{}:
      0
    case Node{p, x} <> rest:
      pick_u32(Nat.is_eq(row, r), x, token_at(rest, 1n+row, r))

# The matching path after a row: c is the next row (0 = the path ends there).
# Each step moves to the lowest child whose token equals the verify id of the
# current row. fuel bounds the walk (7 rows follow the root at most).
def walk(fuel: Nat, c: Nat, +nodes: List<&2, Node>, +verify: List<&2, U32>)
  -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match c:
        case 0n:
          Nil{}
        case 1n+cp:
          +r = {1n+cp : Nat}
          r <> walk(f, child(nodes, 1n, r, id_at(verify, r)), nodes, verify)

# The maximal matching path P: the root, then the walk.
def path(+nodes: List<&2, Node>, +verify: List<&2, U32>) -> List<&2, Nat>:
  0n <> walk(7n, child(nodes, 1n, 0n, id_at(verify, 0n)), nodes, verify)

# Linearization of a path: verify ids of its rows, tokens of its non-root rows.
def targets(ps: List<&2, Nat>, +verify: List<&2, U32>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case r <> rest:
      id_at(verify, r) <> targets(rest, verify)

def proposals(ps: List<&2, Nat>, +nodes: List<&2, Node>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case r <> rest:
      token_at(nodes, 1n, r) <> proposals(rest, nodes)

def finish(v: Chain.Verdict, +ps: List<&2, Nat>) -> TreeVerdict:
  match v:
    case Chain.Verdict{+n, e}:
      TreeVerdict{n, e, row_at(ps, Nat.sub(n, 1n))}

# The chain rules (stop, budget, final, mismatch or checkpoint) of the
# reference chain acceptance on the linearized path; last = P[count - 1].
def linear(+ps: List<&2, Nat>, +nodes: List<&2, Node>,
    +verify: List<&2, U32>, +stops: List<&2, U32>, +budget: Nat,
    +checkpoint: Nat) -> TreeVerdict:
  finish(Chain.accept(targets(ps, verify), proposals(List.tail(&2, Nat, ps), nodes),
    stops, budget, checkpoint), ps)

# One tree round: nodes = rows 1..7, verify = rows 0..7.
def accept_tree(+nodes: List<&2, Node>, +verify: List<&2, U32>,
    +stops: List<&2, U32>, +budget: Nat, +checkpoint: Nat) -> TreeVerdict:
  linear(path(nodes, verify), nodes, verify, stops, budget, checkpoint)

# A chain verdict as a tree verdict on the chain shape (last = count - 1).
def from_chain(v: Chain.Verdict) -> TreeVerdict:
  match v:
    case Chain.Verdict{+n, e}:
      TreeVerdict{n, e, Nat.sub(n, 1n)}

def count(v: TreeVerdict) -> Nat:
  match v:
    case TreeVerdict{n, e, l}:
      n

def eos(v: TreeVerdict) -> Bool:
  match v:
    case TreeVerdict{n, e, l}:
      e

def last(v: TreeVerdict) -> Nat:
  match v:
    case TreeVerdict{n, e, l}:
      l

# The parent of row r (rows numbered from row; 0 when absent).
def parent_at(nodes: List<&2, Node>, +row: Nat, +r: Nat) -> Nat:
  match nodes:
    case Nil{}:
      0n
    case Node{p, x} <> rest:
      pick(Nat.is_eq(row, r), p, parent_at(rest, 1n+row, r))

# Row c extends a path ending at row cur: c is one of the rows 1.., its parent
# is cur and its token is cur's verify id.
def extends(+nodes: List<&2, Node>, +verify: List<&2, U32>, +cur: Nat, +c: Nat) -> Bool:
  Bool.and(Bool.and(Nat.is_le(1n, c), Nat.is_le(c, List.length(&2, Node, nodes))),
    hit(parent_at(nodes, 1n, c), token_at(nodes, 1n, c), cur, id_at(verify, cur)))

# No node extends a path ending at cur whose verify id is want.
def none_extends(nodes: List<&2, Node>, +cur: Nat, +want: U32) -> Bool:
  match nodes:
    case Nil{}:
      True{}
    case Node{p, x} <> rest:
      Bool.and(Bool.not(hit(p, x, cur, want)), none_extends(rest, cur, want))

# The rows ps after cur form a matching path: each row extends the previous
# one, and no row extends the last.
def pext(ps: List<&2, Nat>, +nodes: List<&2, Node>, +verify: List<&2, U32>, +cur: Nat) -> Bool:
  match ps:
    case Nil{}:
      none_extends(nodes, cur, id_at(verify, cur))
    case +c <> rest:
      Bool.and(extends(nodes, verify, cur, c), pext(rest, nodes, verify, c))

# ---------------------------------------------------------------------------
# TreeDesc derivation (DESIGN.md §2.2), transcribing TreeDesign's
# prog_bound.py / tree_stats.py descriptor(). ps = parents of rows 1..7.

# The parent of row r (0 for the root).
def parent_of(+ps: List<&2, Nat>, r: Nat) -> Nat:
  match r:
    case 0n:
      0n
    case 1n+j:
      row_at(ps, j)

def keep(b: Bool, +r: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      r <> rest
    case False{}:
      rest

# Children of v in row order (rows numbered from row).
def kids_from(ps: List<&2, Nat>, +row: Nat, +v: Nat) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      Nil{}
    case q <> rest:
      keep(Nat.is_eq(q, v), row, kids_from(rest, 1n+row, v))

def kids(+ps: List<&2, Nat>, +v: Nat) -> List<&2, Nat>:
  kids_from(ps, 1n, v)

def is_leaf(+ps: List<&2, Nat>, +r: Nat) -> Bool:
  List.is_empty(&2, Nat, kids(ps, r))

# Leaf children / inner children of v, in row order.
def split(xs: List<&2, Nat>, +ps: List<&2, Nat>, +want: Bool) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      keep(Bool.not(Bool.xor(is_leaf(ps, c), want)), c, split(rest, ps, want))

def leaf_kids(+ps: List<&2, Nat>, +v: Nat) -> List<&2, Nat>:
  split(kids(ps, v), ps, True{})

def inner_kids(+ps: List<&2, Nat>, +v: Nat) -> List<&2, Nat>:
  split(kids(ps, v), ps, False{})

# Root-to-r ancestor path (path[r] = path[parent[r]] + [r]); fuel bounds it.
def apath(fuel: Nat, +ps: List<&2, Nat>, r: Nat) -> List<&2, Nat>:
  match fuel:
    case 0n:
      [r]
    case 1n+f:
      match r:
        case 0n:
          [0n]
        case 1n+j:
          +r1 = {1n+j : Nat}
          List.append(&2, Nat, apath(f, ps, parent_of(ps, r1)), [r1])

def anc_path(+ps: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  apath(8n, ps, r)

def mask(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      Nat.add(Nat.pow(2n, x), mask(rest))

# The leaf reached from r by repeatedly taking the lowest-row child.
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

def leaf_of(+ps: List<&2, Nat>, +r: Nat) -> Nat:
  descend(8n, kids(ps, r), ps, r)

# Program bytes: op << 4 | row with ADV 0, PEEK 1, RELOAD 2 (0x20), REPLAY 3.
def peek_all(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case c <> rest:
      Nat.add(16n, c) <> peek_all(rest)

# PEEK every leaf child except the last, which is an ADV.
def peek_adv(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +c <> rest:
      match rest:
        case Nil{}:
          [c]
        case d <> more:
          Nat.add(16n, c) <> peek_adv(d <> more)

def replay(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case c <> rest:
      Nat.add(48n, c) <> replay(rest)

# The leaf part of visit(v): with no inner child, PEEK every leaf child but
# the last and ADV the last; otherwise PEEK every leaf child.
def leaf_part(inner: List<&2, Nat>, +leaves: List<&2, Nat>) -> List<&2, Nat>:
  match inner:
    case Nil{}:
      peek_adv(leaves)
    case c <> rest:
      peek_all(leaves)

def visit_body(+ps: List<&2, Nat>, +v: Nat) -> List<&2, Nat>:
  leaf_part(inner_kids(ps, v), leaf_kids(ps, v))

# The inner children of v, in order: ADV c, visit(c), then (unless c is the
# last) RELOAD and REPLAY path[v]. fuel bounds the recursion.
def emit(+fuel: Nat, xs: List<&2, Nat>, +ps: List<&2, Nat>, +v: Nat)
  -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match xs:
        case Nil{}:
          Nil{}
        case +c <> rest:
          match rest:
            case Nil{}:
              c <> List.append(&2, Nat, visit_body(ps, c),
                emit(f, inner_kids(ps, c), ps, c))
            case +d <> more:
              c <> List.append(&2, Nat, visit_body(ps, c),
                List.append(&2, Nat, emit(f, inner_kids(ps, c), ps, c),
                  32n <> List.append(&2, Nat, replay(anc_path(ps, v)),
                    emit(f, d <> more, ps, v))))

def program(+ps: List<&2, Nat>) -> List<&2, Nat>:
  0n <> List.append(&2, Nat, visit_body(ps, 0n), emit(8n, inner_kids(ps, 0n), ps, 0n))

# Fixed-width field: the first n entries, then fill.
def pad(xs: List<&2, Nat>, n: Nat, +fill: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      match n:
        case 0n:
          Nil{}
        case 1n+m:
          fill <> pad(Nil{}, m, fill)
    case x <> rest:
      match n:
        case 0n:
          Nil{}
        case 1n+m:
          x <> pad(rest, m, fill)

def depth(+ps: List<&2, Nat>, +r: Nat) -> Nat:
  Nat.sub(List.length(&2, Nat, anc_path(ps, r)), 1n)

def anc_mask(+ps: List<&2, Nat>, +r: Nat) -> Nat:
  mask(anc_path(ps, r))

def path_row(+ps: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  pad(anc_path(ps, r), 8n, 255n)

def leaf_rows(n: Nat, +ps: List<&2, Nat>, +row: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      keep(is_leaf(ps, row), row, leaf_rows(m, ps, 1n+row))

def leaves(+ps: List<&2, Nat>) -> List<&2, Nat>:
  leaf_rows(8n, ps, 0n)

# kind 0 exactly for the chain shape parent[r] = r - 1.
def chain_from(ps: List<&2, Nat>, +row: Nat) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case q <> rest:
      Bool.and(Nat.is_eq(q, row), chain_from(rest, 1n+row))

def kind_of(chain: Bool) -> Nat:
  match chain:
    case True{}:
      0n
    case False{}:
      1n

def kind(+ps: List<&2, Nat>) -> Nat:
  kind_of(chain_from(ps, 0n))

# The served domain: parent[r] < r for every row r (rows numbered from row).
def legal(ps: List<&2, Nat>, +row: Nat) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case q <> rest:
      Bool.and(Nat.is_lt(q, row), legal(rest, 1n+row))

# The 128 TreeDesc bytes of DESIGN.md §2.2 (parent[0] = -1 = 0xFF).
def derive(+ps: List<&2, Nat>) -> List<&2, Nat>:
  List.concat(&2, Nat, [
    [84n, 1n, 8n, List.length(&2, Nat, leaves(ps)),
      List.length(&2, Nat, program(ps)), kind(ps), 0n, 0n],
    255n <> pad(ps, 7n, 0n),
    [depth(ps, 0n), depth(ps, 1n), depth(ps, 2n), depth(ps, 3n), depth(ps, 4n), depth(ps, 5n), depth(ps, 6n), depth(ps, 7n)],
    [anc_mask(ps, 0n), anc_mask(ps, 1n), anc_mask(ps, 2n), anc_mask(ps, 3n), anc_mask(ps, 4n), anc_mask(ps, 5n), anc_mask(ps, 6n), anc_mask(ps, 7n)],
    [leaf_of(ps, 0n), leaf_of(ps, 1n), leaf_of(ps, 2n), leaf_of(ps, 3n), leaf_of(ps, 4n), leaf_of(ps, 5n), leaf_of(ps, 6n), leaf_of(ps, 7n)],
    pad(leaves(ps), 8n, 255n),
    pad(program(ps), 16n, 255n),
    List.concat(&2, Nat, [path_row(ps, 0n), path_row(ps, 1n), path_row(ps, 2n),
      path_row(ps, 3n), path_row(ps, 4n), path_row(ps, 5n), path_row(ps, 6n),
      path_row(ps, 7n)])])

# ---------------------------------------------------------------------------
# TreeDesc soundness (law derive_sound): the §2.2 properties of a descriptor d
# checked directly against the parent array, independently of how derive
# builds it: fields in place, depth and path by the parent recurrence, masks
# and leaves from the child relation, leaf_of by the lowest-child descent
# with the path-prefix property, and the GDN program by emulation.

def field(+d: List<&2, Nat>, off: Nat, n: Nat) -> List<&2, Nat>:
  List.take(&2, Nat, List.drop(&2, Nat, d, off), n)

# The descriptor's fields, split once: parent, depth, anc_mask, leaf_of
# (8 bytes each), prog (16) and the 8 path rows.
type Parts is Data:
  Parts{par: List<&2, Nat>, dep: List<&2, Nat>, anc: List<&2, Nat>,
    lof: List<&2, Nat>, prog: List<&2, Nat>, paths: List<&2, List<&2, Nat>>}

def parts(+d: List<&2, Nat>) -> Parts:
  Parts{field(d, 8n, 8n), field(d, 16n, 8n), field(d, 24n, 8n), field(d, 32n, 8n),
    field(d, 48n, 16n),
    [field(d, 64n, 8n), field(d, 72n, 8n), field(d, 80n, 8n), field(d, 88n, 8n),
      field(d, 96n, 8n), field(d, 104n, 8n), field(d, 112n, 8n), field(d, 120n, 8n)]}

def nat_eq_list(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      List.is_empty(&2, Nat, ys)
    case x <> rest:
      match ys:
        case Nil{}:
          False{}
        case y <> more:
          Bool.and(Nat.is_eq(x, y), nat_eq_list(rest, more))

def list_at(xs: List<&2, List<&2, Nat>>, i: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      match i:
        case 0n:
          x
        case 1n+j:
          list_at(rest, j)

def has_child(ps: List<&2, Nat>, +v: Nat) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case q <> rest:
      Bool.or(Nat.is_eq(q, v), has_child(rest, v))

def lowest_child(ps: List<&2, Nat>, +row: Nat, +v: Nat) -> Nat:
  match ps:
    case Nil{}:
      0n
    case q <> rest:
      pick(Nat.is_eq(q, v), row, lowest_child(rest, 1n+row, v))

def cut_ff(stop: Bool, +x: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match stop:
    case True{}:
      Nil{}
    case False{}:
      x <> rest

def before_ff(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      cut_ff(Nat.is_eq(x, 255n), x, before_ff(rest))

def prefix_of(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      match ys:
        case Nil{}:
          False{}
        case y <> more:
          Bool.and(Nat.is_eq(x, y), prefix_of(rest, more))

# Row 0: parent 0xFF, depth 0, path [0].
def row_root(+p: Parts) -> Bool:
  match p:
    case Parts{par, dep, anc, lof, prog, paths}:
      Bool.and(Nat.is_eq(row_at(par, 0n), 255n),
        Bool.and(Nat.is_eq(row_at(dep, 0n), 0n),
          nat_eq_list(list_at(paths, 0n), [0n, 255n, 255n, 255n, 255n, 255n, 255n, 255n])))

# Row r >= 1: parent byte, depth = parent's depth + 1, path = the first
# depth[r] bytes of the parent's path (its whole path), then r, then 0xFF.
def row_inner(+p: Parts, +ps: List<&2, Nat>, +r: Nat) -> Bool:
  match p:
    case Parts{+par, +dep, anc, lof, prog, +paths}:
      Bool.and(Nat.is_eq(row_at(par, r), parent_of(ps, r)),
        Bool.and(Nat.is_eq(row_at(dep, r), Nat.add(row_at(dep, parent_of(ps, r)), 1n)),
          nat_eq_list(list_at(paths, r),
            pad(List.append(&2, Nat, List.take(&2, Nat, list_at(paths, parent_of(ps, r)),
              row_at(dep, r)), [r]), 8n, 255n))))

def match_row(r: Nat, +p: Parts, +ps: List<&2, Nat>) -> Bool:
  match r:
    case 0n:
      row_root(p)
    case 1n+rp:
      row_inner(p, ps, 1n+rp)

def descend_rule(inner: Bool, +lof: List<&2, Nat>, +ps: List<&2, Nat>, +r: Nat) -> Nat:
  match inner:
    case True{}:
      row_at(lof, lowest_child(ps, 1n, r))
    case False{}:
      r

# Every row: parent, depth and path by the recurrence; anc_mask the path's
# bit set; leaf_of a leaf whose path extends the row's, reached through the
# lowest child.
def row_ok(+p: Parts, +ps: List<&2, Nat>, +r: Nat) -> Bool:
  match p:
    case Parts{+par, +dep, +anc, +lof, +prog, +paths}:
      +q = {Parts{par, dep, anc, lof, prog, paths} : Parts}
      +lo = row_at(lof, r)
      +path = before_ff(list_at(paths, r))
      Bool.and(match_row(r, q, ps),
        Bool.and(Nat.is_eq(row_at(anc, r), mask(path)),
          Bool.and(Bool.not(has_child(ps, lo)),
            Bool.and(prefix_of(path, before_ff(list_at(paths, lo))),
              Nat.is_eq(lo, descend_rule(has_child(ps, r), lof, ps, r))))))

def rows_ok(n: Nat, +p: Parts, +ps: List<&2, Nat>, +r: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      Bool.and(row_ok(p, ps, r), rows_ok(m, p, ps, 1n+r))

# Leaf rows (no child) ascending.
def childless(n: Nat, +ps: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      keep(Bool.not(has_child(ps, r)), r, childless(m, ps, 1n+r))

# Program emulation: ADV r extends the state and outputs r; PEEK r outputs r
# with the state extended by r, unchanged; RELOAD empties the state; REPLAY r
# extends it. Each output records the row and its state history.
type Out is Data:
  Out{row: Nat, hist: List<&2, Nat>}

def next_state(op: Nat, +row: Nat, +state: List<&2, Nat>) -> List<&2, Nat>:
  match op:
    case 0n:
      List.append(&2, Nat, state, [row])
    case 1n+a:
      match a:
        case 0n:
          state
        case 1n+b:
          match b:
            case 0n:
              Nil{}
            case 1n+c:
              List.append(&2, Nat, state, [row])

def next_outs(op: Nat, +row: Nat, +state: List<&2, Nat>, outs: List<&2, Out>) -> List<&2, Out>:
  match op:
    case 0n:
      Out{row, List.append(&2, Nat, state, [row])} <> outs
    case 1n+a:
      match a:
        case 0n:
          Out{row, List.append(&2, Nat, state, [row])} <> outs
        case 1n+b:
          outs

def emulate(bs: List<&2, Nat>, +state: List<&2, Nat>, outs: List<&2, Out>) -> List<&2, Out>:
  match bs:
    case Nil{}:
      outs
    case +b <> rest:
      emulate(rest, next_state(Nat.div(b, 16n), Nat.mod(b, 16n), state),
        next_outs(Nat.div(b, 16n), Nat.mod(b, 16n), state, outs))

# Valid op bytes: op <= 3, row <= 7, RELOAD exactly 0x20.
def op_ok(+b: Nat) -> Bool:
  Bool.and(Nat.is_le(Nat.div(b, 16n), 3n),
    Bool.and(Nat.is_le(Nat.mod(b, 16n), 7n),
      Bool.or(Nat.is_ne(Nat.div(b, 16n), 2n), Nat.is_eq(b, 32n))))

def ops_ok(bs: List<&2, Nat>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case +b <> rest:
      Bool.and(op_ok(b), ops_ok(rest))

def all_ff(bs: List<&2, Nat>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case b <> rest:
      Bool.and(Nat.is_eq(b, 255n), all_ff(rest))

def keep_hist(b: Bool, +h: List<&2, Nat>, rest: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match b:
    case True{}:
      h <> rest
    case False{}:
      rest

def outs_of(outs: List<&2, Out>, +r: Nat) -> List<&2, List<&2, Nat>>:
  match outs:
    case Nil{}:
      Nil{}
    case Out{row, +hist} <> rest:
      keep_hist(Nat.is_eq(row, r), hist, outs_of(rest, r))

# Row r is output exactly once, with its path as the state history.
def once(hs: List<&2, List<&2, Nat>>, +path: List<&2, Nat>) -> Bool:
  match hs:
    case Nil{}:
      False{}
    case h <> rest:
      Bool.and(nat_eq_list(h, path), List.is_empty(&2, List<&2, Nat>, rest))

def outs_ok(n: Nat, +outs: List<&2, Out>, +paths: List<&2, List<&2, Nat>>, +r: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      Bool.and(once(outs_of(outs, r), before_ff(list_at(paths, r))), outs_ok(m, outs, paths, 1n+r))

def prog_ok(+np: Nat, +p: Parts) -> Bool:
  match p:
    case Parts{par, dep, anc, lof, +bs, +paths}:
      Bool.and(Nat.is_le(np, 16n),
        Bool.and(ops_ok(List.take(&2, Nat, bs, np)),
          Bool.and(all_ff(List.drop(&2, Nat, bs, np)),
            outs_ok(8n, emulate(List.take(&2, Nat, bs, np), Nil{}, Nil{}), paths, 0n))))

def sound(+ps: List<&2, Nat>, +d: List<&2, Nat>) -> Bool:
  +lv = childless(8n, ps, 0n)
  +p = parts(d)
  Bool.and(Nat.is_eq(List.length(&2, Nat, d), 128n),
    Bool.and(nat_eq_list(field(d, 0n, 3n), [84n, 1n, 8n]),
      Bool.and(nat_eq_list(field(d, 5n, 3n), [kind(ps), 0n, 0n]),
        Bool.and(Nat.is_eq(row_at(d, 3n), List.length(&2, Nat, lv)),
          Bool.and(nat_eq_list(field(d, 40n, 8n), pad(lv, 8n, 255n)),
            Bool.and(rows_ok(8n, p, ps, 0n), prog_ok(row_at(d, 4n), p)))))))
