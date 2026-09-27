# Round-level model of greedy tree verification (8 rows, DESIGN.md §4.1), for
# the tree speculation-invariance laws (spec_inv_tree_laws.bend; greedy
# reference: spec_inv_spec.bend).
#
# The target is abstracted to its per-row output, as in spec_inv.bend: row(p, r)
# is the argmax token of a row whose absolute prefix is p when that row is row r
# of its round. In a tree round, row 0's input is the anchor and row r >= 1 is
# the drafted node r with parent q_r < r and token x_r; row r's prefix is the
# committed sequence followed by the tokens of r's ancestors below the root and
# r itself (seq ++ tokens[path[r][1..]]). The verdict is the tree acceptance
# reference (exl3_tree_accept_spec.bend, proven equal to the executed leaf by
# its tree_refinement law) with the job's remaining budget and the device
# checkpoint; the device state then advances by the advance kernel of
# exl3_round.bend with the 7-token window, and the host emits the verify ids of
# the committed rows (the first count rows of the matching path). Every tree of
# every round is arbitrary (any legal shape, any tokens), so a law quantified
# over them covers every tree drafter. This is a proof model (lists), not a
# shipped artifact.
import Base
import ./exl3_tree_accept_spec.bend as Tree
import ./exl3_round.bend as Round
import ./exl3_round_spec.bend as RoundSpec
import ./spec_inv.bend as Chain

# One round's draft tree: parents q1..q7 (q_r < r) and tokens x1..x7 of rows 1..7.
type Draft is Data:
  Draft{q1: Nat, q2: Nat, q3: Nat, q4: Nat, q5: Nat, q6: Nat, q7: Nat,
    x1: U32, x2: U32, x3: U32, x4: U32, x5: U32, x6: U32, x7: U32}

def nodes(t: Draft) -> List<&2, Tree.Node>:
  match t:
    case Draft{q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7}:
      [Tree.Node{q1, x1}, Tree.Node{q2, x2}, Tree.Node{q3, x3}, Tree.Node{q4, x4},
        Tree.Node{q5, x5}, Tree.Node{q6, x6}, Tree.Node{q7, x7}]

def legal(t: Draft) -> Bool:
  match t:
    case Draft{q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7}:
      Tree.legal([q1, q2, q3, q4, q5, q6, q7], 1n)

# The tokens of r's ancestors below the root and of r itself, root first
# (tokens[path[r][1..]]); fuel bounds the parent chain (depth <= 7 when legal).
def toks(fuel: Nat, +nodes: List<&2, Tree.Node>, r: Nat) -> List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match r:
        case 0n:
          Nil{}
        case 1n+j:
          +c = {1n+j : Nat}
          List.append(&2, U32, toks(f, nodes, Tree.parent_at(nodes, 1n, c)), [Tree.token_at(nodes, 1n, c)])

def prefix(+seq: List<&2, U32>, +nodes: List<&2, Tree.Node>, +r: Nat) -> List<&2, U32>:
  List.append(&2, U32, seq, toks(8n, nodes, r))

# The verify ids of a tree round after the committed sequence seq.
def verify(~row: List<&2, U32> -> Nat -> U32, +seq: List<&2, U32>, +nodes: List<&2, Tree.Node>)
  -> List<&2, U32>:
  [row(prefix(seq, nodes, 0n), 0n), row(prefix(seq, nodes, 1n), 1n), row(prefix(seq, nodes, 2n), 2n),
    row(prefix(seq, nodes, 3n), 3n), row(prefix(seq, nodes, 4n), 4n), row(prefix(seq, nodes, 5n), 5n),
    row(prefix(seq, nodes, 6n), 6n), row(prefix(seq, nodes, 7n), 7n)]

# The verify ids of the matching path's rows (committed: the first count of them).
def path_ids(+verify: List<&2, U32>, +nodes: List<&2, Tree.Node>) -> List<&2, U32>:
  Tree.targets(Tree.path(nodes, verify), verify)

# One tree round: verify, accept, advance the device state (window 7), emit
# the committed rows' verify ids (nothing once the job has stopped).
def round(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>,
    +base: Nat, +interval: Nat, +t: Draft, r: Chain.Run) -> Chain.Run:
  match r:
    case Chain.Run{+st, +o}:
      +ns = nodes(t)
      +vs = verify(~row, List.append(&2, U32, prompt, o), ns)
      +v = Tree.accept_tree(ns, vs, stops, Round.budget(st), Round.checkpoint_of(st))
      Chain.Run{Round.advance(Tree.count(v), Tree.eos(v), 7n, base, interval, st),
        List.append(&2, U32, o, RoundSpec.committed(path_ids(vs, ns), Tree.count(v), Round.stopped(st)))}

def run(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>,
    +base: Nat, +interval: Nat, trees: List<&2, Draft>, r: Chain.Run) -> Chain.Run:
  match trees:
    case Nil{}:
      r
    case +t <> rest:
      run(~row, prompt, stops, base, interval, rest, round(~row, prompt, stops, base, interval, t, r))

def all_legal(trees: List<&2, Draft>) -> Bool:
  match trees:
    case Nil{}:
      True{}
    case t <> rest:
      Bool.and(legal(t), all_legal(rest))

# A job: a running device state with nothing emitted yet, then the tree rounds.
def job(~row: List<&2, U32> -> Nat -> U32, +prompt: List<&2, U32>, +stops: List<&2, U32>,
    +base: Nat, +interval: Nat, trees: List<&2, Draft>, +position: Nat, +budget: Nat,
    +anchor: Nat, +checkpoint: Nat) -> Chain.Run:
  run(~row, prompt, stops, base, interval, trees,
    Chain.Run{Round.State{position, budget, anchor, checkpoint, False{}}, Nil{}})
