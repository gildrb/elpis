# Selector-order and speculative-window lessons from the validated EXL3
# native DFlash2 stack (r0b0tlab), expressed as executable reference code.
# First-max ties, a balanced parallel reduction, and the no-double-crop
# window arithmetic.
import Base
import ./range.bend as Range

type Score is Data:
  Score{+index: Nat, +value: Nat}

def better_pick(flag: Bool, a: Score, b: Score) -> Score:
  match flag:
    case True{}:
      b
    case False{}:
      a

# First max on ties: the earlier index wins. Mirrors the CUDA selector walk's
# "thread 0 argmaxes k scores, first max on ties" and the fused top-k's
# "ties resolve to the lowest lane / earliest element".
def better(a: Score, b: Score) -> Score:
  Score{ai, av} = a
  Score{bi, bv} = b
  better_pick(Nat.is_lt(av, bv), a, b)

# Sequential left fold in index order. The shrinking list leads so every
# recursive call terminates.
def walk_seq(xs: List<&2, Score>, best: Score) -> Score:
  match xs:
    case Nil{}:
      best
    case head <> rest:
      walk_seq(rest, better(best, head))

type Tree is Data:
  Leaf{+index: Nat}
  Node{left: Tree, right: Tree}

# Balanced two-sided build with independent parallel subtrees; scores are
# derived at the leaves so the shape carries no shared affine input.
def build(+depth: Nat, +start: Nat) -> Tree:
  match depth:
    case 0n:
      Leaf{start}
    case 1n+p:
      left right = build(p, start) build(p, Nat.add(Range.width(p), start))
      Node{left, right}

def score(+index: Nat) -> Nat:
  index

def reduce(tree: Tree) -> Score:
  match tree:
    case Leaf{index}:
      Score{index, score(index)}
    case Node{left, right}:
      better(reduce(left), reduce(right))

# Draft round arithmetic: block 8 emits exactly 7 proposals, and each verify
# round commits the accepted proposals plus exactly one target token.
def block_size() -> Nat:
  8n

def proposals() -> Nat:
  Nat.sub(block_size(), 1n)

def window_rows() -> Nat:
  Nat.add(proposals(), 1n)

# Acceptance bookkeeping (their scripts/acceptance_check.py): every round
# emits accepted drafts plus one target token, so rounds = new - accepted.
def rounds_pick(flag: Bool, +new_tokens: Nat, +accepted: Nat) -> Maybe<&2, Nat>:
  match flag:
    case True{}:
      Some{Nat.sub(new_tokens, accepted)}
    case False{}:
      None{}

def rounds(+new_tokens: Nat, +accepted: Nat) -> Maybe<&2, Nat>:
  rounds_pick(Nat.is_lt(accepted, new_tokens), new_tokens, accepted)
