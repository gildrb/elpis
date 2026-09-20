# DFLASH block8 has one anchor and seven proposal comparisons. The balanced
# tree reduces independent summaries; a stopped left side absorbs the right.
# Only qualification/startup emits this CPU table; token tensors stay native.
import Base
import ./range.bend as Range

type Tree is Data:
  Empty{}
  Bit{equal: Bool}
  Fork{left: Tree, right: Tree}

type Summary is Data:
  Full{length: Nat}
  Stopped{accepted: Nat}

def shift(summary: Summary, offset: Nat) -> Summary:
  match summary:
    case Full{length}:
      Full{Nat.add(offset, length)}
    case Stopped{accepted}:
      Stopped{Nat.add(offset, accepted)}

def combine(left: Summary, right: Summary) -> Summary:
  match left:
    case Full{length}:
      shift(right, length)
    case Stopped{accepted}:
      Stopped{accepted}

def leaf(equal: Bool) -> Summary:
  match equal:
    case False{}:
      Stopped{0n}
    case True{}:
      Full{1n}

def summarize(tree: Tree) -> Summary:
  match tree:
    case Empty{}:
      Full{0n}
    case Bit{equal}:
      leaf(equal)
    case Fork{left, right}:
      a b = summarize(left) summarize(right)
      combine(a, b)

def count(summary: Summary) -> Nat:
  match summary:
    case Full{length}:
      length
    case Stopped{accepted}:
      accepted

def accepted(tree: Tree) -> Nat:
  count(summarize(tree))

# The empty eighth leaf is the identity, not an eighth comparison or bonus.
# All three split levels have balanced independent work in this specialization.
def seven(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool) -> Tree:
  Fork{Fork{Fork{Bit{b0}, Bit{b1}}, Fork{Bit{b2}, Bit{b3}}},
    Fork{Fork{Bit{b4}, Bit{b5}}, Fork{Bit{b6}, Empty{}}}}

def low_bit(mask: Nat) -> Bool:
  Nat.is_eq(Nat.mod(mask, 2n), 1n)

def mask_tree(+mask: Nat) -> Tree:
  +m1 = Nat.div(mask, 2n)
  +m2 = Nat.div(m1, 2n)
  +m3 = Nat.div(m2, 2n)
  +m4 = Nat.div(m3, 2n)
  +m5 = Nat.div(m4, 2n)
  m6 = Nat.div(m5, 2n)
  seven(low_bit(mask), low_bit(m1), low_bit(m2), low_bit(m3),
    low_bit(m4), low_bit(m5), low_bit(m6))

def accept_mask(mask: Nat) -> Nat:
  accepted(mask_tree(mask))

# Mask i's least significant bit is candidates[1] == target_top1[0].
# Ascending masks specialize the actual reducer, not a pasted answer table.
def masks() -> List<&2, Nat>:
  Range.tree(7n, 0n)

def decisions(masks: List<&2, Nat>) -> List<&2, Nat>:
  match masks:
    case Nil{}:
      Nil{}
    case mask <> rest:
      accept_mask(mask) <> decisions(rest)

def values() -> List<&2, Nat>:
  decisions(masks())
