# Independent reference for the m16 GEMM work partition. Division-free: iteration x of a
# space of I iterations split over G blocks belongs to block b iff (x + 1) * G lies in
# (b * I, (b + 1) * I], i.e. the real share [b * I / G, (b + 1) * I / G) contains x.
# Owner counts and group contributors are bounded searches over that relation; reductions
# are symbolic sum trees, so a summation order is a term, not a float value.
import Base

# Symbolic fp32 partials: Part{b} is block b's partial tile for a group, Warp{p} is k-phase
# warp p's accumulator; Add{l, r} is one fp32 addition l + r.
type Sum is Data:
  Part{block: Nat}
  Warp{phase: Nat}
  Add{l: Sum, r: Sum}

def owns(+b: Nat, +x: Nat, +I: Nat, +G: Nat) -> Bool:
  Bool.and(Nat.is_lt(Nat.mul(b, I), Nat.mul(1n+x, G)),
    Nat.is_le(Nat.mul(1n+x, G), Nat.mul(1n+b, I)))

def bit(value: Bool) -> Nat:
  match value:
    case True{}:
      1n
    case False{}:
      0n

# Number of blocks b < count that own iteration x.
def owners(+count: Nat, +x: Nat, +I: Nat, +G: Nat) -> Nat:
  match count:
    case 0n:
      0n
    case 1n+b:
      Nat.add(owners(b, x, I, G), bit(owns(b, x, I, G)))

# Block b owns one of the `left` iterations x, x + 1, ...
def owns_some(left: Nat, +x: Nat, +b: Nat, +I: Nat, +G: Nat) -> Bool:
  match left:
    case 0n:
      False{}
    case 1n+rest:
      Bool.or(owns(b, x, I, G), owns_some(rest, 1n+x, b, I, G))

# Block b computes part of group g (iterations g * KT .. g * KT + KT - 1).
def touches(+b: Nat, +g: Nat, +KT: Nat, +I: Nat, +G: Nat) -> Bool:
  owns_some(KT, Nat.mul(g, KT), b, I, G)

# The fixed in-block tree over the four k-phase partials: (p0 + p2) + (p1 + p3).
def tree(p0: Sum, p1: Sum, p2: Sum, p3: Sum) -> Sum:
  Add{Add{p0, p2}, Add{p1, p3}}

def fold_step(hit: Bool, b: Nat, acc: Maybe<&2, Sum>) -> Maybe<&2, Sum>:
  match hit:
    case False{}:
      acc
    case True{}:
      match acc:
        case None{}:
          Some{Part{b}}
        case Some{v}:
          Some{Add{v, Part{b}}}

# Left fold, in ascending block order, of the partials of the `left` blocks b, b + 1, ...
# that touch group g, onto acc (None: nothing summed yet).
def fold_touching(left: Nat, +b: Nat, +g: Nat, +KT: Nat, +I: Nat, +G: Nat,
    acc: Maybe<&2, Sum>) -> Maybe<&2, Sum>:
  match left:
    case 0n:
      acc
    case 1n+rest:
      fold_touching(rest, 1n+b, g, KT, I, G, fold_step(touches(b, g, KT, I, G), b, acc))

# Cross-block reduction of group g over a G-block grid: every touching block's partial,
# summed left to right in ascending block order.
def reduce(+g: Nat, +KT: Nat, +I: Nat, +G: Nat) -> Maybe<&2, Sum>:
  fold_touching(G, 0n, g, KT, I, G, None{})

# Block b has arrived at the group barrier (appears in the arrival sequence).
def arrived(order: List<&2, Nat>, +b: Nat) -> Bool:
  match order:
    case Nil{}:
      False{}
    case a <> rest:
      Bool.or(Nat.is_eq(a, b), arrived(rest, b))

# Every arrival is a block touching group g.
def all_touch(order: List<&2, Nat>, +g: Nat, +KT: Nat, +I: Nat, +G: Nat) -> Bool:
  match order:
    case Nil{}:
      True{}
    case +b <> rest:
      Bool.and(touches(b, g, KT, I, G), all_touch(rest, g, KT, I, G))

# Every block b < count touching group g has arrived.
def all_arrived(+count: Nat, +order: List<&2, Nat>, +g: Nat, +KT: Nat, +I: Nat,
    +G: Nat) -> Bool:
  match count:
    case 0n:
      True{}
    case 1n+b:
      Bool.and(all_arrived(b, order, g, KT, I, G),
        Bool.or(Bool.not(touches(b, g, KT, I, G)), arrived(order, b)))
