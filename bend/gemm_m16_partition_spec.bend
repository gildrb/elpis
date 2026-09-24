# Independent reference for the m16 GEMM (patch 2001 v2) work partition. Division-free
# ownership: iteration x of a space of I iterations split over G blocks belongs to block b iff
# (x + 1) * G lies in (b * I, (b + 1) * I], i.e. the real share [b * I / G, (b + 1) * I / G)
# contains x. Owner counts and group contributors are bounded searches over that relation; a
# block's main loop is an event list; reductions are symbolic sum trees, so a summation order
# is a term, not a float value.
import Base

# Symbolic fp32 partials: Part{b} is block b's partial tile for a group; Add{l, r} is one fp32
# addition l + r.
type Sum is Data:
  Part{block: Nat}
  Add{l: Sum, r: Sum}

# A finisher job (K:353-357): group g, token row r, 128-column chunk ch of the 512-column group.
type Job is Data:
  Job{g: Nat, r: Nat, ch: Nat}

# Row-major job numbering over (group, row < m, chunk < 4).
def encode(j: Job, +m: Nat) -> Nat:
  match j:
    case Job{g, r, ch}:
      Nat.add(Nat.mul(Nat.add(Nat.mul(g, m), r), 4n), ch)

# The job is one of the groups * m * 4 real jobs.
def job_ok(j: Job, +groups: Nat, +m: Nat) -> Bool:
  match j:
    case Job{g, r, ch}:
      Bool.and(Nat.is_lt(g, groups), Bool.and(Nat.is_lt(r, m), Nat.is_lt(ch, 4n)))

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

# Events of one block's main loop: Tile{g, it} consumes iteration it (k-tile of group g) into
# the accumulators of group g; Flush{g} writes the accumulated partial of group g to its slot.
type Ev is Data:
  Tile{g: Nat, it: Nat}
  Flush{g: Nat}

def trace.flush(last: Bool, +g: Nat, rest: List<&2, Ev>) -> List<&2, Ev>:
  match last:
    case True{}:
      Flush{g} <> rest
    case False{}:
      rest

# Intended main loop over the `left` iterations it, it + 1, ... of a range ending at e: each
# iteration in ascending order, tagged with its group it / KT, and a flush of that group right
# after its last iteration in the range (the range ends, or the next iteration starts a group).
def trace(left: Nat, +it: Nat, +e: Nat, +KT: Nat) -> List<&2, Ev>:
  match left:
    case 0n:
      Nil{}
    case 1n+rest:
      Tile{Nat.div(it, KT), it} <> trace.flush(
        Bool.or(Nat.is_eq(1n+it, e), Nat.is_eq(Nat.mod(1n+it, KT), 0n)), Nat.div(it, KT),
        trace(rest, 1n+it, e, KT))

def is_flush(+g: Nat, ev: Ev) -> Bool:
  match ev:
    case Tile{h, it}:
      False{}
    case Flush{h}:
      Nat.is_eq(h, g)

# Number of flushes of group g in an event list.
def flushes(evs: List<&2, Ev>, +g: Nat) -> Nat:
  match evs:
    case Nil{}:
      0n
    case ev <> rest:
      Nat.add(bit(is_flush(g, ev)), flushes(rest, g))

# x occurs in the list.
def member(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), member(rest, x))

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
