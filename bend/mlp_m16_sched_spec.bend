# Independent reference vocabulary for the ext 8201 fused-MLP schedule (bend/mlp_m16_sched.bend):
# the synchronisation events of one block, and semantic counts over the whole grid (signals and
# waits per counter, touched pairs, membership, duplicates). The counts scan the event lists; they
# do not use the table formulas (8 * nc, 8 * k_P, ...) that the laws compare them with.
import Base
import ./gemm_m16_partition_spec.bend as PSpec

# Kernel counters: C1{g} = cnt1[g] (g < 68: gate groups 0..33, up groups 34..67); C2{p} = cnt2[p]
# (p < 34 pairs).
type Ctr is Data:
  C1{g: Nat}
  C2{p: Nat}

# One synchronisation event of a block at a level (the kernel's program order is level order):
# Sig adds amt to counter c (release); Wait blocks until c reaches its expected count. mult is the
# number of passes the wait counts on the counter's pass counter (8 for a finisher block's cnt1
# wait: thread 0 waits once and adds one pass per warp; 1 for a thread-0 cnt2 wait).
type Ev is Data:
  Sig{c: Ctr, amt: Nat, lvl: Nat}
  Wait{c: Ctr, mult: Nat, lvl: Nat}

# 1 for True, 0 for False (gemm_m16_partition_spec's bit, so counts compose with its laws).
def bit(value: Bool) -> Nat:
  PSpec.bit(value)

def ctr_eq(a: Ctr, b: Ctr) -> Bool:
  match a b:
    case C1{x} C1{y}:
      Nat.is_eq(x, y)
    case C2{x} C2{y}:
      Nat.is_eq(x, y)
    case _ _:
      False{}

# Total amount signalled on counter c by one event list.
def sig_amount(evs: List<&2, Ev>, +c: Ctr) -> Nat:
  match evs:
    case Nil{}:
      0n
    case ev <> rest:
      match ev:
        case Sig{d, amt, l}:
          Nat.add(Nat.mul(bit(ctr_eq(d, c)), amt), sig_amount(rest, c))
        case Wait{d, m, l}:
          sig_amount(rest, c)

# Total waiters (weighted by mult) on counter c in one event list.
def wait_amount(evs: List<&2, Ev>, +c: Ctr) -> Nat:
  match evs:
    case Nil{}:
      0n
    case ev <> rest:
      match ev:
        case Sig{d, amt, l}:
          wait_amount(rest, c)
        case Wait{d, m, l}:
          Nat.add(Nat.mul(bit(ctr_eq(d, c)), m), wait_amount(rest, c))

def lvl(ev: Ev) -> Nat:
  match ev:
    case Sig{c, a, l}:
      l
    case Wait{c, m, l}:
      l

# Levels never decrease along the list, starting from at least `from`.
def ordered(evs: List<&2, Ev>, +from: Nat) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case ev <> rest:
      +l = lvl(ev)
      Bool.and(Nat.is_le(from, l), ordered(rest, l))

# Every signal on counter c in the list has level < bound.
def sigs_below(evs: List<&2, Ev>, +c: Ctr, +bound: Nat) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case ev <> rest:
      match ev:
        case Sig{d, a, l}:
          Bool.and(Bool.or(Bool.not(ctr_eq(d, c)), Nat.is_lt(l, bound)),
            sigs_below(rest, c, bound))
        case Wait{d, m, l}:
          sigs_below(rest, c, bound)

# Waits on counter c in the list sit at levels >= bound.
def waits_from(evs: List<&2, Ev>, +c: Ctr, +bound: Nat) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case ev <> rest:
      match ev:
        case Sig{d, a, l}:
          waits_from(rest, c, bound)
        case Wait{d, m, l}:
          Bool.and(Bool.or(Bool.not(ctr_eq(d, c)), Nat.is_le(bound, l)),
            waits_from(rest, c, bound))

# x occurs in the list.
def member(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), member(rest, x))

# Number of occurrences of x in the list.
def occurs(xs: List<&2, Nat>, +x: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case y <> rest:
      Nat.add(bit(Nat.is_eq(y, x)), occurs(rest, x))

# No value occurs twice.
def nodup(+xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case y <> rest:
      Bool.and(Bool.not(member(rest, y)), nodup(rest))

# Some iteration it, it + 1, ... (`left` of them) lies in down pair p (k-tile it mod KT in
# [p * PK, (p + 1) * PK)), stated without division.
def touches_pair(left: Nat, +it: Nat, +p: Nat, +KT: Nat, +PK: Nat) -> Bool:
  match left:
    case 0n:
      False{}
    case 1n+rest:
      Bool.or(Bool.and(Nat.is_le(Nat.mul(p, PK), Nat.mod(it, KT)),
          Nat.is_lt(Nat.mod(it, KT), Nat.mul(1n+p, PK))),
        touches_pair(rest, 1n+it, p, KT, PK))
