# Independent reference for the ext 2105 / 8205 slot-weighted partition. Block b's weight is
# w0 if b < nsm, else w1; wsum(b) is the weight of the blocks before b, built by recursion (not by
# the min/max closed form of the implementation). Ownership is division-free: iteration x of a space
# of `total` iterations belongs to block b iff (x + 1) * WG lies in (total * wsum(b), total * wsum(b + 1)],
# WG = wsum(G), i.e. the real share [total wsum(b) / WG, total wsum(b + 1) / WG) contains x. The owner
# search, owner counts and group contributors are bounded searches over that relation.
import Base
import ./gemm_m16_partition_spec.bend as V2Spec

def weight(below: Bool, +w0: Nat, +w1: Nat) -> Nat:
  match below:
    case True{}:
      w0
    case False{}:
      w1

# Total weight of the blocks 0 .. b - 1.
def wsum(+b: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Nat:
  match b:
    case 0n:
      0n
    case 1n+c:
      Nat.add(wsum(c, nsm, w0, w1), weight(Nat.is_lt(c, nsm), w0, w1))

# Iterations before block b's share end at or below x: total * wsum(b) < (x + 1) * WG.
def starts_by(+b: Nat, +x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Bool:
  Nat.is_lt(Nat.mul(total, wsum(b, nsm, w0, w1)), Nat.mul(1n+x, wsum(G, nsm, w0, w1)))

# Block b owns iteration x.
def owns(+b: Nat, +x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Bool:
  Bool.and(starts_by(b, x, total, G, nsm, w0, w1),
    Bool.not(starts_by(1n+b, x, total, G, nsm, w0, w1)))

# Number of blocks b < count that own iteration x.
def owners(+count: Nat, +x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Nat:
  match count:
    case 0n:
      0n
    case 1n+b:
      Nat.add(owners(b, x, total, G, nsm, w0, w1), V2Spec.bit(owns(b, x, total, G, nsm, w0, w1)))

def search.pick(hit: Bool, +b: Nat, +rest: Nat) -> Nat:
  match hit:
    case True{}:
      b
    case False{}:
      rest

# The largest b < count whose share starts at or below x (0 if none): a downward search.
def search(+count: Nat, +x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Nat:
  match count:
    case 0n:
      0n
    case 1n+b:
      search.pick(starts_by(b, x, total, G, nsm, w0, w1), b, search(b, x, total, G, nsm, w0, w1))

# Block b owns one of the `left` iterations x, x + 1, ...
def owns_some(left: Nat, +x: Nat, +b: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat)
    -> Bool:
  match left:
    case 0n:
      False{}
    case 1n+rest:
      Bool.or(owns(b, x, total, G, nsm, w0, w1), owns_some(rest, 1n+x, b, total, G, nsm, w0, w1))

# Block b computes part of group g (iterations g * KT .. g * KT + KT - 1).
def touches(+b: Nat, +g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat)
    -> Bool:
  owns_some(KT, Nat.mul(g, KT), b, total, G, nsm, w0, w1)

# Number of blocks b < count that touch group g (each flushes one partial slot of g).
def touch_count(+count: Nat, +g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat,
    +w1: Nat) -> Nat:
  match count:
    case 0n:
      0n
    case 1n+b:
      Nat.add(touch_count(b, g, KT, total, G, nsm, w0, w1),
        V2Spec.bit(touches(b, g, KT, total, G, nsm, w0, w1)))
