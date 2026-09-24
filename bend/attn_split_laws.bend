# Obligations for the verify-attention split/combine partition (attn_split.bend) against the
# causal reference (attn_split_spec.bend). Domain: any depth, any q_len, any split count S >= 1
# (the served launch uses S = 20 with q_len = 8), any query row qpos < q_len, any kv position p.
import Base
import ./attn_split.bend as Impl
import ./attn_split_spec.bend as Spec

# Every kv position enters the softmax of verify row qpos in exactly one of the S split CTAs when
# it is causally visible (p <= depth + qpos), and in none otherwise: no position is dropped or
# double counted by the partition, the tile tails or the causal mask.
law attend_once:
  for +depth: Nat
  for +q_len: Nat
  for +S: Nat
  for +qpos: Nat
  for +p: Nat
  for spos: {Nat.is_lt(0n, S) == True{} : Bool}
  for row: {Nat.is_lt(qpos, q_len) == True{} : Bool}
  {Impl.hits(S, p, Nat.add(depth, q_len), S, q_len, qpos) == Spec.once(Spec.sees(p, depth, qpos)) : Nat}

# The combine reads split s (s < live, in the fixed order 0 .. live - 1 of Impl.combine_order)
# exactly when the split kernel ran that CTA and wrote its partial: no read of an unwritten
# partial, no written partial left out. L = depth + q_len >= 1 always holds for a verify round.
law combine_reads_written:
  for +L: Nat
  for +S: Nat
  for +i: Nat
  for spos: {Nat.is_lt(0n, S) == True{} : Bool}
  for lpos: {Nat.is_lt(0n, L) == True{} : Bool}
  {Nat.is_lt(i, Impl.live(L, S)) == Impl.runs(i, L, S) : Bool}

# The combine never reads past the launched grid: live <= S.
law live_in_grid:
  for +L: Nat
  for +S: Nat
  for spos: {Nat.is_lt(0n, S) == True{} : Bool}
  for lpos: {Nat.is_lt(0n, L) == True{} : Bool}
  {Nat.is_le(Impl.live(L, S), S) == True{} : Bool}
