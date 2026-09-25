# Obligations for the strided absolute-tile verify-attention split/combine partition of ext patch
# 3006 (attn_stride.bend) against the causal, round-independent reference (attn_stride_spec.bend).
# Domain: every depth, every q_len, every grid width S >= 1 (the host launches S = max(1, SMs //
# kv heads): 20 on the served target, whatever bsz or depth), every query row qpos < q_len
# (row_ok), every kv position p, CTA / slot index x, tile iteration it. The split kernel traps
# when L > num_pages * 256 (attn_stride_bounds_laws.bend); these laws describe the non-trapping
# execution. Hypotheses a law does not need are left out. Floating point is outside this model:
# that a tile contributing no position leaves the running (m, l, acc) bit-identical (alpha forced
# to 1, p = 0) and that the HMMA row slot does not change a row's value are properties of the CUDA
# arithmetic, checked by the GPU invariance gate.
import Base
import ./attn_stride.bend as Impl
import ./attn_stride_spec.bend as Spec

# 1. Lanes: the tile-local tokens warp * 8 + 2 t + e of the 8 x 4 x 2 lanes are 0 .. 63, each
# exactly once, so a tile stages each of its AV_T = 64 positions in exactly one lane (tile_visits
# counts positions, not lanes).
law lanes_once:
  {List.length(&2, Nat, Impl.lanes()) == 64n : Nat} &
  {Spec.all_once(64n, Impl.lanes()) == True{} : Bool}

# 2. Every kv position enters the softmax of verify row qpos exactly once over the S CTAs, their
# strided tiles and the causal mask when it is causally visible (p <= depth + qpos), and never
# otherwise: no position dropped or double counted by the striding, the early return, the tile
# tails or the mask.
law attend_once:
  for +depth: Nat
  for +q_len: Nat
  for +S: Nat
  for +qpos: Nat
  for +p: Nat
  for spos: {Nat.is_lt(0n, S) == True{} : Bool}
  for row: {Nat.is_lt(qpos, q_len) == True{} : Bool}
  {Impl.ctas_hits(S, p, Nat.add(depth, q_len), S, q_len, qpos) == Spec.once(Spec.sees(p, depth, qpos)) : Nat}

# 3. Partial slots: over the S CTAs, slot s is stored exactly once when s < live = min(S, n_tiles)
# (the combine reads exactly the slots s < live) and never otherwise: no read of an unwritten
# slot, no two CTAs writing one slot.
law slot_once:
  for +L: Nat
  for +S: Nat
  for +s: Nat
  {Impl.writes(S, s, L) == Spec.once(Nat.is_lt(s, Impl.live_slots(Impl.live_tiles(L), S))) : Nat}

# 4. Row invariance (headline). Everything verify row qpos of the round (depth, q_len) is built
# from is a function of its absolute position a = depth + qpos and S alone:
# (a) tile level: iteration it of CTA x < S puts position p into the row (0 unless the kernel runs
#     that tile) exactly when p lies in the absolute tile x + it S and p <= a: tiles past the row
#     add nothing;
# (b) slot level: CTA x's running state accumulates exactly the positions p <= a whose absolute
#     tile p / 64 is x mod S, each once;
# (c) combine: the slots the combine merges into the row (read in slot order, the m = -inf ones
#     skipped) are exactly 0 .. min(S - 1, a / 64), in increasing order.
law row_invariant:
  for +depth: Nat
  for +q_len: Nat
  for +S: Nat
  for +qpos: Nat
  for +x: Nat
  for +it: Nat
  for +p: Nat
  for xb: {Nat.is_lt(x, S) == True{} : Bool}
  for row: {Nat.is_lt(qpos, q_len) == True{} : Bool}
  {Impl.tile_hits(x, it, p, Nat.add(depth, q_len), S, q_len, qpos) ==
    Spec.once(Spec.abs_visit(S, x, it, p, Nat.add(depth, qpos))) : Nat} &
  {Impl.cta_hits(x, p, Nat.add(depth, q_len), S, q_len, qpos) ==
    Spec.once(Spec.abs_in_slot(S, x, p, Nat.add(depth, qpos))) : Nat} &
  {Impl.merged(Nat.add(depth, q_len), S, q_len, qpos) == Spec.abs_slots(S, Nat.add(depth, qpos)) : List<&2, Nat>}

# 4'. Two rounds: rows (d1, q1, j1) and (d2, q2, j2) at the same absolute position d1 + j1 ==
# d2 + j2 get identical tile plans, slot plans and combine plans.
law row_invariant_rounds:
  for +d1: Nat
  for +q1: Nat
  for +j1: Nat
  for +d2: Nat
  for +q2: Nat
  for +j2: Nat
  for +S: Nat
  for +x: Nat
  for +it: Nat
  for +p: Nat
  for xb: {Nat.is_lt(x, S) == True{} : Bool}
  for row1: {Nat.is_lt(j1, q1) == True{} : Bool}
  for row2: {Nat.is_lt(j2, q2) == True{} : Bool}
  for same: {Nat.add(d1, j1) == Nat.add(d2, j2) : Nat}
  {Impl.tile_hits(x, it, p, Nat.add(d1, q1), S, q1, j1) == Impl.tile_hits(x, it, p, Nat.add(d2, q2), S, q2, j2) : Nat} &
  {Impl.cta_hits(x, p, Nat.add(d1, q1), S, q1, j1) == Impl.cta_hits(x, p, Nat.add(d2, q2), S, q2, j2) : Nat} &
  {Impl.merged(Nat.add(d1, q1), S, q1, j1) == Impl.merged(Nat.add(d2, q2), S, q2, j2) : List<&2, Nat>}

# 5. The combine's skip test is exact: a slot the row does not skip holds a position the row sees
# (its first tile's first position enters the row once, so its m is finite) ...
law skip_witness:
  for +depth: Nat
  for +q_len: Nat
  for +S: Nat
  for +qpos: Nat
  for +s: Nat
  for sb: {Nat.is_lt(s, S) == True{} : Bool}
  for row: {Nat.is_lt(qpos, q_len) == True{} : Bool}
  for kept: {Impl.row_nonempty(s, Impl.q_abs(Nat.add(depth, q_len), q_len, qpos)) == True{} : Bool}
  {Impl.cta_hits(s, Nat.mul(s, 64n), Nat.add(depth, q_len), S, q_len, qpos) == 1n : Nat}

# ... and a skipped slot puts no position into the row (its partial keeps m = -inf).
law skip_sound:
  for +depth: Nat
  for +q_len: Nat
  for +S: Nat
  for +qpos: Nat
  for +s: Nat
  for +p: Nat
  for row: {Nat.is_lt(qpos, q_len) == True{} : Bool}
  for skipped: {Impl.row_nonempty(s, Impl.q_abs(Nat.add(depth, q_len), q_len, qpos)) == False{} : Bool}
  {Impl.cta_hits(s, p, Nat.add(depth, q_len), S, q_len, qpos) == 0n : Nat}
