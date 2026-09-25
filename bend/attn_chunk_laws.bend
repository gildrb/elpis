# Obligations for the fixed-absolute-chunk verify-attention split/combine partition of ext patch
# 3003 (attn_chunk.bend) against the causal, round-independent reference (attn_chunk_spec.bend).
# Domain: every depth, every q_len, every grid width S >= 1 (the host launches S = max(1, SMs //
# (bsz * kv heads)): 20 on the served target), every chunk >= 1 (the host passes 512), every query
# row qpos < q_len (row_ok), every kv position p, chunk index c, tile index it. The kernels trap
# when n_chunks > max_chunks (attn_chunk_bounds_laws.bend shows the host never lets that happen);
# these laws describe the non-trapping execution. Hypotheses a law does not need are left out.
# Floating point is outside this model: that a tile or chunk contributing no position leaves the
# running (m, l, acc) bit-identical (alpha forced to 1, p = 0) and that the HMMA row slot does not
# change a row's value are properties of the CUDA arithmetic, checked by the GPU invariance gate.
import Base
import ./attn_chunk.bend as Impl
import ./attn_chunk_spec.bend as Spec

# 1. Lanes: the tile-local tokens warp * 8 + 2 t + e of the 8 x 4 x 2 lanes are 0 .. 63, each
# exactly once (64 lanes, every value below 64 once), so a tile stages each of its AV_T = 64
# positions in exactly one lane (tile_visits counts positions, not lanes).
law lanes_once:
  {List.length(&2, Nat, Impl.lanes()) == 64n : Nat} &
  {Spec.all_once(64n, Impl.lanes()) == True{} : Bool}

# 2. Every kv position enters the softmax of verify row qpos exactly once over the live chunks
# c < n_chunks, their tiles and the causal mask when it is causally visible (p <= depth + qpos),
# and never otherwise: no position dropped or double counted by the chunking, the tile tails or
# the mask. With cta_once (each live chunk processed by exactly one CTA iteration) this is
# exactly-once attention over the whole split grid.
law attend_once:
  for +depth: Nat
  for +q_len: Nat
  for +chunk: Nat
  for +qpos: Nat
  for +p: Nat
  for cpos: {Nat.is_lt(0n, chunk) == True{} : Bool}
  for row: {Nat.is_lt(qpos, q_len) == True{} : Bool}
  {Impl.chunks_hits(Impl.live(Nat.add(depth, q_len), chunk), p, Nat.add(depth, q_len), chunk, q_len, qpos) ==
    Spec.once(Spec.sees(p, depth, qpos)) : Nat}

# 3. The CTA chunk loops (CTA x < S processes x, x + S, ... while below n_chunks) store the partial
# block of chunk s exactly once when s < live = n_chunks (the combine reads exactly the chunks
# s < live) and never otherwise: no read of an unwritten partial, no two CTAs writing one block.
law cta_once:
  for +L: Nat
  for +S: Nat
  for +chunk: Nat
  for +s: Nat
  for spos: {Nat.is_lt(0n, S) == True{} : Bool}
  for cpos: {Nat.is_lt(0n, chunk) == True{} : Bool}
  {Impl.writes(S, S, s, L, chunk) == Spec.once(Nat.is_lt(s, Impl.live(L, chunk))) : Nat}

# 4. Row invariance (headline). Everything verify row qpos of the round (depth, q_len) is built
# from is a function of its absolute position a = depth + qpos and chunk alone:
# (a) tile level: tile it of chunk c puts position p into the row (0 unless the kernel runs that
#     tile) exactly when p lies in the absolute tile [c * chunk + 64 it, + 64) of the absolute
#     chunk c and p <= a: chunk boundaries and tile starts are absolute, tiles past the row add
#     nothing;
# (b) chunk level: the partial of chunk c accumulates exactly the positions of absolute chunk c
#     the row sees, each once;
# (c) combine: the chunks the combine merges into the row (read in combine order, the m = -inf
#     ones skipped) are exactly 0 .. a / chunk, in increasing order.
law row_invariant:
  for +depth: Nat
  for +q_len: Nat
  for +chunk: Nat
  for +qpos: Nat
  for +c: Nat
  for +it: Nat
  for +p: Nat
  for cpos: {Nat.is_lt(0n, chunk) == True{} : Bool}
  for row: {Nat.is_lt(qpos, q_len) == True{} : Bool}
  {Impl.tile_hits(c, it, p, Nat.add(depth, q_len), chunk, q_len, qpos) ==
    Spec.once(Spec.abs_visit(chunk, c, it, p, Nat.add(depth, qpos))) : Nat} &
  {Impl.chunk_hits(c, p, Nat.add(depth, q_len), chunk, q_len, qpos) ==
    Spec.once(Spec.abs_in_chunk(chunk, c, p, Nat.add(depth, qpos))) : Nat} &
  {Impl.merged(Nat.add(depth, q_len), chunk, q_len, qpos) == Spec.abs_chunks(chunk, Nat.add(depth, qpos)) : List<&2, Nat>}

# 4'. Two rounds: rows (d1, q1, j1) and (d2, q2, j2) at the same absolute position d1 + j1 ==
# d2 + j2 get identical tile plans, chunk plans and combine plans.
law row_invariant_rounds:
  for +d1: Nat
  for +q1: Nat
  for +j1: Nat
  for +d2: Nat
  for +q2: Nat
  for +j2: Nat
  for +chunk: Nat
  for +c: Nat
  for +it: Nat
  for +p: Nat
  for cpos: {Nat.is_lt(0n, chunk) == True{} : Bool}
  for row1: {Nat.is_lt(j1, q1) == True{} : Bool}
  for row2: {Nat.is_lt(j2, q2) == True{} : Bool}
  for same: {Nat.add(d1, j1) == Nat.add(d2, j2) : Nat}
  {Impl.tile_hits(c, it, p, Nat.add(d1, q1), chunk, q1, j1) == Impl.tile_hits(c, it, p, Nat.add(d2, q2), chunk, q2, j2) : Nat} &
  {Impl.chunk_hits(c, p, Nat.add(d1, q1), chunk, q1, j1) == Impl.chunk_hits(c, p, Nat.add(d2, q2), chunk, q2, j2) : Nat} &
  {Impl.merged(Nat.add(d1, q1), chunk, q1, j1) == Impl.merged(Nat.add(d2, q2), chunk, q2, j2) : List<&2, Nat>}

# 5. The combine's skip test is exact: a chunk the row does not skip holds a position the row sees
# (its first one enters the row once, so its m is finite) ...
law skip_witness:
  for +depth: Nat
  for +q_len: Nat
  for +chunk: Nat
  for +qpos: Nat
  for +s: Nat
  for cpos: {Nat.is_lt(0n, chunk) == True{} : Bool}
  for row: {Nat.is_lt(qpos, q_len) == True{} : Bool}
  for kept: {Impl.row_nonempty(s, chunk, Impl.q_abs(Nat.add(depth, q_len), q_len, qpos)) == True{} : Bool}
  {Impl.chunk_hits(s, Impl.n_start(s, chunk), Nat.add(depth, q_len), chunk, q_len, qpos) == 1n : Nat}

# ... and a skipped chunk puts no position into the row (its partial keeps m = -inf).
law skip_sound:
  for +depth: Nat
  for +q_len: Nat
  for +chunk: Nat
  for +qpos: Nat
  for +s: Nat
  for +p: Nat
  for cpos: {Nat.is_lt(0n, chunk) == True{} : Bool}
  for row: {Nat.is_lt(qpos, q_len) == True{} : Bool}
  for skipped: {Impl.row_nonempty(s, chunk, Impl.q_abs(Nat.add(depth, q_len), q_len, qpos)) == False{} : Bool}
  {Impl.chunk_hits(s, p, Nat.add(depth, q_len), chunk, q_len, qpos) == 0n : Nat}
