# Obligations for the tile schedule of the ext 3010 prefill attention kernel (pattn_sched.bend) against
# causal attention (pattn_sched_spec.bend). Domain: every chunk of q_len rows over L >= q_len keys, every
# query block qb and thread row r < 16 with q_pos(qb, r) = 16 qb + r < q_len, every tile iteration it and
# key p. The GQA (head, position) mapping and the MMA span boundaries are covered separately. Floating
# point is outside this model (span accumulation precision is measured by the GPU numerics gates).
import Base
import ./pattn_sched.bend as P
import ./pattn_sched_spec.bend as Spec

# 1. Lanes: the tile-local key columns 8 nt + 2 t + (e & 1) of one thread row are 0 .. 31, each exactly
# once, so tile it stages each key n0 .. n0 + 31 in exactly one (nt, t, e) slot of the row.
law lanes_once:
  {List.length(&2, Nat, P.lane_cols(4n)) == 32n : Nat} &
  {Spec.all_once(32n, P.lane_cols(4n)) == True{} : Bool}

# 2. Every causally visible key enters row (qb, r) in its own tile p / 32 exactly when the row sees it:
# the tile loop bound, the maskless interior tiles and the boundary mask together drop nothing and add
# nothing.
law attend_once:
  for +L: Nat
  for +q: Nat
  for +qb: Nat
  for +r: Nat
  for +p: Nat
  for rb: {Nat.is_lt(r, 16n) == True{} : Bool}
  for row: {Nat.is_lt(P.q_pos(qb, r), q) == True{} : Bool}
  for len: {Nat.is_le(q, L) == True{} : Bool}
  {Spec.once(P.visits(L, q, qb, r, Nat.div(p, 32n), p)) == Spec.once(Spec.sees(L, q, P.q_pos(qb, r), p)) : Nat}

# 3. No other iteration ever puts key p into any row: with 2, each visible key is attended exactly once.
law tile_unique:
  for +L: Nat
  for +q: Nat
  for +qb: Nat
  for +r: Nat
  for +it: Nat
  for +p: Nat
  {Bool.and(P.visits(L, q, qb, r, it, p), Nat.is_ne(it, Nat.div(p, 32n))) == False{} : Bool}

# 4. No key past the bound: whatever the iteration, a key the row attends is at or before the row's
# absolute position and inside the chunk's keys.
law no_key_past:
  for +L: Nat
  for +q: Nat
  for +qb: Nat
  for +r: Nat
  for +it: Nat
  for +p: Nat
  for row: {Nat.is_lt(P.q_pos(qb, r), q) == True{} : Bool}
  for len: {Nat.is_le(q, L) == True{} : Bool}
  for hit: {P.visits(L, q, qb, r, it, p) == True{} : Bool}
  {Nat.is_le(p, Nat.add(Nat.sub(L, q), P.q_pos(qb, r))) == True{} : Bool} &
  {Nat.is_lt(p, L) == True{} : Bool}

# 5. Page addressing: a tile's 32 keys lie in the page of its first key (one block-table lookup per tile).
law tile_in_page:
  for +it: Nat
  {Nat.is_le(Nat.add(P.page_off(it), 32n), 256n) == True{} : Bool}

# 6. GQA rows: warp w < 6 of kv head kvh computes q head kvh * 6 + w, which maps back to (kvh, w); thread
# row r < 16 of block qb is position 16 qb + r, which maps back to (qb, r). So every (q head, position)
# is computed by exactly one (kv head, warp, block, row).
law gqa_rows:
  for +kvh: Nat
  for +w: Nat
  for +qb: Nat
  for +r: Nat
  for wb: {Nat.is_lt(w, 6n) == True{} : Bool}
  for rb: {Nat.is_lt(r, 16n) == True{} : Bool}
  {Nat.div(P.q_head(kvh, w), 6n) == kvh : Nat} &
  {Nat.mod(P.q_head(kvh, w), 6n) == w : Nat} &
  {Nat.div(P.q_pos(qb, r), 16n) == qb : Nat} &
  {Nat.mod(P.q_pos(qb, r), 16n) == r : Nat}

# 7. Span flush boundaries: the two k16 MMA steps s < 2 on dims 32 g + 16 s + k (k < 16) all belong to
# span g, the one flushed after them.
law span_flush:
  for +g: Nat
  for +s: Nat
  for +k: Nat
  for sb: {Nat.is_lt(s, 2n) == True{} : Bool}
  for kb: {Nat.is_lt(k, 16n) == True{} : Bool}
  {P.span(Nat.add(Nat.mul(g, 32n), Nat.add(Nat.mul(s, 16n), k))) == g : Nat}

# 8. Spans partition dims (and keys, for PV): d lies in [32 g, 32 g + 32) exactly when its span is g.
law span_member:
  for +g: Nat
  for +d: Nat
  {Bool.and(Nat.is_le(Nat.mul(g, 32n), d), Nat.is_lt(d, Nat.add(Nat.mul(g, 32n), 32n))) == Nat.is_eq(g, P.span(d)) : Bool}
