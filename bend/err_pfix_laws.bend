# Error-bound laws of the ext 3031 prefill attention against stock ExLlamaV3 355c6ee's Triton prefill (model:
# err_pfix.bend, vocabulary: err_bound.bend, exchange rate 128). Proven in err_pfix_proof.bend; gate err_pfix_gate.bend.
# Named hypotheses (model facts, not proven here): those of err_prefill_laws.bend (H_std, H_ratio, H_common_kv,
# H_masked_exact, H_ptx, H_same_text) and
#   H_park     a parked chain's O, m, l are stored and reloaded as fp32 bit patterns (exact), and a CTA owns its SM's
#              scratch slot for its whole run (one CTA per SM, checked on the host before the first launch).
import Base
import ./err_bound.bend as Eb
import ./err_pfix.bend as Ef

# 1. Domination, for every row and context. A row at absolute position p of stock's 64-row block starting at q64 (the
# block's key bound n_hi = nh: q64 < nh <= q64 + 64, p < nh), whatever stock's split count ns in 1 .. 8 (the wrapper's
# candidates are 1 .. 6 and 8): every elpis 3031 composite of the row's output elements (numerator key in any visible tile
# T, either k16 half, any score step s; denominator key in any visible tile Td, any score step s2) is dominated by a stock
# composite of the same row: the leaf with both keys in tile 0 (stock_witness, a real stock leaf: stock_leaf at split 0,
# tile 0, first half).
law pfix_dom:
  for +q64: Nat
  for +nh: Nat
  for +p: Nat
  for +ns: Nat
  for +T: Nat
  for h: Bool
  for +s: Nat
  for +Td: Nat
  for +s2: Nat
  for nlo: {Nat.is_lt(q64, nh) == True{} : Bool}
  for nhi: {Nat.is_le(nh, Nat.add(q64, 64n)) == True{} : Bool}
  for plo: {Nat.is_le(q64, p) == True{} : Bool}
  for phi: {Nat.is_lt(p, nh) == True{} : Bool}
  for ns1: {Nat.is_le(1n, ns) == True{} : Bool}
  for ns8: {Nat.is_le(ns, 8n) == True{} : Bool}
  for tv: {Nat.is_le(T, Nat.div(p, 32n)) == True{} : Bool}
  for tdv: {Nat.is_le(Td, Nat.div(p, 32n)) == True{} : Bool}
  {Eb.dom(128n, Ef.elpis_at(q64, p, T, h, s, Td, s2), Ef.stock_at(q64, nh, p, ns, s, s2)) == True{} : Bool}

# 2. The witness is a stock leaf of the row: stock_at is stock_leaf with both keys in split 0, tile 0, first half, and
# split 0 holding stock_n tiles of the row.
law pfix_witness:
  for +q64: Nat
  for +nh: Nat
  for +p: Nat
  for +ns: Nat
  for +s: Nat
  for +s2: Nat
  {Ef.stock_at(q64, nh, p, ns, s, s2) == Ef.stock_leaf(1n, Nat.is_lt(1n, ns), Ef.stock_ks(Ef.n_tiles(p), nh, ns),
    Ef.interior_tiles(q64), 0n, 0n, Nat.sub(Ef.stock_n(Ef.n_tiles(p), nh, ns), 1n), False{}, s, 0n, 0n,
    Nat.sub(Ef.stock_n(Ef.n_tiles(p), nh, ns), 1n), s2) : Eb.Path}

# 3. Chunk invariance of the chain plan. The kernels compute q_abs64 = (total - q_len) + 64 ((i) / 64) for chunk row i
# (K: total - q_len + (p0 & ~63)); for a chunk starting at a multiple of 64 (served chunks start at page boundaries) it
# is 64 ((absolute position) / 64), so E, the chains, n_full and every rounding path of the row depend only on the row's
# absolute position: 2048-row and merged 4096-row chunks (5110g/h) and any 64-aligned chunking compute the row alike.
law pfix_chunk_invariant:
  for +u: Nat
  for +i: Nat
  {Nat.add(Nat.mul(u, 64n), Nat.mul(Nat.div(i, 64n), 64n)) == Nat.mul(Nat.div(Nat.add(Nat.mul(u, 64n), i), 64n), 64n) : Nat}
