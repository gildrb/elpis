# Obligations for the ext patch 3006 buffers (attn_stride_bounds.bend) against the row-major
# reference (attn_stride_bounds_spec.bend) and the host allocation. Domain: every bsz, n_kv, n_q,
# q_len, grid width S, block-table width and cache size; b < bsz, kvh < n_kv, split CTA x < S,
# combine slot s < live, row < 48, column < 256, float2 element k < 2, q_pos < q_len, local head
# hl < group. Hypotheses a law does not need are left out.
import Base
import ./attn_stride.bend as Stride
import ./attn_stride_bounds.bend as Impl
import ./attn_stride_bounds_spec.bend as Spec
import ./attn_bounds.bend as Bounds

# 1. store_in_bounds: every partial split CTA x < S stores is the row-major cell of (b, kvh, x,
# row, column), and every partial the combine reads for a live slot s < min(S, n_tiles) is the cell
# of (b, kvh, s, row, column) -- the cell split CTA s wrote (attn_stride_laws.bend: slot_once) --
# and both lie below the size configure_slot and attn_verify_gr check partial_o / partial_ml
# against.
law store_in_bounds:
  for +bsz: Nat
  for +n_kv: Nat
  for +S: Nat
  for +L: Nat
  for +b: Nat
  for +kvh: Nat
  for +x: Nat
  for +s: Nat
  for +row: Nat
  for +col: Nat
  for +k: Nat
  for bb: {Nat.is_lt(b, bsz) == True{} : Bool}
  for kb: {Nat.is_lt(kvh, n_kv) == True{} : Bool}
  for xb: {Nat.is_lt(x, S) == True{} : Bool}
  for sb: {Nat.is_lt(s, Stride.live_slots(Stride.live_tiles(L), S)) == True{} : Bool}
  for rb: {Nat.is_lt(row, 48n) == True{} : Bool}
  for colb: {Nat.is_lt(col, 256n) == True{} : Bool}
  for eb: {Nat.is_lt(k, 2n) == True{} : Bool}
  {Impl.po_index(b, kvh, x, row, col, n_kv, S) == Spec.pcell(b, kvh, x, row, col, n_kv, S, 256n) : Nat} &
  {Impl.pml_index(b, kvh, x, row, k, n_kv, S) == Spec.pcell(b, kvh, x, row, k, n_kv, S, 2n) : Nat} &
  {Impl.co_index(b, kvh, row, s, col, n_kv, S) == Spec.pcell(b, kvh, s, row, col, n_kv, S, 256n) : Nat} &
  {Impl.cml_index(b, kvh, row, s, k, n_kv, S) == Spec.pcell(b, kvh, s, row, k, n_kv, S, 2n) : Nat} &
  {Impl.check_o(bsz, n_kv, S) == Spec.psize(bsz, n_kv, S, 256n) : Nat} &
  {Impl.check_ml(bsz, n_kv, S) == Spec.psize(bsz, n_kv, S, 2n) : Nat} &
  {Nat.is_lt(Impl.po_index(b, kvh, x, row, col, n_kv, S), Impl.check_o(bsz, n_kv, S)) == True{} : Bool} &
  {Nat.is_lt(Impl.pml_index(b, kvh, x, row, k, n_kv, S), Impl.check_ml(bsz, n_kv, S)) == True{} : Bool} &
  {Nat.is_lt(Impl.co_index(b, kvh, row, s, col, n_kv, S), Impl.check_o(bsz, n_kv, S)) == True{} : Bool} &
  {Nat.is_lt(Impl.cml_index(b, kvh, row, s, k, n_kv, S), Impl.check_ml(bsz, n_kv, S)) == True{} : Bool}

# 2. The combine's output store (and the split's Q load, same index and same check) of a valid row
# is the row-major cell of (b, q_pos, q head kvh * group + hl, d), inside the checked size.
law out_in_bounds:
  for +bsz: Nat
  for +q_len: Nat
  for +n_q: Nat
  for +n_kv: Nat
  for +b: Nat
  for +q_pos: Nat
  for +kvh: Nat
  for +hl: Nat
  for +d: Nat
  for bb: {Nat.is_lt(b, bsz) == True{} : Bool}
  for qb: {Nat.is_lt(q_pos, q_len) == True{} : Bool}
  for kb: {Nat.is_lt(kvh, n_kv) == True{} : Bool}
  for hb: {Nat.is_lt(hl, Nat.div(n_q, n_kv)) == True{} : Bool}
  for db: {Nat.is_lt(d, 256n) == True{} : Bool}
  {Impl.out_index(b, q_pos, kvh, hl, d, q_len, n_q, n_kv) ==
    Spec.ocell(b, q_pos, Nat.add(Nat.mul(kvh, Nat.div(n_q, n_kv)), hl), d, q_len, n_q) : Nat} &
  {Nat.is_lt(Impl.out_index(b, q_pos, kvh, hl, d, q_len, n_q, n_kv), Impl.check_out(bsz, q_len, n_q)) == True{} : Bool} &
  {Impl.check_out(bsz, q_len, n_q) == Spec.osize(bsz, q_len, n_q) : Nat}

# 3. The host allocation passes configure_slot's (and attn_verify_gr's) checks for the av_splits it
# launches, keeps the 3004 dense allocation (so attn_bounds_laws.bend's bounds still hold for the
# same slot), and the split grid is nonempty. The size depends on bsz, kv heads and SMs only: it
# does not grow with the cache.
law host_fits:
  for +bsz: Nat
  for +kvh: Nat
  for +splits: Nat
  for +nsub: Nat
  for +rows: Nat
  for +hd_pad: Nat
  for +sms: Nat
  {Nat.is_le(Impl.check_o(bsz, kvh, Impl.host_splits(sms, kvh)),
    Impl.host_pn_o(bsz, kvh, splits, nsub, rows, hd_pad, sms)) == True{} : Bool} &
  {Nat.is_le(Impl.check_ml(bsz, kvh, Impl.host_splits(sms, kvh)),
    Impl.host_pn_ml(bsz, kvh, splits, nsub, rows, sms)) == True{} : Bool} &
  {Nat.is_le(Impl.dense_o(bsz, kvh, splits, nsub, rows, hd_pad),
    Impl.host_pn_o(bsz, kvh, splits, nsub, rows, hd_pad, sms)) == True{} : Bool} &
  {Nat.is_le(Impl.dense_ml(bsz, kvh, splits, nsub, rows),
    Impl.host_pn_ml(bsz, kvh, splits, nsub, rows, sms)) == True{} : Bool} &
  {Nat.is_lt(0n, Impl.host_splits(sms, kvh)) == True{} : Bool}

# 4. K/V staging: every tile starts at a multiple of AV_T = 64, so it lies inside one 256-token page
# (n0 % 256 + 64 <= 256) and the physical rows bt[n0 / 256] * 256 + n0 % 256 + tok, tok < 64, stay
# in that page.
law tile_in_page:
  for +x: Nat
  for +it: Nat
  for +S: Nat
  {Nat.is_le(Impl.tile_slot_end(Stride.tile_n0(x, it, S)), 256n) == True{} : Bool}

# 5. Every tile a non-trapping split CTA stages starts inside the live range (n0 < L, so the
# cp.async byte count min(64, L - n0) rows is positive and the rest is zero-filled) and reads a
# block-table entry the table has (n0 / 256 < num_pages).
law tile_in_table:
  for +L: Nat
  for +S: Nat
  for +num_pages: Nat
  for +x: Nat
  for +it: Nat
  for xb: {Nat.is_lt(x, Stride.live_tiles(L)) == True{} : Bool}
  for tb: {Nat.is_lt(it, Stride.cta_tiles(Stride.live_tiles(L), x, S)) == True{} : Bool}
  for ok: {Impl.runs(L, num_pages) == True{} : Bool}
  {Nat.is_lt(Stride.tile_n0(x, it, S), L) == True{} : Bool} &
  {Nat.is_lt(Impl.tile_page(Stride.tile_n0(x, it, S)), num_pages) == True{} : Bool}

# 6. Why the block-table trap is needed: a round of L = 257 over a one-page table has a live tile
# 4 (CTA 4 of 20, first iteration) at n0 = 256, whose block-table entry 1 the table does not have.
law trap_needed:
  {Nat.is_lt(4n, Stride.live_tiles(257n)) == True{} : Bool} &
  {Nat.is_lt(0n, Stride.cta_tiles(Stride.live_tiles(257n), 4n, 20n)) == True{} : Bool} &
  {Impl.tile_page(Stride.tile_n0(4n, 0n, 20n)) == 1n : Nat} &
  {Impl.runs(257n, 1n) == False{} : Bool}

# 7. The combine's staging trap never fires: a grid width attn_verify_gr accepts (1 <= S <= 256)
# keeps the live slot count within one staging thread per slot, for every live length; and the
# served host width (20 on 82 SMs / 4 kv heads) passes the check.
law combine_no_trap:
  for +L: Nat
  for +S: Nat
  for checked: {Impl.gr_ok(S) == True{} : Bool}
  {Impl.combine_runs(Stride.live_slots(Stride.live_tiles(L), S)) == True{} : Bool}

law host_gr_ok:
  {Impl.gr_ok(Impl.host_splits(82n, 4n)) == True{} : Bool}
