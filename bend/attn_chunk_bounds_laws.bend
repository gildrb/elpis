# Obligations for the ext patch 3003 buffers (attn_chunk_bounds.bend) against the row-major
# reference (attn_chunk_bounds_spec.bend) and the host allocation. Domain: every bsz, n_kv, n_q,
# q_len, max_chunks, chunk, block-table width and cache size; b < bsz, kvh < n_kv, live chunk
# c < n_chunks, row < 48, column < 256, float2 element k < 2, q_pos < q_len, local head hl < group.
# Hypotheses a law does not need are left out.
import Base
import ./attn_chunk.bend as Chunk
import ./attn_chunk_bounds.bend as Impl
import ./attn_chunk_bounds_spec.bend as Spec
import ./attn_bounds.bend as Bounds

# 1. store_in_bounds: in a non-trapping launch (n_chunks <= max_chunks), every partial the split
# kernel stores for a live chunk and every partial the combine reads for it is the row-major cell of
# (b, kvh, chunk, row, column) -- the combine reads exactly the cell the split wrote -- and lies
# below the size configure_slot checks partial_o / partial_ml against.
law store_in_bounds:
  for +bsz: Nat
  for +n_kv: Nat
  for +mc: Nat
  for +L: Nat
  for +chunk: Nat
  for +b: Nat
  for +kvh: Nat
  for +c: Nat
  for +row: Nat
  for +col: Nat
  for +k: Nat
  for bb: {Nat.is_lt(b, bsz) == True{} : Bool}
  for kb: {Nat.is_lt(kvh, n_kv) == True{} : Bool}
  for cb: {Nat.is_lt(c, Chunk.live(L, chunk)) == True{} : Bool}
  for notrap: {Nat.is_le(Chunk.live(L, chunk), mc) == True{} : Bool}
  for rb: {Nat.is_lt(row, 48n) == True{} : Bool}
  for colb: {Nat.is_lt(col, 256n) == True{} : Bool}
  for eb: {Nat.is_lt(k, 2n) == True{} : Bool}
  {Impl.po_index(b, kvh, c, row, col, n_kv, mc) == Spec.pcell(b, kvh, c, row, col, n_kv, mc, 256n) : Nat} &
  {Impl.co_index(b, kvh, row, c, col, n_kv, mc) == Spec.pcell(b, kvh, c, row, col, n_kv, mc, 256n) : Nat} &
  {Impl.pml_index(b, kvh, c, row, k, n_kv, mc) == Spec.pcell(b, kvh, c, row, k, n_kv, mc, 2n) : Nat} &
  {Impl.cml_index(b, kvh, row, c, k, n_kv, mc) == Spec.pcell(b, kvh, c, row, k, n_kv, mc, 2n) : Nat} &
  {Impl.check_o(bsz, n_kv, mc) == Spec.psize(bsz, n_kv, mc, 256n) : Nat} &
  {Impl.check_ml(bsz, n_kv, mc) == Spec.psize(bsz, n_kv, mc, 2n) : Nat} &
  {Nat.is_lt(Impl.po_index(b, kvh, c, row, col, n_kv, mc), Impl.check_o(bsz, n_kv, mc)) == True{} : Bool} &
  {Nat.is_lt(Impl.pml_index(b, kvh, c, row, k, n_kv, mc), Impl.check_ml(bsz, n_kv, mc)) == True{} : Bool}

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

# 3. The traps never fire: a live length the block table spans (L <= num_pages * 256) has
# n_chunks <= max_chunks whenever attn_verify_gr's check passes, and the host's av_max_chunks
# passes that check for every block-table width up to the cache's pages.
law no_trap:
  for +L: Nat
  for +chunk: Nat
  for +mc: Nat
  for +num_pages: Nat
  for cpos: {Nat.is_lt(0n, chunk) == True{} : Bool}
  for spans: {Nat.is_le(L, Nat.mul(num_pages, 256n)) == True{} : Bool}
  for checked: {Impl.gr_ok(mc, chunk, num_pages) == True{} : Bool}
  {Nat.is_le(Chunk.live(L, chunk), mc) == True{} : Bool}

law host_no_trap:
  for +max_pages: Nat
  for +num_pages: Nat
  for +chunk: Nat
  for cpos: {Nat.is_lt(0n, chunk) == True{} : Bool}
  for width: {Nat.is_le(num_pages, max_pages) == True{} : Bool}
  {Impl.gr_ok(Impl.host_max_chunks(max_pages, chunk), chunk, num_pages) == True{} : Bool}

# 4. The host allocation passes configure_slot's checks for the av_max_chunks it passes, keeps the
# 3004 dense allocation (so attn_bounds_laws.bend's bounds still hold for the same slot), and the
# split grid is nonempty.
law host_fits:
  for +bsz: Nat
  for +kvh: Nat
  for +splits: Nat
  for +nsub: Nat
  for +rows: Nat
  for +hd_pad: Nat
  for +max_pages: Nat
  for +chunk: Nat
  for +sms: Nat
  {Nat.is_le(Impl.check_o(bsz, kvh, Impl.host_max_chunks(max_pages, chunk)),
    Impl.host_pn_o(bsz, kvh, splits, nsub, rows, hd_pad, max_pages, chunk)) == True{} : Bool} &
  {Nat.is_le(Impl.check_ml(bsz, kvh, Impl.host_max_chunks(max_pages, chunk)),
    Impl.host_pn_ml(bsz, kvh, splits, nsub, rows, max_pages, chunk)) == True{} : Bool} &
  {Nat.is_le(Impl.dense_o(bsz, kvh, splits, nsub, rows, hd_pad),
    Impl.host_pn_o(bsz, kvh, splits, nsub, rows, hd_pad, max_pages, chunk)) == True{} : Bool} &
  {Nat.is_le(Impl.dense_ml(bsz, kvh, splits, nsub, rows),
    Impl.host_pn_ml(bsz, kvh, splits, nsub, rows, max_pages, chunk)) == True{} : Bool} &
  {Nat.is_lt(0n, Impl.host_splits(sms, bsz, kvh)) == True{} : Bool}

# 5. K/V staging: with chunk a multiple of AV_T = 64 (configure_slot / attn_verify_gr check), every
# tile lies inside one 256-token page (n0 % 256 + 64 <= 256), so the physical rows
# bt[n0 / 256] * 256 + n0 % 256 + tok, tok < 64, stay in that page; and every staged tile of a live
# chunk reads a block-table entry the table has (n0 / 256 < num_pages when L <= num_pages * 256).
law tile_in_page:
  for +m: Nat
  for +c: Nat
  for +it: Nat
  {Nat.is_le(Impl.tile_slot_end(Chunk.tile_n0(c, it, Nat.mul(m, 64n))), 256n) == True{} : Bool}

law tile_in_table:
  for +L: Nat
  for +chunk: Nat
  for +num_pages: Nat
  for +c: Nat
  for +it: Nat
  for cb: {Nat.is_lt(c, Chunk.live(L, chunk)) == True{} : Bool}
  for tb: {Nat.is_lt(it, Chunk.ntiles(c, L, chunk)) == True{} : Bool}
  for spans: {Nat.is_le(L, Nat.mul(num_pages, 256n)) == True{} : Bool}
  {Nat.is_lt(Impl.tile_page(Chunk.tile_n0(c, it, chunk)), num_pages) == True{} : Bool}

# 6. Why the multiple-of-64 check is needed: with chunk 96 (not a multiple of 64) tile 0 of chunk 5
# starts at 480 = page 1 slot 224 and its 64 rows would run 32 rows past the page end into
# whatever page follows physically.
law unaligned_chunk_straddles:
  {Chunk.tile_n0(5n, 0n, 96n) == 480n : Nat} &
  {Impl.tile_slot_end(Chunk.tile_n0(5n, 0n, 96n)) == 288n : Nat} &
  {Nat.is_lt(256n, Impl.tile_slot_end(Chunk.tile_n0(5n, 0n, 96n))) == True{} : Bool}
