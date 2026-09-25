# Buffer index arithmetic of the ext patch 3006 verify-attention kernels (exllamav3_ext/attn_verify.cu:
# split partial stores, combine partial reads, output store, Q loads, K/V tile staging, the
# block-table trap) and the sizes the host allocates and checks for them
# (modules/attention_fn/bc_attn.py: av_splits, pn_o / pn_ml; exllamav3_ext/libtorch/attention.cpp:
# BC_Attention::configure_slot TORCH_CHECKs; exllamav3_ext/attn_verify_gr.cu: the partial-size
# checks), transcribed over Nat. C `size_t` / `int64_t` and Python int arithmetic on these
# non-negative values is Nat arithmetic (every index and size < 2^40). The 3006 allocation extends
# the 3004 one (attn_bounds.bend): pn_o / pn_ml are the max of the 3004 dense sizes and the 3006
# sizes. Supersedes attn_chunk_bounds.bend (3003's per-chunk partials). Reference:
# attn_stride_bounds_spec.bend; laws: attn_stride_bounds_laws.bend.
import Base
import ./attn_stride.bend as Stride
import ./attn_bounds.bend as Bounds

# C split store: pbase = ((size_t) (b * n_kv_heads + kvh) * S + cta) * AV_ROWS, AV_ROWS = 48,
# S = gridDim.x
def pbase(+b: Nat, +kvh: Nat, +x: Nat, +n_kv: Nat, +S: Nat) -> Nat:
  Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(b, n_kv), kvh), S), x), 48n)

# C: partial_o + (pbase + row) * AV_HD + col, row = 16 i + gid or 16 i + 8 + gid (< 48), col =
# 32 warp + 8 j + 2 t and col + 1 of the float2 (< 256), AV_HD = 256
def po_index(+b: Nat, +kvh: Nat, +x: Nat, +row: Nat, +col: Nat, +n_kv: Nat, +S: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(pbase(b, kvh, x, n_kv, S), row), 256n), col)

# C: partial_ml + (pbase + 8 * s + gid) * 2, float2 (m, l): element k < 2, row = 8 s + gid < 48
def pml_index(+b: Nat, +kvh: Nat, +x: Nat, +row: Nat, +k: Nat, +n_kv: Nat, +S: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(pbase(b, kvh, x, n_kv, S), row), 2n), k)

# C combine: base = (size_t) (b * n_kv_heads + kvh) * splits * AV_ROWS + r;
# idx = base + (size_t) s * AV_ROWS
def cidx(+b: Nat, +kvh: Nat, +r: Nat, +s: Nat, +n_kv: Nat, +S: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(Nat.mul(Nat.add(Nat.mul(b, n_kv), kvh), S), 48n), r), Nat.mul(s, 48n))

# C combine reads partial_ml[idx * 2] (the float2 at idx * 2: element k < 2) and
# partial_o[idx * AV_HD + d], d = threadIdx.x < 256
def cml_index(+b: Nat, +kvh: Nat, +r: Nat, +s: Nat, +k: Nat, +n_kv: Nat, +S: Nat) -> Nat:
  Nat.add(Nat.mul(cidx(b, kvh, r, s, n_kv, S), 2n), k)

def co_index(+b: Nat, +kvh: Nat, +r: Nat, +s: Nat, +d: Nat, +n_kv: Nat, +S: Nat) -> Nat:
  Nat.add(Nat.mul(cidx(b, kvh, r, s, n_kv, S), 256n), d)

# C combine store: out[((size_t) (b * q_len + q_pos) * n_q_heads + kvh * group + hl) * AV_HD + d],
# group = n_q_heads / n_kv_heads. The split's Q prologue reads q at the same index with
# d = 32 g + 16 ks + 8 kh + 2 t (+ 1) < 256 for valid rows (q_pos = gid < q_len, hl < group).
def out_index(+b: Nat, +q_pos: Nat, +kvh: Nat, +hl: Nat, +d: Nat, +q_len: Nat, +n_q: Nat, +n_kv: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.add(Nat.mul(Nat.add(Nat.mul(b, q_len), q_pos), n_q),
    Nat.mul(kvh, Nat.div(n_q, n_kv))), hl), 256n), d)

# T / G TORCH_CHECK: partial_o.numel() >= (int64_t) bsz * n_kv_heads * splits * AV_ROWS * AV_HD
# (configure_slot with av_splits, attn_verify_gr with splits: the same expression)
def check_o(+bsz: Nat, +n_kv: Nat, +S: Nat) -> Nat:
  Nat.mul(Nat.mul(Nat.mul(Nat.mul(bsz, n_kv), S), 48n), 256n)

# T / G TORCH_CHECK: partial_ml.numel() >= (int64_t) bsz * n_kv_heads * splits * AV_ROWS * 2
def check_ml(+bsz: Nat, +n_kv: Nat, +S: Nat) -> Nat:
  Nat.mul(Nat.mul(Nat.mul(Nat.mul(bsz, n_kv), S), 48n), 2n)

# T TORCH_CHECK: o.numel() and q.numel() >= (int64_t) bsz * q_len * num_q_heads * AV_HD
def check_out(+bsz: Nat, +q_len: Nat, +n_q: Nat) -> Nat:
  Nat.mul(Nat.mul(Nat.mul(bsz, q_len), n_q), 256n)

# C split: `if (L > num_pages_per_seq * AV_PAGE) __trap();` -- the kernel runs past it iff
def runs(+L: Nat, +num_pages: Nat) -> Bool:
  Nat.is_le(L, Nat.mul(num_pages, 256n))

# P: av_splits = max(1, _get_sm_count(dev) // kvh), the split grid's x = S (no bsz, no depth)
def host_splits(+sms: Nat, +kvh: Nat) -> Nat:
  Nat.max(1n, Nat.div(sms, kvh))

# P: the 3004 dense sizes (pn_o = dense_blocks * block_rows * hd_pad, pn_ml = dense_blocks *
# block_rows * 2, dense_blocks = dense_partial_blocks(bsz, kvh, splits_p, nsub_p)), then
# pn_o = max(pn_o, bsz * kvh * av_splits * 48 * 256), pn_ml = max(pn_ml, ... * 48 * 2)
def dense_o(+bsz: Nat, +kvh: Nat, +splits: Nat, +nsub: Nat, +rows: Nat, +hd_pad: Nat) -> Nat:
  Nat.mul(Nat.mul(Bounds.dense_partial_blocks(bsz, kvh, splits, nsub), rows), hd_pad)

def dense_ml(+bsz: Nat, +kvh: Nat, +splits: Nat, +nsub: Nat, +rows: Nat) -> Nat:
  Nat.mul(Nat.mul(Bounds.dense_partial_blocks(bsz, kvh, splits, nsub), rows), 2n)

def host_pn_o(+bsz: Nat, +kvh: Nat, +splits: Nat, +nsub: Nat, +rows: Nat, +hd_pad: Nat, +sms: Nat) -> Nat:
  Nat.max(dense_o(bsz, kvh, splits, nsub, rows, hd_pad),
    Nat.mul(Nat.mul(Nat.mul(Nat.mul(bsz, kvh), host_splits(sms, kvh)), 48n), 256n))

def host_pn_ml(+bsz: Nat, +kvh: Nat, +splits: Nat, +nsub: Nat, +rows: Nat, +sms: Nat) -> Nat:
  Nat.max(dense_ml(bsz, kvh, splits, nsub, rows),
    Nat.mul(Nat.mul(Nat.mul(Nat.mul(bsz, kvh), host_splits(sms, kvh)), 48n), 2n))

# G TORCH_CHECK: splits > 0 && splits <= AV_HD (one combine staging thread per slot)
def gr_ok(+S: Nat) -> Bool:
  Bool.and(Nat.is_lt(0n, S), Nat.is_le(S, 256n))

# C combine: `if (live > AV_HD) __trap();` -- the combine runs past it iff
def combine_runs(+live: Nat) -> Bool:
  Nat.is_le(live, 256n)

# C issue: the tile at n0 reads block_table[b][n0 / AV_PAGE] and stages cache rows
# bt[n0 / 256] * 256 + n0 % 256 + tok for tok < min(AV_T, L - n0): the page slot of token tok
# is n0 % 256 + tok
def tile_page(+n0: Nat) -> Nat:
  Nat.div(n0, 256n)

def tile_slot_end(+n0: Nat) -> Nat:
  Nat.add(Nat.mod(n0, 256n), 64n)
