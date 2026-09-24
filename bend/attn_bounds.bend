# Partial-buffer index arithmetic of the dense verify-attention split/combine (ext patch 3002,
# modules/attention_fn/triton_paged.py: _paged_attn_decode_gqa_split_kernel,
# _paged_attn_decode_gqa_combine_kernel, gqa_geometry) and its host sizing (ext patch 3004,
# modules/attention_fn/bc_attn.py: dense_partial_blocks, dense_partial_extent), transcribed over
# Nat. Indices count partial row blocks (BLOCK_ROWS x HD_PAD fp32 in partial_o, BLOCK_ROWS x 2 in
# partial_ml; both buffers use the same block index). Triton / Python int arithmetic on the
# non-negative values used here is Nat arithmetic (no overflow at these sizes). q_len only fixes
# NSUB (= h_blocks, 1..4) and BLOCK_M, so the laws quantify over NSUB directly. Independent
# reference: attn_bounds_spec.bend; laws: attn_bounds_laws.bend.
import Base

# gqa_geometry: SPLITS = max(1, min(h_blocks * grid_y, (_gqa_ctas_per_sm * sm_count) //
# (bsz * n_kv_heads))); `ctas` is _gqa_ctas_per_sm * sm_count.
def gqa_splits(+bsz: Nat, +kvh: Nat, +nsub: Nat, +grid_y: Nat, +ctas: Nat) -> Nat:
  Nat.max(1n, Nat.min(Nat.mul(nsub, grid_y), Nat.div(ctas, Nat.mul(bsz, kvh))))

# Launch grids: split (programs, GRID_Y), combine (programs,), programs = bsz * kvh * NSUB.
def programs(+bsz: Nat, +kvh: Nat, +nsub: Nat) -> Nat:
  Nat.mul(Nat.mul(bsz, kvh), nsub)

# Split kernel, program (pid, y): split = (pid % NSUB) * GRID_Y + y.
def split_index(+pid: Nat, +y: Nat, +nsub: Nat, +grid_y: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.mod(pid, nsub), grid_y), y)

# Split kernel: `if split >= SPLITS: return`; a program that passes stores its partials.
def split_runs(+pid: Nat, +y: Nat, +nsub: Nat, +grid_y: Nat, +splits: Nat) -> Bool:
  Bool.not(Nat.is_ge(split_index(pid, y, nsub, grid_y), splits))

# Split kernel store: base = (bh * SPLITS + split) * NSUB with bh = pid // NSUB; row block `sub`
# (sub < NSUB) goes to base + sub (ml always, acc when the split has work).
def store_index(+pid: Nat, +y: Nat, +sub: Nat, +nsub: Nat, +grid_y: Nat, +splits: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(pid, nsub), splits), split_index(pid, y, nsub, grid_y)),
    nsub), sub)

# Combine kernel, program pid (bh = pid // NSUB, sub = pid % NSUB), loop step s < SPLITS:
# idx = (bh * SPLITS + s) * NSUB + sub.
def combine_index(+pid: Nat, +s: Nat, +nsub: Nat, +splits: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(pid, nsub), splits), s), nsub), Nat.mod(pid, nsub))

# 3004 dense_partial_blocks(bsz, n_kv_heads, splits, nsub) = bsz * n_kv_heads * splits * nsub.
def dense_partial_blocks(+bsz: Nat, +kvh: Nat, +splits: Nat, +nsub: Nat) -> Nat:
  Nat.mul(Nat.mul(Nat.mul(bsz, kvh), splits), nsub)

# 3004 dense_partial_extent (GQA branch): bh_max = (programs - 1) // nsub,
# split_max = min(splits, nsub * grid_y) - 1, (bh_max * splits + split_max) * nsub + (nsub - 1) + 1.
def dense_partial_extent(+programs: Nat, +grid_y: Nat, +splits: Nat, +nsub: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(Nat.sub(programs, 1n), nsub), splits),
    Nat.sub(Nat.min(splits, Nat.mul(nsub, grid_y)), 1n)), nsub), Nat.sub(nsub, 1n)), 1n)

# 3004 host allocation of a dense GQA slot (nsub_p = h_blocks, splits_p = gqa_splits):
# dense_blocks = dense_partial_blocks(bsz, kvh, splits_p, nsub_p).
def host_partial_blocks(+bsz: Nat, +kvh: Nat, +nsub: Nat, +grid_y: Nat, +splits: Nat) -> Nat:
  dense_partial_blocks(bsz, kvh, splits, nsub)

# Pristine (g7n) host allocation, bc_attn.py:381-386: programs * splits_cap blocks.
def pristine_partial_blocks(+bsz: Nat, +kvh: Nat, +nsub: Nat, +grid_y: Nat) -> Nat:
  Nat.mul(programs(bsz, kvh, nsub), grid_y)

# Non-GQA split kernel (pristine _paged_attn_decode_split_kernel): program (pid, split) stores
# block pid * num_splits + split for split < num_splits <= splits_cap; the combine reads the same.
def plain_store_index(+pid: Nat, +split: Nat, +num_splits: Nat) -> Nat:
  Nat.add(Nat.mul(pid, num_splits), split)
