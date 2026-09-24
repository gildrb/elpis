# Independent reference for the dense verify-attention partial buffer (ext 3002 kernels, 3004 host
# sizing): the partials of one launch form a row-major [B][SPLITS][NSUB] array of row blocks,
# B = bsz * n_kv_heads, with one cell per (batch * kv head, split, 16-row block). Stated without
# the kernels' program-id arithmetic (attn_bounds.bend).
import Base

# Number of cells of the [B][SPLITS][NSUB] array.
def cells(+bsz: Nat, +kvh: Nat, +splits: Nat, +nsub: Nat) -> Nat:
  Nat.mul(Nat.mul(bsz, kvh), Nat.mul(splits, nsub))

# The split-grid program owning the last cell (bh = B - 1, split = SPLITS - 1, sub = NSUB - 1):
# split SPLITS - 1 lies in sub-program q = (SPLITS - 1) / GRID_Y at height (SPLITS - 1) % GRID_Y.
def last_pid(+bsz: Nat, +kvh: Nat, +nsub: Nat, +grid_y: Nat, +splits: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.sub(Nat.mul(bsz, kvh), 1n), nsub), Nat.div(Nat.sub(splits, 1n), grid_y))

def last_y(+grid_y: Nat, +splits: Nat) -> Nat:
  Nat.mod(Nat.sub(splits, 1n), grid_y)

def last_sub(+nsub: Nat) -> Nat:
  Nat.sub(nsub, 1n)
