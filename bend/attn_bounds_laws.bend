# Obligations for the dense verify-attention partial buffers (ext patch 3004-attn-partial-bounds)
# over the Nat model attn_bounds.bend and the row-major reference attn_bounds_spec.bend.
# Domain: every bsz, n_kv_heads, NSUB >= 1 (the kernel's 1..4: every q_len, since q_len only fixes
# NSUB / BLOCK_M), every GRID_Y, every SPLITS (A3 needs 1 <= SPLITS <= NSUB * GRID_Y, which
# gqa_geometry guarantees, A0); served target: bsz 1, kvh 4, NSUB 3, GRID_Y 13, SPLITS 39.
# Hypotheses a law does not need are left out (a law without them is stronger).
import Base
import ./attn_bounds.bend as Impl
import ./attn_bounds_spec.bend as Spec

# A0: gqa_geometry's SPLITS lies in 1 .. NSUB * GRID_Y for every sm count, bsz and kvh.
law gqa_splits_in_grid:
  for +bsz: Nat
  for +kvh: Nat
  for +nsub: Nat
  for +grid_y: Nat
  for +ctas: Nat
  for grid_pos: {Nat.is_lt(0n, Nat.mul(nsub, grid_y)) == True{} : Bool}
  {Nat.is_le(1n, Impl.gqa_splits(bsz, kvh, nsub, grid_y, ctas)) == True{} : Bool} &
  {Nat.is_le(Impl.gqa_splits(bsz, kvh, nsub, grid_y, ctas), Nat.mul(nsub, grid_y)) == True{} : Bool}

# A1: every partial block stored by every launched split program (pid < programs, any y, any
# row block sub < NSUB, split < SPLITS) lies inside the 3004 allocation.
law split_store_in_bounds:
  for +bsz: Nat
  for +kvh: Nat
  for +nsub: Nat
  for +grid_y: Nat
  for +splits: Nat
  for +pid: Nat
  for +y: Nat
  for +sub: Nat
  for nsub_pos: {Nat.is_lt(0n, nsub) == True{} : Bool}
  for pid_in: {Nat.is_lt(pid, Impl.programs(bsz, kvh, nsub)) == True{} : Bool}
  for sub_in: {Nat.is_lt(sub, nsub) == True{} : Bool}
  for runs: {Impl.split_runs(pid, y, nsub, grid_y, splits) == True{} : Bool}
  {Nat.is_lt(Impl.store_index(pid, y, sub, nsub, grid_y, splits),
    Impl.host_partial_blocks(bsz, kvh, nsub, grid_y, splits)) == True{} : Bool}

# A2: every partial block read by every combine program (pid < programs, loop step s < SPLITS)
# lies inside the 3004 allocation.
law combine_read_in_bounds:
  for +bsz: Nat
  for +kvh: Nat
  for +nsub: Nat
  for +grid_y: Nat
  for +splits: Nat
  for +pid: Nat
  for +s: Nat
  for nsub_pos: {Nat.is_lt(0n, nsub) == True{} : Bool}
  for pid_in: {Nat.is_lt(pid, Impl.programs(bsz, kvh, nsub)) == True{} : Bool}
  for s_in: {Nat.is_lt(s, splits) == True{} : Bool}
  {Nat.is_lt(Impl.combine_index(pid, s, nsub, splits),
    Impl.host_partial_blocks(bsz, kvh, nsub, grid_y, splits)) == True{} : Bool}

# A3: the allocation is tight and the host's fail-closed extent equals it: the extent formula
# equals the allocation, the allocation is the [B][SPLITS][NSUB] cell count, and the program that
# owns the last cell is launched, passes the split guard and stores block allocation - 1 (so by A1
# the maximum stored index + 1 is exactly the allocation).
law extent_exact:
  for +bsz: Nat
  for +kvh: Nat
  for +nsub: Nat
  for +grid_y: Nat
  for +splits: Nat
  for bsz_pos: {Nat.is_lt(0n, bsz) == True{} : Bool}
  for kvh_pos: {Nat.is_lt(0n, kvh) == True{} : Bool}
  for nsub_pos: {Nat.is_lt(0n, nsub) == True{} : Bool}
  for splits_pos: {Nat.is_lt(0n, splits) == True{} : Bool}
  for splits_cap: {Nat.is_le(splits, Nat.mul(nsub, grid_y)) == True{} : Bool}
  {Impl.dense_partial_extent(Impl.programs(bsz, kvh, nsub), grid_y, splits, nsub) ==
    Impl.host_partial_blocks(bsz, kvh, nsub, grid_y, splits) : Nat} &
  {Impl.host_partial_blocks(bsz, kvh, nsub, grid_y, splits) == Spec.cells(bsz, kvh, splits, nsub) : Nat} &
  {Nat.is_lt(Spec.last_pid(bsz, kvh, nsub, grid_y, splits), Impl.programs(bsz, kvh, nsub)) == True{} : Bool} &
  {Nat.is_lt(Spec.last_y(grid_y, splits), grid_y) == True{} : Bool} &
  {Nat.is_lt(Spec.last_sub(nsub), nsub) == True{} : Bool} &
  {Impl.split_runs(Spec.last_pid(bsz, kvh, nsub, grid_y, splits), Spec.last_y(grid_y, splits), nsub, grid_y, splits) == True{} : Bool} &
  {1n+Impl.store_index(Spec.last_pid(bsz, kvh, nsub, grid_y, splits), Spec.last_y(grid_y, splits),
    Spec.last_sub(nsub), nsub, grid_y, splits) == Impl.host_partial_blocks(bsz, kvh, nsub, grid_y, splits) : Nat}

# A4 (the bug 3004 fixes): with the pristine programs * splits_cap sizing the store law fails. On
# the served target (bsz 1, kvh 4, NSUB 3, GRID_Y 13, gqa_geometry SPLITS 39 on 82 SMs x 2 CTAs)
# program (pid 11, y 12) is launched, passes the guard and stores row block 2 at index 467, while
# the pristine allocation holds 156 blocks (and the 3004 allocation 468).
law pristine_store_out_of_bounds:
  {Impl.gqa_splits(1n, 4n, 3n, 13n, 164n) == 39n : Nat} &
  {Nat.is_lt(11n, Impl.programs(1n, 4n, 3n)) == True{} : Bool} &
  {Nat.is_lt(12n, 13n) == True{} : Bool} &
  {Nat.is_lt(2n, 3n) == True{} : Bool} &
  {Impl.split_runs(11n, 12n, 3n, 13n, 39n) == True{} : Bool} &
  {Impl.store_index(11n, 12n, 2n, 3n, 13n, 39n) == 467n : Nat} &
  {Impl.pristine_partial_blocks(1n, 4n, 3n, 13n) == 156n : Nat} &
  {Nat.is_le(Impl.pristine_partial_blocks(1n, 4n, 3n, 13n), Impl.store_index(11n, 12n, 2n, 3n, 13n, 39n)) == True{} : Bool} &
  {Impl.host_partial_blocks(1n, 4n, 3n, 13n, 39n) == 468n : Nat}

# A5: the non-GQA split kernel (pid < programs, split < num_splits <= splits_cap) stores inside the
# 3004 allocation for that branch, dense_partial_blocks(bsz, kvh, splits_cap, h_blocks).
law plain_store_in_bounds:
  for +bsz: Nat
  for +kvh: Nat
  for +nsub: Nat
  for +grid_y: Nat
  for +num_splits: Nat
  for +pid: Nat
  for +split: Nat
  for pid_in: {Nat.is_lt(pid, Impl.programs(bsz, kvh, nsub)) == True{} : Bool}
  for split_in: {Nat.is_lt(split, num_splits) == True{} : Bool}
  for splits_cap: {Nat.is_le(num_splits, grid_y) == True{} : Bool}
  {Nat.is_lt(Impl.plain_store_index(pid, split, num_splits),
    Impl.dense_partial_blocks(bsz, kvh, grid_y, nsub)) == True{} : Bool}
