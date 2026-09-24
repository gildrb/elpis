# Semantic obligations for the tile partition of the draft-only int4 head kernel (ext patch 9001,
# dflash2_q4_head_topk_kernel; D: refs as in draft_head_partition.bend) over the Nat model
# draft_head_partition.bend and its reference draft_head_partition_spec.bend. Quantifies over every
# grid G >= 1 (the host launches one 16-warp block per SM, G <= n_tiles) and every tile count n.
# Nat model of the C int expressions: overflow, fp32 values, the register ring's timing and the
# top-16 merge network are outside this contract (the merge network is checked by the CPU
# differential test of the patch, not proven here).
import Base
import ./draft_head_partition.bend as Impl
import ./draft_head_partition_spec.bend as Spec

# Every vocabulary tile x < n is computed by exactly one (block, warp) of the grid, and no tile
# x >= n by any: each tile's logits enter exactly one warp's running top-16 list.
law tiles_exactly_once:
  for +x: Nat
  for +G: Nat
  for +n: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  {Impl.tile_hits(G, x, G, n) == Spec.covered(x, n) : Nat}

# Fixed reduction order inside a tile: for every CH = K / 64 with CH % 8 == 0 (host check
# K % 512 == 0), the tile consumes chunks 0 .. CH - 1 once each in ascending order and folds the
# 128-deep scale groups 0 .. CH / 2 - 1 in ascending order, group g right after its chunks 2 g, 2 g + 1
# (so every logit is the same fixed fp32 expression sum_g scale_g * part_g, left to right).
law tile_order:
  for +L: Nat
  {Impl.tile_trace(Nat.mul(8n, L)) == Spec.groups_trace(Nat.mul(4n, L), 0n, 0n) : List<&2, Spec.Ev>}
