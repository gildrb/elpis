# Tile partition of the draft-only int4 head kernel, ext patch 9001 (9001-draft-fast.patch,
# exllamav3_ext/dflash2_head.cu, dflash2_q4_head_topk_kernel), transcribed from the CUDA integer
# expressions over Nat (D: = dflash2_head.cu, post-patch):
#   D:  const int W = gridDim.x * HEAD_WARPS;                  HEAD_WARPS = 16
#   D:  const int gw = blockIdx.x * HEAD_WARPS + warp;
#   D:  for (int tile = gw; tile < n_tiles; tile += W) { chunks 0..CH-1; epilogue(tile) }
# C int arithmetic on these non-negative values is Nat arithmetic while no value overflows (the host
# checks n_tiles = ceil(vocab / 16) with vocab < 2^31 and grid <= n_tiles); `blockIdx.x * 16 + warp`
# is written warp + 16 * b (Nat addition and multiplication commute). The `for` loop is the loop form
# M16.jobloop.go of the m16 finisher (patch 2001), reused here as the generic model of
# `for (x = start; x < n; x += step)`; its fuel n + 1 never cuts the loop short for step >= 1.
# Reference: draft_head_partition_spec.bend; laws: draft_head_partition_laws.bend.
import Base
import ./gemm_m16_partition.bend as M16
import ./draft_head_partition_spec.bend as Spec

# D: gw = blockIdx.x * HEAD_WARPS + warp
def gw(+b: Nat, +w: Nat) -> Nat:
  Nat.add(w, Nat.mul(16n, b))

# D: W = gridDim.x * HEAD_WARPS
def stride(+G: Nat) -> Nat:
  Nat.mul(16n, G)

# D: for (int tile = gw; tile < n_tiles; tile += W): the tiles warp w of block b computes, in order.
def tiles(+b: Nat, +w: Nat, +G: Nat, +n: Nat) -> List<&2, Nat>:
  M16.jobloop.go(1n+n, Nat.is_lt(gw(b, w), n), gw(b, w), stride(G), n)

# Number of warps w < count of block b whose loop computes tile x.
def warp_hits(+count: Nat, +b: Nat, +x: Nat, +G: Nat, +n: Nat) -> Nat:
  match count:
    case 0n:
      0n
    case 1n+w:
      Nat.add(warp_hits(w, b, x, G, n), Spec.bit(Spec.member(tiles(b, w, G, n), x)))

# Number of (block b < count, warp w < HEAD_WARPS = 16) whose loop computes tile x.
def tile_hits(+count: Nat, +x: Nat, +G: Nat, +n: Nat) -> Nat:
  match count:
    case 0n:
      0n
    case 1n+b:
      Nat.add(tile_hits(b, x, G, n), warp_hits(16n, b, x, G, n))

# D (per tile): for (int base = 0; base < CH; base += HEAD_DEPTH) { for j in 0..7 (unrolled): chunk
# c = base + j (weights rw[j], activations xs4[c * 64 + ..]); if (j & 1): fold with the scale rs[j]
# that the ring loaded for chunk c, i.e. group c >> 1 = c / 2 } (HEAD_DEPTH = 8; base + j is written
# j + base).
def body(+base: Nat, rest: List<&2, Spec.Ev>) -> List<&2, Spec.Ev>:
  Spec.Chunk{Nat.add(0n, base)} <> Spec.Chunk{Nat.add(1n, base)} <> Spec.Fold{Nat.div(Nat.add(1n, base), 2n)} <>
  Spec.Chunk{Nat.add(2n, base)} <> Spec.Chunk{Nat.add(3n, base)} <> Spec.Fold{Nat.div(Nat.add(3n, base), 2n)} <>
  Spec.Chunk{Nat.add(4n, base)} <> Spec.Chunk{Nat.add(5n, base)} <> Spec.Fold{Nat.div(Nat.add(5n, base), 2n)} <>
  Spec.Chunk{Nat.add(6n, base)} <> Spec.Chunk{Nat.add(7n, base)} <> Spec.Fold{Nat.div(Nat.add(7n, base), 2n)} <>
  rest

# The base loop; `go` is base < CH. `fuel` bounds the model only (tile_trace passes CH + 1; the law
# tile_order shows it never cuts the loop short).
def loop(fuel: Nat, go: Bool, +base: Nat, +CH: Nat) -> List<&2, Spec.Ev>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match go:
        case True{}:
          body(base, loop(f, Nat.is_lt(Nat.add(8n, base), CH), Nat.add(8n, base), CH))
        case False{}:
          Nil{}

def tile_trace(+CH: Nat) -> List<&2, Spec.Ev>:
  loop(1n+CH, Nat.is_lt(0n, CH), 0n, CH)
