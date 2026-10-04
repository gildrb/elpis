# Rounding-error Paths (bend/err_bound.bend) of the served decode GEMMs, per input term (leaf) of one
# output element: elpis (verify rows m = 1 .. 8, the kernels of m1map-map.json kernel_map 'verify')
# and the yardstick, stock ExLlamaV3 355c6ee non-speculative M = 1 decode. A Nat model of rounding
# STEP COUNTS by class; no floating-point value is modelled. Laws: bend/err_gemm_laws.bend.
#
# Op boundary. A linear y = had_out(svh, W^T had_in(suh, x)) consumes the fp16 activation x and
# ends at the value the next op reads (stored C, or for elpis's fused tail the fp32 value at the
# point where stock stores it). A leaf is one input element x_j on its way through one input
# Hadamard output xh_k, the product xh_k * w[k, n'], the accumulation into y'_n' and the output
# Hadamard into y_n. Every step on that way is counted, on both sides:
#   had_in   input scales + 128-point Hadamard (hadamard_inner.cuh:93-147 had_hf_r_128_inner<true,
#            false>): pre-scale __hmul2 (r16, :113-114), 2 fp32 butterfly levels (:122-129) + 5
#            warp-shuffle levels (shuffle_had_f4x32 :17-44, one fp32 add each, :39-42), * r_scale
#            (r32, :133), __floats2half2_rn (r16, :133-134):   r32 8, r16 2
#   dq       EXL3 mul1 (cb 2) codebook decode of the leaf's weight: decode_3inst_2<2> ->
#            decode_mul1_product_2, one __hfma2 (codebook.cuh:28-42, :117-122):   r16 1
#            (stock exl3_gemm_inner dq_dispatch -> exl3_dq.cuh decode_3inst_2, exl3_gemm_inner.cuh:307;
#            elpis m16_tile_diet -> dq8_m16_regs -> decode_3inst_2, exl3_m16_decode.cuh:37-55)
#   had_out  output Hadamard + svh: had_ff_r_128_inner<false, true> (hadamard_inner.cuh:151-212:
#            7 adds, * r_scale, * svh):   r32 9;   had_fh_r_128_inner<false, true> (:216-279:
#            7 adds, * r_scale, __floats2half2_rn, __hmul2 svh):   r32 8, r16 2;
#            had_hf_r_128_inner<false, true> (:93-147, half input):   r32 8, r16 2
# fp16 x fp16 products in an MMA or an fmaf, fp16 -> fp32 conversions, fp32 stores and adding an
# exact 0 are exact (no step). No series patch touches hadamard_inner.cuh, codebook.cuh, exl3_dq.cuh,
# exl3_gemm_inner.cuh, exl3_gemm_kernel.cuh or exl3_gemv_int8*.cu* (patches/exl3-ext/series: no hunk
# on these files), so the shared helpers are the same code on both sides.
#
# Line references: stock files under /tmp/kernel-work/PrecisionLaw/stock/exllamav3/exllamav3_ext/
# (GI: quant/exl3_gemm_inner.cuh, GK: quant/exl3_gemm_kernel.cuh, I8K: quant/exl3_gemv_int8_kernel.cuh,
# GDN: gdn.cu); elpis files of the series applied to that tree (patches/exl3-ext/series, 2102 .. 3023;
# G16: quant/exl3_gemm_m16g_kernel.cuh, T16: quant/exl3_tail_m16_kernel.cuh, M16: quant/exl3_mlp_m16_kernel.cuh).
# bend/err_gemm_diff.py checks the transcribed source fragments.
import Base
import ./err_bound.bend as Eb
import ./lmhead.bend as LH
import ./m16_diet.bend as Diet
import ./gemm_m16_wpart.bend as Wp
import ./tail_m16_sched.bend as TS
import ./mlp_m16_sched.bend as Mlp

# The served decode GEMMs (hidden 5120; attention q|gate 12288, k / v 1024, o 6144 -> 5120; GDN qkv
# 10240, z 6144, b/a 2 * 48 fp16 rows, out 6144 -> 5120; MLP 5120 -> 17408 -> 5120; lm_head).
type Op is Data:
  AttnQG{}
  AttnK{}
  AttnV{}
  GdnQkv{}
  GdnZ{}
  GdnBA{}
  AttnO{}
  GdnOut{}
  MlpGate{}
  MlpUp{}
  MlpDown{}
  LmHead{}

def bsel(c: Bool, +t: Nat, +f: Nat) -> Nat:
  match c:
    case True{}:
      t
    case False{}:
      f

def psel(c: Bool, t: Eb.Path, f: Eb.Path) -> Eb.Path:
  match c:
    case True{}:
      t
    case False{}:
      f

# A path of r32 / r16 / t16 steps only.
def seg(+r32: Nat, +r16: Nat, +t16: Nat) -> Eb.Path:
  Eb.Path{r32, 0n, r16, t16, 0n, 0n, 0n, 0n}

# ==== segments shared by both sides (header) ====

def had_in() -> Eb.Path:
  seg(8n, 2n, 0n)

def dq() -> Eb.Path:
  seg(0n, 1n, 0n)

def had_ff() -> Eb.Path:
  seg(9n, 0n, 0n)

def had_fh() -> Eb.Path:
  seg(8n, 2n, 0n)

def had_hf() -> Eb.Path:
  seg(8n, 2n, 0n)

# One fp16 store (__floats2half2_rn).
def st16() -> Eb.Path:
  seg(0n, 1n, 0n)

# ==== stock tensor-core kernel (exl3_gemm_kernel_inner), per leaf of a column's reduction order ====
# The order of an element (row r, column tile nt) is bend/lmhead.bend's Order: the blocks' segments of
# the column in lock order (LH.col_segs, GI:834-871), each the k-tiles of one block in that column
# followed by its one reduce() (a block's piece of a column is one fp16 run: reduce() runs at the
# column end or the slice end, GI:934 / 942), and the sub_k combine tree. Leaf (i, j, g): the j-th
# k-tile of the i-th segment in lock order, sub_k group g. Its steps:
#   - t16: the MMA of its tile and every later tile of the segment into frag_c_h (GI:884-896),
#     tiles(segment i) - j;
#   - the fold into frag_c (GI:801-827) adds to the cleared fp32 accumulator (clear_frag_c at GI:873
#     after every reduce and at GI:921 before the loop): exact;
#   - the sub_k combine (threadblock_reduce, GI:346-527): one r32 per Add above Leaf g (LH.Tree);
#   - cross-block: segment i > 0 reads the running partial and adds it (GI:844-847, :680-705: r32);
#     every later segment adds once more (r32 each); with fp16 C every non-last segment stores the
#     partial as fp16 (GI:850-853, write_sum_gl :711-796, __floats2half2_rn: r16), so the leaf passes
#     ns - 1 - i such stores; with fp32 C those stores are exact;
#   - output: mgemm (exl3_mgemm_kernel, shmem_out_had = false, GK:234-236): the last segment writes C
#     (GI:861 write_sum_gl: fp16 r16 / fp32 exact), then the separate output pass had_hf / had_ff
#     (GK:251-288); exl3_gemm_kernel (shmem_out_had = true, GK:39-41): write_sum_tile_sh (fp32 tile
#     in shared memory) and output_had_sh_gl (GI:594-618: had_ff / had_fh).

def ev_tiles(evs: List<&2, LH.Ev>) -> Nat:
  match evs:
    case Nil{}:
      0n
    case ev <> rest:
      match ev:
        case LH.Tile{n, k}:
          1n+ev_tiles(rest)
        case LH.Reduce{n}:
          ev_tiles(rest)

def nth_seg(segs: List<&2, List<&2, LH.Ev>>, i: Nat) -> List<&2, LH.Ev>:
  match segs:
    case Nil{}:
      Nil{}
    case s <> rest:
      match i:
        case 0n:
          s
        case 1n+p:
          nth_seg(rest, p)

def nsegs(segs: List<&2, List<&2, LH.Ev>>) -> Nat:
  match segs:
    case Nil{}:
      0n
    case s <> rest:
      1n+nsegs(rest)

def tree_has(t: LH.Tree, +g: Nat) -> Bool:
  match t:
    case LH.Leaf{i}:
      Nat.is_eq(i, g)
    case LH.Add{a, b}:
      Bool.or(tree_has(a, g), tree_has(b, g))

# r32 adds above Leaf g.
def tree_adds(t: LH.Tree, +g: Nat) -> Nat:
  match t:
    case LH.Leaf{i}:
      0n
    case LH.Add{+a, +b}:
      Nat.add(bsel(Bool.or(tree_has(a, g), tree_has(b, g)), 1n, 0n), Nat.add(tree_adds(a, g), tree_adds(b, g)))

def tc_out(+c32: Bool, +mg: Bool) -> Eb.Path:
  match mg:
    case True{}:
      psel(c32, had_ff(), Eb.add(st16(), had_hf()))
    case False{}:
      psel(c32, had_ff(), had_fh())

# The leaf's path in the order's own steps (MMAs, sub_k combine, cross-block exchange).
def tc_core(+segs: List<&2, List<&2, LH.Ev>>, +tb: LH.Tree, +i: Nat, +j: Nat, +g: Nat, +c32: Bool) -> Eb.Path:
  +later = Nat.sub(Nat.sub(nsegs(segs), 1n), i)
  seg(Nat.add(bsel(Nat.is_lt(0n, i), 1n, 0n), Nat.add(later, tree_adds(tb, g))), bsel(c32, 0n, later),
    Nat.sub(ev_tiles(nth_seg(segs, i)), j))

def tc_ord(o: LH.Order, +i: Nat, +j: Nat, +g: Nat, +c32: Bool) -> Eb.Path:
  match o:
    case LH.Order{segs, tb, wr, t0}:
      tc_core(segs, tb, i, j, g, c32)

# Full stock tensor-core leaf path: had_in, dq, the order's steps, the output.
def tc_path(o: LH.Order, +i: Nat, +j: Nat, +g: Nat, +c32: Bool, +mg: Bool) -> Eb.Path:
  Eb.add(Eb.add(had_in(), dq()), Eb.add(tc_ord(o, i, j, g, c32), tc_out(c32, mg)))

# ---- stock M = 1 projections: exl3_mgemm_kernel on the sliced bundles (precision_stock.bend
#      lines 391-397 records; GK:217-236 one exl3_gemm_kernel_inner per matrix, grid.x blocks) ----
# Attention bundle: slices of 1024 columns, k 5120, shape 4 (TILESIZE_K 16, TILESIZE_N 512, so
# TILEBLOCKS_K = 1: no sub_k combine), grid 4, fp16 C (modules/attn.py:531); GDN bundle: slices of
# 2048, grid 10, fp32 C (modules/gated_delta_net.py:717-726). Element in slice column tile nt
# (row 0 of the M = 1 call). The same steps as tc_core, in the column-piece form of the partition:
# block b's slice is [slice_beg, slice_end) = [c b, c (b + 1)) (GI:98-100: T b / G, and G divides
# the slice space T exactly here, c = T / G = 160 resp. 128: law partition_exact); its fp16 run in
# column nt is the slice cut to the column's k-tiles [nt tk, (nt + 1) tk) (law
# stock_runs_are_column_pieces of bend/precision_laws.bend: the runs of the stock loop are exactly
# these pieces); the column's pieces meet in descending k order, which is descending block order
# (GI:834-841, lmhead.bend col_segs): a piece with a non-empty piece of a higher block reads and adds
# the running partial (r32), every lower non-empty piece adds once more (r32) and, with fp16 C, each
# non-last piece stores the partial as fp16 (r16).
def piece(+b: Nat, +c: Nat, +tk: Nat, +nt: Nat) -> Nat:
  Nat.sub(Nat.min(Nat.mul(c, 1n+b), Nat.mul(1n+nt, tk)), Nat.max(Nat.mul(c, b), Nat.mul(nt, tk)))

# Blocks b .. b + left - 1 with a non-empty piece of column nt.
def pieces(left: Nat, +b: Nat, +c: Nat, +tk: Nat, +nt: Nat) -> Nat:
  match left:
    case 0n:
      0n
    case 1n+r:
      Nat.add(bsel(Nat.is_lt(0n, piece(b, c, tk, nt)), 1n, 0n), pieces(r, 1n+b, c, tk, nt))

# Leaf (b, j): the j-th k-tile of block b's piece of column nt.
def mg_core(+b: Nat, +j: Nat, +c: Nat, +G: Nat, +tk: Nat, +nt: Nat, +c32: Bool) -> Eb.Path:
  +hi = pieces(Nat.sub(Nat.sub(G, 1n), b), 1n+b, c, tk, nt)
  +lo = pieces(b, 0n, c, tk, nt)
  seg(Nat.add(bsel(Nat.is_lt(0n, hi), 1n, 0n), lo), bsel(c32, 0n, lo), Nat.sub(piece(b, c, tk, nt), j))

def mg_path(+b: Nat, +j: Nat, +c: Nat, +G: Nat, +tk: Nat, +nt: Nat, +c32: Bool) -> Eb.Path:
  Eb.add(Eb.add(had_in(), dq()), Eb.add(mg_core(b, j, c, G, tk, nt, c32), tc_out(c32, True{})))

def mg_leaf(+b: Nat, +j: Nat, +c: Nat, +G: Nat, +tk: Nat, +nt: Nat) -> Bool:
  Bool.and(Nat.is_lt(b, G), Nat.is_lt(j, piece(b, c, tk, nt)))

def is_attn(op: Op) -> Bool:
  match op:
    case AttnQG{}:
      True{}
    case AttnK{}:
      True{}
    case AttnV{}:
      True{}
    case GdnQkv{}:
      False{}
    case GdnZ{}:
      False{}
    case GdnBA{}:
      False{}
    case AttnO{}:
      False{}
    case GdnOut{}:
      False{}
    case MlpGate{}:
      False{}
    case MlpUp{}:
      False{}
    case MlpDown{}:
      False{}
    case LmHead{}:
      False{}

def is_proj(op: Op) -> Bool:
  match op:
    case AttnQG{}:
      True{}
    case AttnK{}:
      True{}
    case AttnV{}:
      True{}
    case GdnQkv{}:
      True{}
    case GdnZ{}:
      True{}
    case GdnBA{}:
      False{}
    case AttnO{}:
      False{}
    case GdnOut{}:
      False{}
    case MlpGate{}:
      False{}
    case MlpUp{}:
      False{}
    case MlpDown{}:
      False{}
    case LmHead{}:
      False{}

# Bundle of a projection: slice width c = T / G k-tiles per block (T = tiles of one slice, k 5120 x
# slice width at shape 4: 320 x 2 = 640 over grid 4, 320 x 4 = 1280 over grid 10), grid, k-tiles
# tk = 5120 / 16 per column, column tiles of a slice, fp32 C (laws partition_exact, shape_literals).
def proj_c(+op: Op) -> Nat:
  bsel(is_attn(op), 160n, 128n)

def proj_G(+op: Op) -> Nat:
  bsel(is_attn(op), 4n, 10n)

def proj_tk() -> Nat:
  320n

def proj_tn(+op: Op) -> Nat:
  bsel(is_attn(op), 2n, 4n)

# The stock M = 1 path of leaf (b, j) of a projection element in column tile nt.
def proj_stock(+op: Op, +nt: Nat, +b: Nat, +j: Nat) -> Eb.Path:
  mg_path(b, j, proj_c(op), proj_G(op), proj_tk(), nt, Bool.not(is_attn(op)))

def proj_leaf(+op: Op, +nt: Nat, +b: Nat, +j: Nat) -> Bool:
  mg_leaf(b, j, proj_c(op), proj_G(op), proj_tk(), nt)

# The stock witness of a projection element: the first k-tile of block wit_b's piece. Attention
# (2 x 320 k-tiles per slice over 4 blocks of 160): block 2 nt + 1, the first in its column's lock
# order (160 MMAs, an fp16 partial store, one add in block 2 nt, the fp16 C store); GDN (4 x 320
# over 10 blocks of 128): blocks 1, 3, 6, 8, each a full 128-tile piece with one higher and one
# lower piece in its column (two fp32 adds). Law witness_leaves: real leaves, with these paths.
def wit_b(+op: Op, +nt: Nat) -> Nat:
  bsel(is_attn(op), 1n+Nat.mul(2n, nt),
    bsel(Nat.is_eq(nt, 0n), 1n, bsel(Nat.is_eq(nt, 1n), 3n, bsel(Nat.is_eq(nt, 2n), 6n, 8n))))

def proj_wit(+op: Op, +nt: Nat) -> Eb.Path:
  proj_stock(op, nt, wit_b(op, nt), 0n)

# ---- stock M = 1 int8 GEMV (o_proj, out_proj, gate, up, down): exl3_gemv_int8_sq_kernel<4, 1,
#      c_fp32, residual = false> (EXL3_INT8_GEMV unset = 2, plain int8; I8K:765-1043) ----
# The witness: a leaf of k-slice 0, through the accumulator term of the epilogue:
#   had_in (I8K:823 had_hf_r_128_inner<true, false> while staging the slice);
#   quantize (I8K:842, :847-849): rq = 1.0f / q_s (rcp), a * rq (r32), __float2int_rn (q8);
#   dp4a with the exact mul1 codebook bytes, int32 accumulation and plain int32 partial stores:
#   exact (I8K:20-31, :60-65, :327-460);
#   epilogue (I8K:893-947): (float) partial (cvt.rn.f32.s32: r32), acc[i] += q_s * (float) p (one
#   fma per slice; slice 0's adds to 0.0f, every later slice's fma rounds again: 1 + (ksplit - 1)
#   r32), tmp = k_inv * acc[i] + corr (one fma: r32);
#   output: had_ff (fp32 C: o_proj / out_proj / down, out_dtype torch.float, architecture/qwen3_5.py
#   :351, :382, :436) or had_fh (fp16 C: gate / up, interm_dtype torch.half, :435).
# ksplit (the number of k-slices, I8K:985-988) is any value: the laws hold for every ksplit.
def i8_quant() -> Eb.Path:
  Eb.Path{1n, 0n, 0n, 0n, 1n, 0n, 1n, 0n}

def i8_epi(+ks: Nat) -> Eb.Path:
  seg(Nat.add(3n, Nat.sub(ks, 1n)), 0n, 0n)

def i8_wit(+ks: Nat, +c32: Bool) -> Eb.Path:
  Eb.add(Eb.add(had_in(), i8_quant()), Eb.add(i8_epi(ks), psel(c32, had_ff(), had_fh())))

def fp32_out(op: Op) -> Bool:
  match op:
    case AttnQG{}:
      False{}
    case AttnK{}:
      False{}
    case AttnV{}:
      False{}
    case GdnQkv{}:
      True{}
    case GdnZ{}:
      True{}
    case GdnBA{}:
      True{}
    case AttnO{}:
      True{}
    case GdnOut{}:
      True{}
    case MlpGate{}:
      False{}
    case MlpUp{}:
      False{}
    case MlpDown{}:
      True{}
    case LmHead{}:
      False{}

def is_tail(op: Op) -> Bool:
  match op:
    case AttnQG{}:
      False{}
    case AttnK{}:
      False{}
    case AttnV{}:
      False{}
    case GdnQkv{}:
      False{}
    case GdnZ{}:
      False{}
    case GdnBA{}:
      False{}
    case AttnO{}:
      True{}
    case GdnOut{}:
      True{}
    case MlpGate{}:
      True{}
    case MlpUp{}:
      True{}
    case MlpDown{}:
      True{}
    case LmHead{}:
      False{}

def tail_wit(+op: Op, +ks: Nat) -> Eb.Path:
  i8_wit(ks, fp32_out(op))

# ---- stock M = 1 b/a: gdn_ba_gemv_kernel (GDN:1626-1669; BC_GatedDeltaNetSplit,
#      libtorch/gated_delta_net.cpp:278, modules/gated_delta_net.py:658-690) ----
# One warp per output row: lane l chains sum = fmaf(xf, wf, sum) over half2 j = l, l + 32, ..
# (k / 2 / 32 = 80 half2, 160 fmaf, GDN:1652-1659; the first onto 0.0f is exact), 5 shuffle-down
# adds (GDN:1661-1662), `if (bias) sum += bias` (GDN:1666). Witness: lane 0, chain position 0:
# 159 later fmaf + 5 adds (+ the bias add).
def ba_bias(hb: Bool) -> Nat:
  bsel(hb, 1n, 0n)

# k / 2 / 32 half2 per lane, 2 fmaf each (literal 160; law shape_literals).
def ba_chain() -> Nat:
  160n

def ba_wit(+hb: Bool) -> Eb.Path:
  seg(Nat.add(Nat.add(Nat.sub(ba_chain(), 1n), 5n), ba_bias(hb)), 0n, 0n)

# ==== elpis ====

# The served m16 fold cadence FO (k16 tiles per fp16 run, ext 3023 fold-32: bend/m16_diet.bend
# cfg_fold = 2), the m16g k-tiles per group KT = 5120 / 16 and grid 164 (gemm_m16_wpart.bend
# kt_served / grid_served), the tail phases' KT0 = 6144 / 16, KT1 = 5120 / 16, KT2 = 17408 / 16 and
# grid 164 (tail_m16_sched.bend kt0, mlp_m16_sched.bend kt1 / kt2 / grid). The literals below are
# those defs' values (law shape_literals); literals keep the kernel's evaluation small.
def fo() -> Nat:
  Diet.cfg_fold()

def op_kt(op: Op) -> Nat:
  match op:
    case AttnQG{}:
      320n
    case AttnK{}:
      320n
    case AttnV{}:
      320n
    case GdnQkv{}:
      320n
    case GdnZ{}:
      320n
    case GdnBA{}:
      0n
    case AttnO{}:
      384n
    case GdnOut{}:
      384n
    case MlpGate{}:
      320n
    case MlpUp{}:
      320n
    case MlpDown{}:
      1088n
    case LmHead{}:
      0n

def op_grid(op: Op) -> Nat:
  164n

# ---- the m16 kernels (m16g for the projections at m = 2 .. 8, the 8202 tail for o_proj / out_proj
#      and 8201's gate / up / down at m = 1 .. 8; MT = 1) ----
# Leaf (tr, own, fa, pa) of an output element:
#   tr   MMAs into the fp16 accumulator hacc from the leaf's tile to its run's fold (its own included;
#        G16:347 / exl3_m16_decode.cuh:92 ptx_mma_m16n8k16 into hacc; fold every FO tiles and at the
#        segment end, G16:445, :450, T16:504, :532): t16 = tr, 1 <= tr <= FO (law fold_runs_m16g /
#        fold_runs_tail of bend/precision_laws.bend: every run is at most FO tiles);
#   own  1 iff the leaf's run is not the first of its segment: fold() adds hacc into acc (G16:284-298),
#        which is 0.0f before the segment's first fold (G16:281, zeroed again by flush G16:315), so the
#        first run's fold is exact;
#   fa   folds of the later runs of the segment (r32 each); a segment lies in one group of KT k-tiles
#        (G16:401 seg_end = min(e_b, (g_cur + 1) * KT) - s_b), so fa <= KT;
#   pa   finisher adds after the leaf's slot (G16:470-478, T16:592-597, :730-735, :809-814: v = slot 0,
#        v += slot c for c = 1 .. nc - 1, so slot 0 and 1 pass nc - 1 adds, slot c nc - c); slots are
#        distinct contributing blocks of the grid (gemm_m16_wpart_laws.bend contrib_bounds,
#        slot_in_range), so pa <= nc - 1 <= grid - 1.
# Flush stores (G16:314 __stcg fp32) are exact. Input: had_in (G16:231-237; T16:264, :291, :295
# exl3_m16_had_load / _store = had_hf_r_128_inner<true, false>, M16:40, :101-120; T16:683-684 gate / up;
# T16:756 down). Output: attention q / k / v had_fh into the fp16 q / kv buffers (G16:497-503,
# libtorch/attention.cpp:553-563), GDN qkv / z had_ff into fp32 (G16:489-495,
# libtorch/gated_delta_net.cpp:278), o_proj / out_proj had_ff into yo (T16:603), gate / up had_fh
# (T16:738), down had_ff (T16:819).
def m16_out(+op: Op) -> Eb.Path:
  psel(fp32_out(op), had_ff(), had_fh())

def m16_const(+op: Op, +tr: Nat) -> Eb.Path:
  Eb.add(Eb.add(had_in(), dq()), Eb.add(seg(0n, 0n, tr), m16_out(op)))

def m16_var(+own: Nat, +fa: Nat, +pa: Nat) -> Eb.Path:
  seg(Nat.add(own, Nat.add(fa, pa)), 0n, 0n)

def m16_path(+op: Op, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat) -> Eb.Path:
  Eb.add(m16_const(op, tr), m16_var(own, fa, pa))

# The coordinate bounds of a real m16 leaf of op (see above).
def m16_leaf(+op: Op, +tr: Nat, +own: Nat, +fa: Nat, +pa: Nat) -> Bool:
  Bool.and(Nat.is_le(1n, tr), Bool.and(Nat.is_le(tr, fo()), Bool.and(Nat.is_le(own, 1n),
    Bool.and(Nat.is_le(fa, op_kt(op)), Nat.is_le(1n+pa, op_grid(op))))))

# pa of a leaf in finisher slot c of a group with nc contributors (G16:470-478: v = slot 0, then
# v += slot c for c = 1 .. nc - 1): slots 0 and 1 pass nc - 1 adds, slot c >= 1 passes nc - c.
def fin_adds(+c: Nat, +nc: Nat) -> Nat:
  bsel(Nat.is_eq(c, 0n), Nat.sub(nc, 1n), Nat.sub(nc, c))

# ---- elpis b/a: gdn_conv_rule_norm_kernel, KS = 1 / 2 (ext 5106; bend/gdn_ba_ksplit.bend task) ----
# Per (thread, row): 10 fmaf from ZeroF (GR_KS_ITERS = 5 iterations x 2 components, gdn_ba_ksplit.bend
# accs / fma2; every j = warp * 32 + lane + 512 i < k2 = 2560); lane 0's value after the 5-level
# shuffle-down tree (tree); 16 warp partials summed from 0.0f in warp order (rsum: Add{ZeroF, p0} is
# exact, partial 0 then passes 15 adds, partial w >= 1 16 - w); the bias add (with_bias).
# Leaf (p, w): chain position p < 10, warp w < 16.
def ba_fma(+p: Nat) -> Nat:
  bsel(Nat.is_eq(p, 0n), 9n, Nat.sub(10n, p))

def ba_rs(+w: Nat) -> Nat:
  bsel(Nat.is_eq(w, 0n), 15n, Nat.sub(16n, w))

def ba_path(+p: Nat, +w: Nat, +hb: Bool) -> Eb.Path:
  seg(Nat.add(Nat.add(ba_fma(p), Nat.add(5n, ba_rs(w))), ba_bias(hb)), 0n, 0n)

# ---- elpis at m = 1 on the projections: the site's own sliced exl3_mgemm (route M16G_OLD,
#      2102-proj-m16-grouped-v2-on3003-5101.patch:283-295; m1map 'm1' kernel exl3_mgemm_kernel
#      'identical'), i.e. the stock leaf path ----
def proj_m1(+op: Op, +nt: Nat, +b: Nat, +j: Nat) -> Eb.Path:
  proj_stock(op, nt, b, j)

# ---- lm_head: the stock exl3_gemm_gr / exl3_gemm_kernel on every row (bend/lmhead.bend), row r
#      of an m-row verify call vs row 0 of the stock 1-row call ----
def head_path(+k: Nat, +n: Nat, +nt: Nat, +m: Nat, +r: Nat, +i: Nat, +j: Nat, +g: Nat, +c32: Bool) -> Eb.Path:
  tc_path(LH.elem_order(LH.served_tab(), 6n, k, n, m, r, nt), i, j, g, c32, False{})
