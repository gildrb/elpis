# Rounding-error paths (vocabulary bend/err_bound.bend) of the decode norms and elementwise ops of
# the served verify path (elpis, rows m = 1..8; every row is computed independently, so one row is
# modeled) and of stock ExLlamaV3 355c6ee M = 1 decode: the RMSNorms (attention / GDN input norm,
# post-attention norm, final norm), the residual adds and stream precision, SiLU(gate) * up, and the
# dtypes of the tensors handed between kernels. Laws: bend/err_elem_laws.bend.
#
# Sources (file:line). Stock: OUT/stock of bend/engine_trees.py (clean 355c6ee), written
# "S:<file>:<line>". Elpis: the stock package with patches/exl3/series then patches/exl3-ext/series
# applied by the repository's applier (bend/err_elem_diff.py builds it), written "E:<file>:<line>
# (<patch>)". bend/err_elem_diff.py checks every transcribed fragment against both trees.
#
# Served routes (m1map: m1map-map.json of bend/err_elem_diff.py --m1map DIR, kernel_map, side
# 'verify', and m1map-stock.json side 'm1_stock'):
#   elpis verify: input norm = rms_norm_kernel (every GDN / attention layer and the final norm);
#     o_proj + residual add + post-attention norm + MLP = exl3_tail_m16_kernel (ext 8202, all 64
#     layers); the closing MLP residual add is folded into the next input norm (ext 7001 RES_IN) or
#     is a torch add (at::native CUDAFunctor_add<float>) where not deferred.
#   stock M = 1: input / post-attention / final norm = rms_norm_kernel (post-attention one with
#     RES_IN, S:modules/transformer.py:168,182), SiLU * up = act_mul_kernel_h (BC_GatedMLP,
#     S:exllamav3_ext/libtorch/mlp.cpp:81-82), MLP residual = torch add (S:modules/transformer.py:195).
#
# Hypotheses (each used by the models below, none assumed by a law):
#   H_model    Higham's standard model per rounding step (no overflow, underflow or subnormal
#              results; both builds flush subnormals alike under --use_fast_math, S:ext.py:92,
#              E:ext.py:92, and the repository root's setup.py line 23), so a step is a factor (1 + d), |d| <= u of its class.
#   H_sass     The division `sum / (float) dim` (runtime dim; stock and elpis rms_norm_kernel)
#              compiles to MUFU.RCP of dim then one FFMA with epsilon (rcp + r32), and the tail's
#              `sum / (float) N0` (constexpr N0 = 5120) to one FFMA with the fp32 constant
#              0x394ccccd = RN(1/5120) (r32 + r32). Observed in the SASS (sm_86, nvcc 12.9,
#              -O3 --use_fast_math) of rms_norm_kernel<2, float, half, bf16, float> and
#              exl3_tail_m16_kernel<0, 2> in the elpis extension
#              .so given to bend/err_elem_diff.py --sass (MUFU.RCP + FFMA.FTZ + MUFU.RSQ;
#              MOV R30, 0x394ccccd + FFMA.FTZ + MUFU.RSQ) and in a probe compile of both
#              expressions. h2exp compiles to an exact f16 -> f32 conversion, FFMA by log2(e)
#              (r32), MUFU.EX2 (ex2) and F2FP (r16, the HSET2 / HFMA2 fix-ups only replace the
#              result at a few special inputs by its correctly rounded fp16 value); h2rcp to an exact
#              conversion, MUFU.RCP (rcp) and F2FP (r16). Both sides call the same intrinsics, so
#              those two segments are common to both paths.
#   H_torch    torch's fp32 `x += y` (CUDAFunctor_add<float>, alpha = 1) rounds once: alpha * y is
#              exact for alpha = 1 and a contracted FMA gives RN(x + y) as well.
#   H_leaf     Leaves: a norm's leaves are the fp32 residual-stream elements it reads (in the RES_IN
#              kernels the stream value is the rounded add, stored fp32 and reread, so the add is
#              the residual-add op's own step, law resid_*) and the norm weight; the activation's
#              leaves are the fp16 gate / up elements (their production is the GEMM laws' output
#              path). A leaf entering an output along two routes (x_j directly and through the sum
#              of squares; the gate through the sigmoid and directly) is two terms, one per route.
#   H_shape    Served shape: hidden size D = 5120 = 4 * 1280 columns of float4 per row; the
#              rms_norm_kernel launch uses MIN(1024, CEIL(1280 / 32) * 32) = 1024 threads
#              (S:exllamav3_ext/norm.cu:377, E:exllamav3_ext/norm.cu:431), i.e. 32 warps.
import Base
import ./err_bound.bend as Eb

# ==== path segments ====

def r32(n: Nat) -> Eb.Path:
  Eb.Path{n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

def r16(n: Nat) -> Eb.Path:
  Eb.Path{0n, 0n, n, 0n, 0n, 0n, 0n, 0n}

def ex2(n: Nat) -> Eb.Path:
  Eb.Path{0n, 0n, 0n, 0n, 0n, n, 0n, 0n}

def rcp(n: Nat) -> Eb.Path:
  Eb.Path{0n, 0n, 0n, 0n, 0n, 0n, n, 0n}

def rsq(n: Nat) -> Eb.Path:
  Eb.Path{0n, 0n, 0n, 0n, 0n, 0n, 0n, n}

def cat(p: Eb.Path, q: Eb.Path) -> Eb.Path:
  Eb.add(p, q)

# ==== tensor dtypes between kernels ====

type Dt is Data:
  DF32{}
  DF16{}

# Storing an fp32 result as dt: fp32 is exact, fp16 is one cvt.rn.f16.f32 (__float2half_rn).
def store(d: Dt) -> Eb.Path:
  match d:
    case DF32{}:
      Eb.zero()
    case DF16{}:
      r16(1n)

# The tensors handed between the kernels of one block on the served route.
type Ten is Data:
  TStream{}    # residual stream x
  TNormOut{}   # input norm output (attention / GDN input)
  TSubOut{}    # attention / GDN output after o_proj (the sublayer output added to x)
  TMlpIn{}     # post-attention norm output (gate / up input)
  TGateUp{}    # gate and up projections (SiLU * up input)
  TActOut{}    # SiLU(gate) * up (down input)
  TMlpOut{}    # down projection output (the MLP output added to x)
  TFinalOut{}  # final norm output (lm_head input)

# Stock 355c6ee M = 1.
def stock_dtype(t: Ten) -> Dt:
  match t:
    case TStream{}:
      DF32{}     # S:modules/embedding.py:19 out_dtype = torch.float; blocks add in place
    case TNormOut{}:
      DF16{}     # S:modules/transformer.py:156 attn_norm.forward(x, params, out_dtype = torch.half)
    case TSubOut{}:
      DF32{}     # S:architecture/qwen3_5.py:351,382 attention / GDN out_dtype = torch.float
    case TMlpIn{}:
      DF16{}     # S:modules/transformer.py:182 mlp_norm.forward(..., out_dtype = torch.half, residual_in = x)
    case TGateUp{}:
      DF16{}     # S:architecture/qwen3_5.py:435 GatedMLP interm_dtype = torch.half, S:exllamav3_ext/activation.cu:71 act_mul_kernel_h
    case TActOut{}:
      DF16{}     # S:exllamav3_ext/activation.cu:47 TORCH_CHECK_DTYPE(z, kHalf)
    case TMlpOut{}:
      DF32{}     # S:architecture/qwen3_5.py:436 GatedMLP out_dtype = torch.float
    case TFinalOut{}:
      DF16{}     # S:architecture/qwen3_5.py:463 final RMSNorm out_dtype = torch.half

# Elpis verify (rows m = 1..8).
def elpis_dtype(t: Ten) -> Dt:
  match t:
    case TStream{}:
      DF32{}     # E:modules/transformer.py:128 the layer tail requires x.dtype == torch.float (8202); E:exllamav3_ext/quant/exl3_tail_m16_kernel.cuh:74 float* X
    case TNormOut{}:
      DF16{}     # E:modules/transformer.py:233,235 attn_norm.forward(..., out_dtype = torch.half)
    case TSubOut{}:
      DF32{}     # E:exllamav3_ext/quant/exl3_tail_m16_kernel.cuh:49 float* yo (o_proj output inside the tail)
    case TMlpIn{}:
      DF16{}     # E:exllamav3_ext/quant/exl3_tail_m16_kernel.cuh:50,680-681 half* xn, __float2half_rn
    case TGateUp{}:
      DF16{}     # E:exllamav3_ext/quant/exl3_tail_m16_kernel.cuh:61-62 half* g, half* u
    case TActOut{}:
      DF16{}     # E:exllamav3_ext/quant/exl3_tail_m16_kernel.cuh:751 half2* ap = (half2*) (q.a + o)
    case TMlpOut{}:
      DF32{}     # E:exllamav3_ext/quant/exl3_tail_m16_kernel.cuh:74,819 float* D, had_ff (fp32 out)
    case TFinalOut{}:
      DF16{}     # E:architecture/qwen3_5.py:463 final RMSNorm out_dtype = torch.half (unpatched)

# ==== residual adds ====

# Routes that add a sublayer output to the residual stream.
type ERes is Data:
  ETail{}     # attention / GDN residual: tail F0, y4 = yo + r4 (E:exllamav3_ext/quant/exl3_tail_m16_kernel.cuh:611-615, 8202)
  EResIn{}    # MLP residual folded into the next input norm (rms_norm RES_IN, E:exllamav3_ext/norm.cu:227-230,319, 7001)
  ETorch{}    # MLP residual not deferred (last block, unlinked): x += y (E:modules/transformer.py:257,296)

type SRes is Data:
  SResIn{}    # attention / GDN residual folded into the post-attention norm (S:exllamav3_ext/norm.cu:209-212, S:modules/transformer.py:182)
  STorch{}    # MLP residual: x += y (S:modules/transformer.py:195)

# The two leaves of an add: the sublayer output element and the residual element.
type RLeaf is Data:
  RSub{}
  RRes{}

# Every route is one fp32 add (FADD; H_torch for the torch add) whose result is stored to the
# fp32 stream; both operands take the same rounding.
def elpis_res(e: ERes, l: RLeaf) -> Eb.Path:
  match e:
    case ETail{}:
      cat(r32(1n), store(elpis_dtype(TStream{})))
    case EResIn{}:
      cat(r32(1n), store(elpis_dtype(TStream{})))
    case ETorch{}:
      cat(r32(1n), store(elpis_dtype(TStream{})))

def stock_res(s: SRes, l: RLeaf) -> Eb.Path:
  match s:
    case SResIn{}:
      cat(r32(1n), store(stock_dtype(TStream{})))
    case STorch{}:
      cat(r32(1n), store(stock_dtype(TStream{})))

# The stock add an elpis add replaces: the attention / GDN residual is stock's RES_IN add, the MLP
# residual is stock's torch add.
def res_witness(e: ERes) -> SRes:
  match e:
    case ETail{}:
      SResIn{}
    case EResIn{}:
      STorch{}
    case ETorch{}:
      STorch{}

# ==== RMSNorm ====

# The float4 component of a column, in sum_sq4's fma order (S:exllamav3_ext/norm.cu:101-108).
type Comp is Data:
  CX{}
  CY{}
  CZ{}
  CW{}

def comp_ix(k: Comp) -> Nat:
  match k:
    case CX{}:
      0n
    case CY{}:
      1n
    case CZ{}:
      2n
    case CW{}:
      3n

def guard(g: Bool) -> Nat:
  match g:
    case True{}:
      1n
    case False{}:
      0n

# Served rms_norm_kernel shape (H_shape): 1280 float4 columns, 1024 threads, 32 warps.
def cols() -> Nat:
  1280n

def nthreads() -> Nat:
  1024n

# Stock thread t's column count: the strided loop
#   for (int column = t; column < columns; column += blockDim.x)            S:exllamav3_ext/norm.cu:285
# run with `fuel` iterations at most (fuel = columns suffices: the column grows by blockDim.x >= 1).
def strided(fuel: Nat, g: Bool, +col: Nat, +n: Nat, +stride: Nat) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      match g:
        case True{}:
          1n+strided(f, Nat.is_lt(Nat.add(col, stride), n), Nat.add(col, stride), n, stride)
        case False{}:
          0n

def stock_ncols(+t: Nat) -> Nat:
  strided(cols(), Nat.is_lt(t, cols()), t, cols(), nthreads())

# Elpis thread t's column count: the register-resident branch (taken: columns <= REG_COLS *
# blockDim.x, E:exllamav3_ext/norm.cu:294-295, 7001), REG_COLS = 2 unrolled:
#   int column = t + i * blockDim.x; if (column < columns) ... sum = sum_sq4(sum, x4[i]);   E:exllamav3_ext/norm.cu:313-321
def elpis_ncols(+t: Nat) -> Nat:
  Nat.add(guard(Nat.is_lt(t, cols())), guard(Nat.is_lt(Nat.add(t, nthreads()), cols())))

# The register branch's guard, evaluated at the served shape.
def reg_branch() -> Bool:
  Nat.is_le(cols(), Nat.mul(2n, nthreads()))

# The fma steps a leaf's square passes through in its thread's chain: sum_sq4 is
# lsum = fma(x, x, lsum) per component (S:exllamav3_ext/norm.cu:103-106, E:exllamav3_ext/norm.cu:119-122), thread chains over its
# columns in order, so the leaf at (column i of the thread, component k) is rounded by its own fma
# and every later one: 4 n - (4 i + k).
def chain(n: Nat, +i: Nat, k: Comp) -> Nat:
  Nat.sub(Nat.mul(4n, n), Nat.add(Nat.mul(4n, i), comp_ix(k)))

# reduce_dyn (S:exllamav3_ext/norm.cu:140-151 = E:exllamav3_ext/norm.cu:156-167): 5 xor-shuffle
# adds within the warp, and with more than one warp 5 more over the warp sums: 32 warps -> 10.
def reduce_steps() -> Nat:
  10n

# rmf = rsqrtf(sum / (float) dim + epsilon) * constant_scale (S:exllamav3_ext/norm.cu:293,
# E:exllamav3_ext/norm.cu:324) by H_sass: MUFU.RCP of dim (rcp), FFMA (r32), MUFU.RSQ (rsq),
# FMUL by constant_scale (r32).
def rmf_rt() -> Eb.Path:
  cat(rcp(1n), cat(r32(1n), cat(rsq(1n), r32(1n))))

# Tail: rmf = rsqrtf(sum / (float) N0 + p.eps) * p.nscale with constexpr N0
# (E:exllamav3_ext/quant/exl3_tail_m16_kernel.cuh:643, 8202) by H_sass: the constant RN(1/5120)
# (r32), FFMA (r32), MUFU.RSQ (rsq), FMUL by nscale (r32).
def rmf_tail() -> Eb.Path:
  cat(r32(1n), cat(r32(1n), cat(rsq(1n), r32(1n))))

# apply4: x * w * rmf (S:exllamav3_ext/norm.cu:112-115, E:exllamav3_ext/norm.cu:128-131 called at 266, and
# E:exllamav3_ext/quant/exl3_tail_m16_kernel.cuh:674-677): two FMULs, then the output store
# (__float2half_rn, S:exllamav3_ext/norm.cu:79 and E:exllamav3_ext/norm.cu:95 write_half4,
# E:exllamav3_ext/quant/exl3_tail_m16_kernel.cuh:680-681).
# The x term passes both FMULs, the rmf term the second only. The weight term first takes
# w + constant_bias (one FADD, S:exllamav3_ext/norm.cu:239-242, E:exllamav3_ext/norm.cu:255-258,
# E:exllamav3_ext/quant/exl3_tail_m16_kernel.cuh:669-672; the bf16 / fp16 -> fp32 read is exact).

# Leaves of one output element y_j of a rms_norm_kernel row (H_leaf): x_j by the direct route,
# w_j, and the element x at (thread t, its column i, component k) through the sum of squares.
type NLeaf is Data:
  NIn{}
  NW{}
  NSq{t: Nat, i: Nat, k: Comp}

# Leaves of one output element of the tail's post-attention norm: x_j, w_j, and the element x at
# (chunk ch of 128 columns, lane, component k) through the sum of squares.
type TLeaf is Data:
  TIn{}
  TW{}
  TSq{ch: Nat, lane: Nat, k: Comp}

def norm_out(ssq: Eb.Path, d: Dt) -> Eb.Path:
  cat(ssq, cat(r32(1n), store(d)))

# Stock rms_norm_kernel (strided branch: 1280 columns > 1024 threads, S:exllamav3_ext/norm.cu:195,282-307),
# output dtype d.
def stock_norm(l: NLeaf, d: Dt) -> Eb.Path:
  match l:
    case NIn{}:
      cat(r32(2n), store(d))
    case NW{}:
      cat(r32(3n), store(d))
    case NSq{+t, +i, k}:
      norm_out(cat(r32(Nat.add(chain(stock_ncols(t), i, k), reduce_steps())), rmf_rt()), d)

# Elpis rms_norm_kernel (register branch), output dtype d.
def elpis_norm(l: NLeaf, d: Dt) -> Eb.Path:
  match l:
    case NIn{}:
      cat(r32(2n), store(d))
    case NW{}:
      cat(r32(3n), store(d))
    case NSq{+t, +i, k}:
      norm_out(cat(r32(Nat.add(chain(elpis_ncols(t), i, k), reduce_steps())), rmf_rt()), d)

# A stock / plain-elpis sum-of-squares leaf is real when its thread exists and owns that column.
def stock_leaf_ok(l: NLeaf) -> Bool:
  match l:
    case NIn{}:
      True{}
    case NW{}:
      True{}
    case NSq{+t, +i, k}:
      Bool.and(Nat.is_lt(t, nthreads()), Nat.is_lt(i, stock_ncols(t)))

def thread_ok(l: NLeaf) -> Bool:
  match l:
    case NIn{}:
      True{}
    case NW{}:
      True{}
    case NSq{+t, i, k}:
      Nat.is_lt(t, nthreads())

# Tail norm (E:exllamav3_ext/quant/exl3_tail_m16_kernel.cuh:579-685, 8202). Sum of squares of the
# element at (chunk ch, lane, component k):
#   F0: ss = fma(y4.x, y4.x, ss) ... fma(y4.w, ...) (lines 616-620): 4 - k fma roundings;
#       5 xor-shuffle adds (621-622), stored per chunk to ssq[r][ch] (623);
#   N:  lane L reads chunk L and, when L + 32 < NCH = 40, adds chunk L + 32 (639-640): one more
#       add for chunks 0..7 and 32..39; then 5 xor-shuffle adds (641-642).
def tail_extra(+ch: Nat) -> Bool:
  Bool.or(Nat.is_lt(ch, 8n), Nat.is_le(32n, ch))

def tail_ssq(k: Comp, b: Bool) -> Eb.Path:
  r32(Nat.add(Nat.sub(4n, comp_ix(k)), Nat.add(5n, Nat.add(guard(b), 5n))))

def elpis_tail(l: TLeaf) -> Eb.Path:
  match l:
    case TIn{}:
      cat(r32(2n), store(elpis_dtype(TMlpIn{})))
    case TW{}:
      cat(r32(3n), store(elpis_dtype(TMlpIn{})))
    case TSq{+ch, lane, k}:
      norm_out(cat(tail_ssq(k, tail_extra(ch)), rmf_tail()), elpis_dtype(TMlpIn{}))

# The stock post-attention norm leaf each tail leaf is compared with: the same role for the direct
# and weight routes; for the sum of squares the stock leaf with the longest fma chain, thread 0's
# first column, component x (8 fmas: thread 0 owns columns 0 and 1024).
def tail_witness(l: TLeaf) -> NLeaf:
  match l:
    case TIn{}:
      NIn{}
    case TW{}:
      NW{}
    case TSq{ch, lane, k}:
      NSq{0n, 0n, CX{}}

# ==== SiLU(gate) * up ====

# One half2 lane of act_mul_kernel_h<ACT_SILU> (S:exllamav3_ext/activation_kernels.cuh:22-31,169-185) and
# of exl3_mlp_act_mul_h2 (E:exllamav3_ext/quant/exl3_mlp_m16_kernel.cuh:138-160, 8201; called by the tail,
# E:exllamav3_ext/quant/exl3_tail_m16_kernel.cuh:752-753), act_limit = 0 (no clamp), as operation lists.
type AOp is Data:
  HNeg{}     # neg_x = __hneg2(x): exact
  HExp{}     # e = h2exp(neg_x): r32 + ex2 + r16 (H_sass)
  HAdd1{}    # sum = __hadd2(one, e): r16
  HRcp{}     # r = h2rcp(sum): rcp + r16 (H_sass)
  HMulX{}    # result = __hmul2(x, r): r16
  HMulY{}    # z = __hmul2(silu, y): r16

def aop_path(o: AOp) -> Eb.Path:
  match o:
    case HNeg{}:
      Eb.zero()
    case HExp{}:
      cat(r32(1n), cat(ex2(1n), r16(1n)))
    case HAdd1{}:
      r16(1n)
    case HRcp{}:
      cat(rcp(1n), r16(1n))
    case HMulX{}:
      r16(1n)
    case HMulY{}:
      r16(1n)

def stock_act_ops() -> List<AOp>:
  [HNeg{}, HExp{}, HAdd1{}, HRcp{}, HMulX{}, HMulY{}]

def elpis_act_ops() -> List<AOp>:
  [HNeg{}, HExp{}, HAdd1{}, HRcp{}, HMulX{}, HMulY{}]

# Routes of a leaf into a = silu(g) * u (H_leaf): the gate through the sigmoid (enters at hneg),
# the gate directly (enters at the x * r product), the up value (enters at the final product).
type ALeaf is Data:
  AGateSig{}
  AGateDir{}
  AUp{}

# The position of the operation a route enters at in the operation list (hneg, h2exp, hadd2,
# h2rcp, hmul2 x, hmul2 y): the route passes that operation and every later one.
def a_entry(l: ALeaf) -> Nat:
  match l:
    case AGateSig{}:
      0n
    case AGateDir{}:
      4n
    case AUp{}:
      5n

def path_all(ops: List<AOp>) -> Eb.Path:
  match ops:
    case Nil{}:
      Eb.zero()
    case Con{o, t}:
      cat(aop_path(o), path_all(t))

def drop_ops(n: Nat, ops: List<AOp>) -> List<AOp>:
  match n:
    case 0n:
      ops
    case 1n+p:
      match ops:
        case Nil{}:
          Nil{}
        case Con{o, t}:
          drop_ops(p, t)

def stock_act(l: ALeaf) -> Eb.Path:
  path_all(drop_ops(a_entry(l), stock_act_ops()))

def elpis_act(l: ALeaf) -> Eb.Path:
  path_all(drop_ops(a_entry(l), elpis_act_ops()))
