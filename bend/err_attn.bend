# Rounding-error paths (vocabulary bend/err_bound.bend) of decode attention in the 16 full-attention
# layers of Qwen3.8-27B (24 q / 4 kv heads of 256, q/k RMSNorm, partial RoPE, GQA group 6, CQ3 K/V
# cache, interleaved output gate): elpis's verify kernels (rows m = 1..8; a row's arithmetic depends
# only on its absolute position, bend/attn_stride_laws.bend row_invariant, bend/attn_tree_laws.bend
# sees_path) against stock ExLlamaV3 355c6ee M = 1 decode. Laws: bend/err_attn_laws.bend (contract:
# pre stage) and bend/err_attn_finding_laws.bend (the current core's gap).
#
# SCOPE: the attention-core part of this model and its finding describe the verify kernels BEFORE ext
# 3030 (patches/exl3-ext series up to 3029: 3006 / 3007 / 3012). Ext 3030 fixes the four causes below;
# the 3030 kernels are modelled by bend/err_attn_dec.bend (laws bend/err_attn_dec_laws.bend: dominated
# at every L). bend/err_attn_diff.py builds its elpis tree with the series stopped before 3030.
#
# Why the pre-3030 core is not dominated (input for the kernel fix, done by ext 3030; counts from the
# routes below and the
# bend/err_attn_diff.py scan over L = 1 .. 262144):
#   1. Back-rotation chain. elpis rotates the fp16 quotient with a 32-term fp32 FFMA chain,
#      y = fmaf(oh[g0 + i], h32[i][jn], y) (E:exllamav3_ext/attn_verify.cu:637): 31 r32 steps on
#      position 0. stock rotates with tl.dot over k = 32 (S:modules/attention_fn/triton_paged.py:
#      718, called at :1064): two HMMA k16 steps, 2 t32. Alone this makes every L fail (L = 2:
#      elpis r32 / t32 = 39 / 37 vs stock 8 / 39).
#   2. Denominator tile sum. elpis sums a 64-key tile's p as p0 + p1 and two lane xors
#      (E:attn_verify.cu:461-463) then the 8 warp partials in sequence (E:attn_verify.cu:473-475):
#      up to 10 adds per p. stock's tl.sum(p) (S:triton_paged.py:962) is a 5-level tree over 32 keys
#      (in-thread add, 2 lane and 2 warp butterflies). Visible e.g. at L = 32, 64 with cause 1 fixed.
#   3. Combine fan-in. elpis merges min(20, ceil(L / 64)) slots with one FFMA each
#      (E:attn_verify.cu:628-629; 20 = 82 SMs // 4 kv heads, E:modules/attention_fn/bc_attn.py:440),
#      stock ceil(L / split_len) splits (S:triton_paged.py:1057-1058) with split_len = 128 for
#      L <= 4096 (S:exllamav3_ext/libtorch/attention.cpp:391-393, block-table width
#      S:generator/generator.py:965-966): more r32 steps for elpis at 500 <= L <= 4096.
#   4. P.V chain length. elpis CTA x accumulates the tiles x, x + 20, ... (E:exllamav3_ext/
#      attn_verify.cuh:45-62) through 4 HMMA k16 steps per 64-key tile (E:attn_verify.cu:491-513),
#      stock split s its own split_len keys through 2 per 32-key tile (S:triton_paged.py:973) over
#      41 splits (splits_cap, S:modules/attention_fn/bc_attn.py:287-288): about twice the t32 steps
#      on the q / k / v routes at long L (856 vs 438 at L = 262144).
#
# Sources (file:line). Stock: /tmp/kernel-work/PrecisionLaw/stock/exllamav3 (clean 355c6ee),
# "S:<file>:<line>". Elpis: that tree with patches/exl3/series then patches/exl3-ext/series applied,
# stopped before 3030, "E:<file>:<line>". bend/err_attn_diff.py checks every quoted fragment against both trees, the
# compiled-code facts (H_ptx, H_sass) and the geometry constants below.
#
# Served kernels.
#   elpis (m1map-map.json kernel_map 'T|attn|attn(...)', side verify): attn_pre_kernel (ext 3007,
#     E:exllamav3_ext/attn_small.cu:27-300), attn_verify_split_k3v3_tree (ext 3006 + 3012; m = 1
#     rounds run attn_verify_split_k3v3, the same split_body without tree passes,
#     E:exllamav3_ext/attn_verify.cu:539-559), attn_verify_combine_gate (ext 3007,
#     E:exllamav3_ext/attn_verify.cu:588-665). The 3005 Triton row split is not on the served route
#     (the CUDA verify attention replaces it whenever its guard holds, E:modules/attention_fn/
#     bc_attn.py:433-440); the served split is 3006's: S = max(1, SMs // kv heads) = 82 // 4 = 20
#     CTAs, CTA x takes the absolute 64-token tiles x, x + 20, ... (E:exllamav3_ext/attn_verify.cuh:
#     45-62).
#   stock M = 1 (m1map-stock.json side m1_stock; BC attention, enabled by default,
#     S:modules/attention_fn/bc_attn.py:42): rope_kernel (q/k norm + RoPE, S:exllamav3_ext/rope.cu:
#     16-260), quant_cache_paged_kernel, Triton _paged_attn_decode_split_kernel (QCK = QCV = 3,
#     S:modules/attention_fn/triton_paged.py:851-995) and _paged_attn_decode_combine_kernel
#     (S:triton_paged.py:998-1066), mul_sigmoid_kernel_h (S:exllamav3_ext/activation.cu:301-315).
#     BLOCK_N = max(16, 8192 // 256) = 32 (S:bc_attn.py:278), splits_cap = min(2 * 82 // 4, 128) = 41
#     (S:bc_attn.py:287-288), num_splits / split_len from the block-table width
#     (S:exllamav3_ext/libtorch/attention.cpp:388-394,760), the width being
#     16 * ceil(ceil(L / 256) / 16) pages (S:generator/generator.py:952,965-966, no draft tokens).
#
# Hypotheses (named; used by the models, none assumed by a law):
#   H_model   Higham's standard model per rounding step: no overflow, underflow or subnormal results
#             (both builds flush subnormals: --use_fast_math S:setup.py:23 = E:ext.py:92, Triton
#             enable_reflect_ftz); multiplication by a power of two is exact.
#   H_mma     One mma.sync m16n8k16 .f32 (HMMA.16816.F32) is one t32 step for the value it
#             accumulates; fp16 x fp16 products inside it are exact.
#   H_zero    A step whose other operands are structurally zero is exact and not counted, on both
#             sides alike: an MMA k-step or add whose other contributions are all masked / absent
#             keys (p = 0, zero-filled K / V), a running accumulator before its first live tile
#             (acc = l = 0, alpha = 0 exactly), a combine slot holding no live key (skipped by elpis,
#             weight 0 and partial 0 in stock), fmaf(a, h, 0) with fp16 a and h (exact product).
#   H_ptx     The stock Triton kernels are those compiled by Triton 3.6.0 (enable_fp_fusion) into the
#             image's cache: _paged_attn_decode_split_kernel XFUF7JHJ... (head_dim 256, BLOCK_N 32)
#             and _paged_attn_decode_combine_kernel IPYAKBVP... under
#             /tmp/elpis-recovery-ops-id8q0yvb/exl3-native-cache-1/triton (sha256 in the diff
#             script): tl.dot = an HMMA chain in k order (q rotation 2, Q.K^T 16, P.V 2 per tile
#             accumulating into acc * alpha, output rotation 2); scores * 0.0625 an exact FMUL;
#             tl.exp(x) = FADD (the subtraction) + FMUL by fp32(log2 e) + MUFU.EX2; tl.sum over a
#             32-key tile = 1 in-thread FADD + 2 lane butterflies + 2 warp butterflies; l * alpha +
#             sum one FFMA; acc += o * w and l_sum += l * w one FFMA each; acc / l_sum = div.full.f32
#             = exact power-of-two scalings + MUFU.RCP + FMUL.
#   H_sass    The elpis kernels compile (nvcc 12.9, sm_86, -O3 --use_fast_math, E:ext.py:91-92) as the
#             diff script's compile of E:exllamav3_ext/attn_verify.cu shows: QK^T a 16-HMMA chain,
#             x = FMUL by scale_log2, p = MUFU.EX2 of one FADD, l = FFMA, acc *= alpha FMUL, P.V an
#             HMMA chain over the tile's 4 k16 groups, combine fmaf -> FFMA, acc / lsum = MUFU.RCP +
#             FMUL, the output rotation a 32-FFMA chain starting from RZ. In the pre kernel the diff
#             script's probe compile of the kernel's own lines gives: sum = v1 * v1 + v2 * v2 -> FMUL(v2 * v2) then
#             FFMA(v1, v1, .); r1 = v1 * cos - v2 * sin -> FMUL(v2 * sin) then FFMA(v1, cos, -.);
#             r2 = v2 * cos + v1 * sin -> FMUL(v1 * sin) then FFMA(v2, cos, .); sum / (float) dim +
#             eps -> MUFU.RCP + FFMA (bend/err_elem.bend H_sass). attn_pre_kernel's floating-point
#             lines are textually rope_kernel's (diff script) and both kernels are built with the
#             same flags, so the pre stage compiles alike on both sides.
#   H_common  Rounding steps outside the vocabulary's classes are common to both sides and left out
#             of both paths (the parent's rule): __sinf / __cosf in RoPE (S:rope.cu:76-77 =
#             E:attn_small.cu:93-94); the CQ3 quantization of K / V (quant_block_x4, called as is by
#             attn_pre_kernel, E:attn_small.cu:290-293; the cache bits are identical, so the cache
#             words and fp16 scales are the attention's input leaves); constant roundings: fp32(log2 e)
#             (stock's 0f3FB8AA3B; elpis's scale_log2 = fp32(2^-4 log2 e) = 2^-4 fp32(log2 e),
#             E:bc_attn.py:481) and the fp16 H32 entries +-fp16(1/sqrt 32) (the same _get_h32 tensor,
#             S:triton_paged.py:705-711).
#   H_route   Leaves are routes (a leaf entering an output along two routes is two terms; the
#             production of the other factor of a product is that factor's leaves' route, as in
#             bend/err_elem.bend H_leaf). Quotient convention (the parent's): the path of a route
#             into acc / l is its numerator route + the denominator's worst path + the division
#             step; the denominator's worst path is the componentwise maximum over the
#             denominator's routes (through p into l, and through the max m into the combine weight
#             w and l).
#   H_dispatch Stock's served dispatch is the default one listed above (EXL3_BC_ATTN unset, Triton
#             cache as in H_ptx, 82 SMs, one sequence, no speculative draft so num_draft_tokens = 0).
import Base
import ./err_bound.bend as Eb

# ==== path segments ====

def r32(n: Nat) -> Eb.Path:
  Eb.Path{n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

def t32(n: Nat) -> Eb.Path:
  Eb.Path{0n, n, 0n, 0n, 0n, 0n, 0n, 0n}

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

# =====================================================================================================
# Pre stage: elpis attn_pre_kernel vs stock rope_kernel, one q or k head (q_norm / k_norm present,
# rotate_dims 1). Output element o of the head; its leaves (routes): the head's input elements through
# o's own value (self), through o's RoPE partner (partner, rotated dims only), and through the sum of
# squares (sq: the element at warp w, low / high half of its half2), and the norm weight.
# =====================================================================================================

# Norm weight dtype (the kernel template norm_bf16; both sides take the same branch).
type Nw is Data:
  NwF16{}
  NwBf16{}

# Whether o lies in the rotated part (first partial_head_dim dims) of the head.
type Rot is Data:
  RotNo{}
  RotYes{}

type Src is Data:
  SIn{}                      # the element itself (direct)
  SW{}                       # its norm weight
  SSq{w: Nat, hi: Bool}      # an element of the head through the sum of squares: warp w, half2 half

type Via is Data:
  VSelf{}
  VPartner{}

type PreLeaf is Data:
  PreLeaf{via: Via, src: Src}

# ---- stock rope_kernel ----

# float sum = v1 * v1 + v2 * v2;  (S:exllamav3_ext/rope.cu:199; H_sass: FMUL v2 * v2, FFMA v1)
def s_sumsq(hi: Bool) -> Nat:
  match hi:
    case True{}:
      2n
    case False{}:
      1n

# sum = warp_reduce_sum_f(sum)  (S:rope.cu:200): 5 xor-shuffle adds; then
# sum = sums[warps * t_head]; for (i = 1; i < warps; ++i) sum += sums[...]  (S:rope.cu:204-205):
# warps = 128 / 32 = 4 (blockDim.x = 32 * ceil(256 / 64)); warp 0's partial takes 3 adds, warp w >= 1
# takes 4 - w.
def s_partials(w: Nat) -> Nat:
  match w:
    case 0n:
      3n
    case 1n+p:
      Nat.sub(3n, p)

# float rmf = rsqrtf(sum / (float) head_dim + norm_eps)  (S:rope.cu:208): MUFU.RCP + FFMA + MUFU.RSQ.
def s_rmf() -> Eb.Path:
  cat(rcp(1n), cat(r32(1n), rsq(1n)))

# v1 *= rmf (S:rope.cu:209-210), then the weight: fp16 weights: v = __floats2half2_rn(v1, v2);
# v = __hmul2(w, v) (S:rope.cu:231-232); bf16 weights: v1 *= w.x; v = __floats2half2_rn
# (S:rope.cu:222-224). Steps of the normalized value from v * rmf on.
def s_norm_out(nw: Nw) -> Eb.Path:
  match nw:
    case NwF16{}:
      cat(r32(1n), r16(2n))
    case NwBf16{}:
      cat(r32(2n), r16(1n))

# The weight's route: fp16: w = __hadd2(w, bias) (S:rope.cu:230), __hmul2 (S:rope.cu:232);
# bf16: w.x += bias (S:rope.cu:220-221, FADD), v1 *= w.x, __floats2half2_rn.
def s_weight(nw: Nw) -> Eb.Path:
  match nw:
    case NwF16{}:
      r16(2n)
    case NwBf16{}:
      cat(r32(2n), r16(1n))

def s_src(nw: Nw, s: Src) -> Eb.Path:
  match s:
    case SIn{}:
      s_norm_out(nw)
    case SW{}:
      s_weight(nw)
    case SSq{+w, hi}:
      cat(r32(Nat.add(s_sumsq(hi), Nat.add(5n, s_partials(w)))), cat(s_rmf(), s_norm_out(nw)))

# RoPE (S:rope.cu:163-169, NEOX): r1 = v1 * cos - v2 * sin; r2 = v2 * cos + v1 * sin;
# sh_head[.] = __float2half_rn(r): the self term 1 rounding (the FFMA), the partner term 2 (FMUL +
# FFMA), then the fp16 store. cos / sin = __cosf / __sinf(fr * pf) * attn_factor (S:rope.cu:76-77):
# coefficients, not leaves (the sin.approx step is H_common).
def s_rope(r: Rot, v: Via) -> Eb.Path:
  match r:
    case RotNo{}:
      Eb.zero()
    case RotYes{}:
      match v:
        case VSelf{}:
          cat(r32(1n), r16(1n))
        case VPartner{}:
          cat(r32(2n), r16(1n))

def stock_pre(nw: Nw, r: Rot, l: PreLeaf) -> Eb.Path:
  match l:
    case PreLeaf{v, s}:
      cat(s_src(nw, s), s_rope(r, v))

# ---- elpis attn_pre_kernel (ext 3007) ----

# float sum = v1 * v1 + v2 * v2;  (E:exllamav3_ext/attn_small.cu:208)
def e_sumsq(hi: Bool) -> Nat:
  match hi:
    case True{}:
      2n
    case False{}:
      1n

# warp_reduce_sum_f (E:attn_small.cu:209), partial sums in warp order (E:attn_small.cu:213-214),
# blockDim.x = 32 * ceil(head_dim / 64) as rope_kernel's (E:attn_small.cu:15-16, attn_pre_gr).
def e_partials(w: Nat) -> Nat:
  match w:
    case 0n:
      3n
    case 1n+p:
      Nat.sub(3n, p)

# float rmf = rsqrtf(sum / (float) head_dim + norm_eps);  (E:attn_small.cu:216)
def e_rmf() -> Eb.Path:
  cat(rcp(1n), cat(r32(1n), rsq(1n)))

# v1 *= rmf (E:attn_small.cu:217-218); fp16: __floats2half2_rn, __hmul2 (E:attn_small.cu:237-238);
# bf16: v1 *= w.x, __floats2half2_rn (E:attn_small.cu:228-230).
def e_norm_out(nw: Nw) -> Eb.Path:
  match nw:
    case NwF16{}:
      cat(r32(1n), r16(2n))
    case NwBf16{}:
      cat(r32(2n), r16(1n))

# fp16: __hadd2(w, bias) (E:attn_small.cu:236), __hmul2; bf16: w.x += bias (E:attn_small.cu:226-227).
def e_weight(nw: Nw) -> Eb.Path:
  match nw:
    case NwF16{}:
      r16(2n)
    case NwBf16{}:
      cat(r32(2n), r16(1n))

def e_src(nw: Nw, s: Src) -> Eb.Path:
  match s:
    case SIn{}:
      e_norm_out(nw)
    case SW{}:
      e_weight(nw)
    case SSq{+w, hi}:
      cat(r32(Nat.add(e_sumsq(hi), Nat.add(5n, e_partials(w)))), cat(e_rmf(), e_norm_out(nw)))

# apply_rope (E:attn_small.cu:173-180): the same NEOX lines; cos / sin (E:attn_small.cu:93-94).
def e_rope(r: Rot, v: Via) -> Eb.Path:
  match r:
    case RotNo{}:
      Eb.zero()
    case RotYes{}:
      match v:
        case VSelf{}:
          cat(r32(1n), r16(1n))
        case VPartner{}:
          cat(r32(2n), r16(1n))

def elpis_pre(nw: Nw, r: Rot, l: PreLeaf) -> Eb.Path:
  match l:
    case PreLeaf{v, s}:
      cat(e_src(nw, s), e_rope(r, v))

# =====================================================================================================
# Attention core: one output element out[row, q head, d] (fp16, after the output gate) of a row at
# absolute position L - 1 (L visible keys). Input leaves: the fp16 q head (pre-stage output), the CQ3
# cache words / scales of K and V (H_common), the fp16 gate.
# =====================================================================================================

# Geometry of a route's key j at live length L (computed by the diff script from the kernels'
# index arithmetic, H_zero applied):
#   own    t32 steps of the key's own P.V tile: its own k16 group (1 when another live key shares the
#          group or the accumulator already holds a live tile, else 0) + the later live k16 groups
#          of the tile;
#   later  live tiles after the key's tile in its chain (elpis: CTA x's tiles x, x + 20, ...;
#          stock: the 32-key tiles of the key's split);
#   laterk live k16 groups summed over those later tiles;
#   after  live combine slots after the key's slot;
#   dr32, dt32, dex2  the denominator's worst path beyond the q rotation (H_route).
type Geo is Data:
  Geo{own: Nat, later: Nat, laterk: Nat, after: Nat, dr32: Nat, dt32: Nat, dex2: Nat}

# ---- segments shared in form (citations per side) ----

# q rotation: two k16 HMMA steps over the 32-dim group then fp16 (E:attn_verify.cu:299-304 mma16816 x 2,
# pack_h2; S:triton_paged.py:715-719 _rot_h32 tl.dot, .to(fp16); H_ptx / H_sass). kh = the q element's
# k16 half within its group.
def qrot(kh: Nat) -> Eb.Path:
  cat(t32(Nat.sub(2n, kh)), r16(1n))

# K / V dequantization: fp32 centered * scale (exact operands) then fp16
# (E:attn_verify.cu:82 __floats2half2_rn(__fmul_rn(...)), :94,510 deq_one + pack_h2;
#  S:triton_paged.py:805,848 ((raw - mh) * (scx * inv_m)).to(fp16)).
def deq() -> Eb.Path:
  cat(r32(1n), r16(1n))

# Q.K^T: the 16-HMMA chain over the 256 dims in k16 order (E:attn_verify.cu:401-414; S:triton_paged.py:943).
def qk(ks: Nat) -> Eb.Path:
  t32(Nat.sub(16n, ks))

# Score to p: elpis x = sc * scale_log2 (E:attn_verify.cu:433, FMUL) then ex2(x - m_use)
# (E:attn_verify.cu:458-459, FADD + MUFU.EX2); stock scores * 0.0625 (exact, S:triton_paged.py:943),
# tl.exp(scores - m_exp) (S:triton_paged.py:959: FADD, FMUL by fp32(log2 e), MUFU.EX2).
def e_xs() -> Eb.Path:
  cat(r32(2n), ex2(1n))

def s_xs() -> Eb.Path:
  cat(r32(2n), ex2(1n))

# P to fp16 for P.V (E:attn_verify.cu:460 pack_h2(p0, p1); S:triton_paged.py:973 p.to(v_tile.dtype)).
def pconv() -> Eb.Path:
  r16(1n)

# The running accumulator from the key's tile on: own + later k16 HMMA steps, one acc * alpha FMUL per
# later tile (E:attn_verify.cu:483-486,513; S:triton_paged.py:973 acc * alpha + tl.dot, H_ptx).
def chain(g: Geo) -> Eb.Path:
  match g:
    case Geo{+own, +later, +laterk, after, dr32, dt32, dex2}:
      cat(t32(Nat.add(own, laterk)), r32(later))

# Combine of the slot's partial: one FFMA for it and one per later live slot
# (E:attn_verify.cu:628 acc = fmaf(v, w, acc); S:triton_paged.py:1057 acc += o_s * w).
def comb(g: Geo) -> Eb.Path:
  match g:
    case Geo{own, later, laterk, +after, dr32, dt32, dex2}:
      r32(1n+after)

# The combine weight w of a slot, a route of the score leaves through the max m:
# elpis ex2(m_s - m_use) (E:attn_verify.cu:619, FADD + MUFU.EX2);
# stock tl.exp(m_s - m_safe) (S:triton_paged.py:1054, FADD + FMUL + MUFU.EX2).
def e_w() -> Eb.Path:
  cat(r32(1n), ex2(1n))

def s_w() -> Eb.Path:
  cat(r32(2n), ex2(1n))

# The denominator's worst path (H_route): its q rotation + the geometry's part.
def den(g: Geo) -> Eb.Path:
  match g:
    case Geo{own, later, laterk, after, +dr32, +dt32, +dex2}:
      cat(qrot(0n), Eb.Path{dr32, dt32, 0n, 0n, 0n, dex2, 0n, 0n})

# acc / l: elpis MUFU.RCP + FMUL (E:attn_verify.cu:631); stock div.full.f32 = scalings by powers of two
# + MUFU.RCP + FMUL (S:triton_paged.py:1062, H_ptx).
def div() -> Eb.Path:
  cat(rcp(1n), r32(1n))

# After the quotient. elpis: oh[d] = __float2half_rn(q) (E:attn_verify.cu:631); the H32 back-rotation
# y = fmaf(oh[g0 + i], h32[i][jn], y), i = 0..31 (E:attn_verify.cu:637): the value at position i
# passes 31 FFMA roundings if i = 0 (the first product, from RZ, is exact: H_zero) and 32 - i if
# i >= 1; out = __float2half_rn(y) (E:attn_verify.cu:638); the gate __hmul2(x2, sigmoid(y2))
# (E:attn_verify.cu:650).
def e_rot(i: Nat) -> Nat:
  match i:
    case 0n:
      31n
    case 1n+p:
      Nat.sub(31n, p)

def e_post(i: Nat) -> Eb.Path:
  cat(r16(1n), cat(r32(e_rot(i)), r16(2n)))

# stock: _rot_h32(out_tile) (S:triton_paged.py:1064, 715-719): x.to(fp16), tl.dot over k = 32 (two
# HMMA steps; position i < 16 passes both, i >= 16 the second), y.to(fp16); then mul_sigmoid_kernel_h
# x2 = __hmul2(x2, _sigmoid(y2)) (S:exllamav3_ext/activation_kernels.cuh:313).
def s_rot(lo: Bool) -> Nat:
  match lo:
    case True{}:
      2n
    case False{}:
      1n

# lo = the position lies in the first k16 half (i < 16).
def s_postb(lo: Bool) -> Eb.Path:
  cat(r16(1n), cat(t32(s_rot(lo)), r16(2n)))

def s_post(+i: Nat) -> Eb.Path:
  s_postb(Nat.is_lt(i, 16n))

# The gate's own route: _sigmoid (S:activation_kernels.cuh:132-139 = E:attn_verify.cu:579-586:
# h2exp r32 + ex2 + r16, __hadd2 r16, h2rcp rcp + r16, bend/err_elem.bend H_sass) then the __hmul2.
def gate() -> Eb.Path:
  cat(r32(1n), cat(ex2(1n), cat(r16(4n), rcp(1n))))

# Routes of out[row, head, d]:
#   AQ{kh, ks, i}  a q element (k16 half kh of its rotation) -> q-hat (Q.K^T k-step ks) -> p_j -> P.V ->
#                  combine -> quotient -> rotation position i -> gate
#   AK{ks, i}      a K cache value (dequant, k-step ks) -> p_j -> ...
#   AV{i}          a V cache value (dequant) -> P.V -> ...
#   AW{kh, ks, i}  a q element -> score -> slot max m -> combine weight w -> combine -> ...
#   AG{}           the gate element -> sigmoid -> product
# Routes through the in-split rescale alpha exist only with two or more live tiles in one chain
# (alpha of a chain's first tile is exactly 0, H_zero); none at the geometry of the laws.
type ALeaf is Data:
  AQ{kh: Nat, ks: Nat, i: Nat}
  AK{ks: Nat, i: Nat}
  AV{i: Nat}
  AW{kh: Nat, ks: Nat, i: Nat}
  AG{}

def quot(g: Geo, num: Eb.Path) -> Eb.Path:
  cat(num, cat(den(g), div()))

def elpis_leaf(+g: Geo, l: ALeaf) -> Eb.Path:
  match l:
    case AQ{kh, ks, i}:
      cat(quot(g, cat(qrot(kh), cat(qk(ks), cat(e_xs(), cat(pconv(), cat(chain(g), comb(g))))))), e_post(i))
    case AK{ks, i}:
      cat(quot(g, cat(deq(), cat(qk(ks), cat(e_xs(), cat(pconv(), cat(chain(g), comb(g))))))), e_post(i))
    case AV{i}:
      cat(quot(g, cat(deq(), cat(chain(g), comb(g)))), e_post(i))
    case AW{kh, ks, i}:
      cat(quot(g, cat(qrot(kh), cat(qk(ks), cat(e_w(), comb(g))))), e_post(i))
    case AG{}:
      gate()

# Stock routes, the rotation position entering as its k16 half lo = (i < 16).
def s_aq(+g: Geo, kh: Nat, ks: Nat, lo: Bool) -> Eb.Path:
  cat(quot(g, cat(qrot(kh), cat(qk(ks), cat(s_xs(), cat(pconv(), cat(chain(g), comb(g))))))), s_postb(lo))

def s_ak(+g: Geo, ks: Nat, lo: Bool) -> Eb.Path:
  cat(quot(g, cat(deq(), cat(qk(ks), cat(s_xs(), cat(pconv(), cat(chain(g), comb(g))))))), s_postb(lo))

def s_av(+g: Geo, lo: Bool) -> Eb.Path:
  cat(quot(g, cat(deq(), cat(chain(g), comb(g)))), s_postb(lo))

def s_aw(+g: Geo, kh: Nat, ks: Nat, lo: Bool) -> Eb.Path:
  cat(quot(g, cat(qrot(kh), cat(qk(ks), cat(s_w(), comb(g))))), s_postb(lo))

def stock_leaf(+g: Geo, l: ALeaf) -> Eb.Path:
  match l:
    case AQ{kh, ks, +i}:
      s_aq(g, kh, ks, Nat.is_lt(i, 16n))
    case AK{ks, +i}:
      s_ak(g, ks, Nat.is_lt(i, 16n))
    case AV{+i}:
      s_av(g, Nat.is_lt(i, 16n))
    case AW{kh, ks, +i}:
      s_aw(g, kh, ks, Nat.is_lt(i, 16n))
    case AG{}:
      gate()

# ---- geometry at L = 2 (a row at absolute position 1: a one-token prompt, then a verify / decode
# row; every key j in {0, 1} has this geometry on each side, checked by the diff script) ----
# elpis: one live tile (tile 0 of CTA 0), keys 0 and 1 share k16 group 0 (own = 1), no later tile,
# one live slot (after = 0). Denominator: through p: qk 16 t32, x / sub 2 r32 + ex2, the tile sum's
# p0 + p1 FADD (E:attn_verify.cu:461; the shuffles and the warp sum add structural zeros), the l FFMA
# of the first tile is exact (l = 0), the lsum FFMA 1 (E:attn_verify.cu:629): 3 + ... = dr32 4,
# dt32 16, dex2 1; through w: 16 t32, 1 r32 + ex2, lsum FFMA 1: below that maximum.
def geo_e2() -> Geo:
  Geo{1n, 0n, 0n, 0n, 4n, 16n, 1n}

# stock: one live split (split_len 128 >= 2), one 32-key tile, keys share k16 group 0 (own 1).
# Denominator through p: qk 16, sub + log2e mul 2 r32 + ex2, the in-thread FADD of tl.sum (the
# butterflies add structural zeros), l FFMA exact, l_sum FFMA 1: dr32 4, dt32 16, dex2 1; through w:
# 16 t32, 2 r32 + ex2, FFMA 1: below.
def geo_s2() -> Geo:
  Geo{1n, 0n, 0n, 0n, 4n, 16n, 1n}

# The elpis route compared: a q element of the first k16 half, Q.K^T k-step 0, rotation position 0.
def elpis_worst2() -> Eb.Path:
  elpis_leaf(geo_e2(), AQ{0n, 0n, 0n})

# Diagnostic: the same elpis route with stock's output stage (fp16, two-HMMA rotation, fp16, gate).
def elpis_worst2_srot() -> Eb.Path:
  cat(quot(geo_e2(), cat(qrot(0n), cat(qk(0n), cat(e_xs(), cat(pconv(), cat(chain(geo_e2()), comb(geo_e2()))))))), s_post(0n))
