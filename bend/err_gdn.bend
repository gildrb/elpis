# Rounding-error paths of the decode Gated DeltaNet (the 48 linear-attention layers), elpis verify
# against stock ExLlamaV3 355c6ee M=1 decode, over the error-bound vocabulary (bend/err_bound.bend).
# Laws: bend/err_gdn_laws.bend; source link: bend/err_gdn_diff.py (checks every `S` / `E` citation
# line below against the stock tree and the patched tree, and the identical-arithmetic fragments).
# Proof model only (not shipped).
#
# Kernels (served dispatch, hypothesis H_dispatch in err_gdn_laws.bend):
#   stock  BC_GatedDeltaNetSplit::run_bszN_gr (bsz 1, seqlen 1, history false): gdn_ba_gemv_kernel,
#          gated_delta_net_fused_op_3_kernel, conv1d_update_kernel<true, false>,
#          cuda_recurrent_gated_delta_rule_kernel_128<false, 4>, gated_rms_norm_kernel<32, half, w, float>
#   elpis  gdn_conv_rule_norm_kernel<a_log_T, norm_w_T, 4, KS = 2, false, TREE> (ext 5101, 5106, 5108,
#          5109): b/a k-split GEMV, beta/g, conv + SiLU, l2 norm, gdn_rule_tokens(_tree), gated norm
# Citations: `S <file>:<line> | <text>` = stock tree (355c6ee, PrecisionLaw/stock/exllamav3),
# `E <file>:<line> | <text>` = patched tree (355c6ee + patches/exl3/series + patches/exl3-ext/series);
# <file> relative to the exllamav3 package directory.
#
# The exact computation of one token of one v head is a DAG over the nodes below; an edge (Seg) is one
# operand-to-result step with the rounding steps it takes on each side. A leaf's path to an output is
# a route (a connected list of edges); its Path is the concatenation (Eb.add) of the edge Paths.
# Counting rule (both sides): every source-level fp32 operation (add, mul, fmaf/fma, sub) counts one
# r32 step, except the additions of an exact 0.0f (`x = 0.0f; x += p` and stock's zero lanes, exact in
# IEEE); a product of two operands is one leaf for both factors. __expf(x) = FMUL by log2(e) (r32) +
# ex2.approx (ex2); `/` (div.approx under --use_fast_math) and __fdividef count rcp; rsqrtf counts
# rsq; __float2half_rn counts r16. Conversions bf16 / fp16 -> fp32 and fp32 state stores / loads are
# exact. Steps outside the vocabulary (bf16 RN, bf16 RZ, log1pf) are NOT in the Paths: they are
# common factors, counted per edge in Com and proven equal on both sides (err_gdn_laws.bend com_same).
import Base
import ./err_bound.bend as Eb

# ==== Path helpers ====
def pth(+r32: Nat, +ex2: Nat, +rcp: Nat, +rsq: Nat, +r16: Nat) -> Eb.Path:
  Eb.Path{r32, 0n, r16, 0n, 0n, ex2, rcp, rsq}

def r32p(+n: Nat) -> Eb.Path:
  pth(n, 0n, 0n, 0n, 0n)

def bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# Common factors outside the vocabulary: bf16 round-to-nearest, bf16 round-toward-zero, log1pf.
type Com is Data:
  Com{rn: Nat, rz: Nat, lg: Nat}

def com0() -> Com:
  Com{0n, 0n, 0n}

def com_add(a: Com, b: Com) -> Com:
  match a:
    case Com{a1, a2, a3}:
      match b:
        case Com{b1, b2, b3}:
          Com{Nat.add(a1, b1), Nat.add(a2, b2), Nat.add(a3, b3)}

# ==== Nodes of the exact DAG (one token, one v head h, its k head, one v column) ====
def n_qkv() -> Nat:
  0n   # qkv projection output, fp32 (input leaf)
def n_xb() -> Nat:
  1n   # conv input, bf16 (this token's or an earlier token's: conv window / conv_state)
def n_cw() -> Nat:
  2n   # conv weight (leaf)
def n_cb() -> Nat:
  3n   # conv bias (leaf)
def n_acc() -> Nat:
  4n   # conv pre-activation, fp32
def n_act() -> Nat:
  5n   # SiLU output, fp32
def n_co() -> Nat:
  6n   # conv output, bf16: raw q / k / v
def n_qn() -> Nat:
  7n   # l2-normalized q element
def n_kn() -> Nat:
  8n   # l2-normalized k element
def n_st() -> Nat:
  9n   # recurrent state element S[i][c] before the token (fp32)
def n_d1s() -> Nat:
  10n  # dot1 partial of one 32-row k slice
def n_d1() -> Nat:
  11n  # dot1 = S^T k (column c)
def n_vv() -> Nat:
  12n  # v - dot1 * gexp
def n_ns() -> Nat:
  13n  # updated state element
def n_vos() -> Nat:
  14n  # v_out partial of one k slice
def n_vo() -> Nat:
  15n  # v_out = S'^T q (column c)
def n_out() -> Nat:
  16n  # rule output, bf16
def n_y() -> Nat:
  17n  # gated-norm output, fp16 (the op's output)
def n_bal() -> Nat:
  18n  # b/a GEMV term x[j] * w[j] (leaf; one per half element)
def n_bb() -> Nat:
  19n  # b/a bias (leaf)
def n_b() -> Nat:
  20n  # b, fp32
def n_a() -> Nat:
  21n  # a, fp32
def n_beta() -> Nat:
  22n  # beta, bf16
def n_dtb() -> Nat:
  23n  # dt_bias (leaf)
def n_alog() -> Nat:
  24n  # a_log (leaf)
def n_g() -> Nat:
  25n  # g, fp32
def n_gexp() -> Nat:
  26n  # exp(g)
def n_z() -> Nat:
  27n  # norm gate z, fp32 (leaf)
def n_nw() -> Nat:
  28n  # norm weight (leaf)

# C ternary on a 0 / 1 selector (ab, qk)
def sel(s: Nat, +x: Nat, +y: Nat) -> Nat:
  match s:
    case 0n:
      x
    case 1n+p:
      y

# ==== Edges ====
# Index fields: kk < 4 conv tap; qk 0 = q, 1 = k; p < 32 position in a 32-term k-slice chain; w < 4 k
# slice (SUBK); q < 4 element of a lane's float4 in the norm; ab 0 = b, 1 = a. BaE is the elpis b/a
# term (warp w < 16, lane l < 32, iteration i < 5, half2 component c < 2), BaS the stock one (lane l <
# 32, loop iteration m < 80, component c); hb: the b/a bias is present.
type Seg is Data:
  Cast{}
  ConvX{kk: Nat}
  ConvW{kk: Nat}
  ConvB{}
  SiluD{}
  SiluG{}
  ConvO{}
  L2D{qk: Nat}
  L2S{qk: Nat}
  D1K{p: Nat}
  D1S{p: Nat}
  D1Sl{w: Nat}
  VD{}
  VI{}
  VG{}
  GX{}
  UpS{}
  UpG{}
  UpK{}
  UpV{}
  UpB{}
  Carry{}
  VoN{p: Nat}
  VoQ{p: Nat}
  VoSl{w: Nat}
  Sc{}
  NoD{}
  NoW{cb: Bool}
  NoS{q: Nat}
  NoGD{}
  NoGS{}
  BaE{ab: Nat, w: Nat, l: Nat, i: Nat, c: Nat, hb: Bool}
  BaS{ab: Nat, l: Nat, m: Nat, c: Nat, hb: Bool}
  BaB{ab: Nat}
  Beta{}
  GA{lin: Bool}
  GD{lin: Bool}
  GL{}

def src(s: Seg) -> Nat:
  match s:
    case Cast{}:
      n_qkv()
    case ConvX{kk}:
      n_xb()
    case ConvW{kk}:
      n_cw()
    case ConvB{}:
      n_cb()
    case SiluD{}:
      n_acc()
    case SiluG{}:
      n_acc()
    case ConvO{}:
      n_act()
    case L2D{qk}:
      n_co()
    case L2S{qk}:
      n_co()
    case D1K{p}:
      n_kn()
    case D1S{p}:
      n_st()
    case D1Sl{w}:
      n_d1s()
    case VD{}:
      n_d1()
    case VI{}:
      n_co()
    case VG{}:
      n_gexp()
    case GX{}:
      n_g()
    case UpS{}:
      n_st()
    case UpG{}:
      n_gexp()
    case UpK{}:
      n_kn()
    case UpV{}:
      n_vv()
    case UpB{}:
      n_beta()
    case Carry{}:
      n_ns()
    case VoN{p}:
      n_ns()
    case VoQ{p}:
      n_qn()
    case VoSl{w}:
      n_vos()
    case Sc{}:
      n_vo()
    case NoD{}:
      n_out()
    case NoW{cb}:
      n_nw()
    case NoS{q}:
      n_out()
    case NoGD{}:
      n_z()
    case NoGS{}:
      n_z()
    case BaE{ab, w, l, i, c, hb}:
      n_bal()
    case BaS{ab, l, m, c, hb}:
      n_bal()
    case BaB{ab}:
      n_bb()
    case Beta{}:
      n_b()
    case GA{lin}:
      n_a()
    case GD{lin}:
      n_dtb()
    case GL{}:
      n_alog()

def dst(s: Seg) -> Nat:
  match s:
    case Cast{}:
      n_xb()
    case ConvX{kk}:
      n_acc()
    case ConvW{kk}:
      n_acc()
    case ConvB{}:
      n_acc()
    case SiluD{}:
      n_act()
    case SiluG{}:
      n_act()
    case ConvO{}:
      n_co()
    case L2D{qk}:
      sel(qk, n_qn(), n_kn())
    case L2S{qk}:
      sel(qk, n_qn(), n_kn())
    case D1K{p}:
      n_d1s()
    case D1S{p}:
      n_d1s()
    case D1Sl{w}:
      n_d1()
    case VD{}:
      n_vv()
    case VI{}:
      n_vv()
    case VG{}:
      n_vv()
    case GX{}:
      n_gexp()
    case UpS{}:
      n_ns()
    case UpG{}:
      n_ns()
    case UpK{}:
      n_ns()
    case UpV{}:
      n_ns()
    case UpB{}:
      n_ns()
    case Carry{}:
      n_st()
    case VoN{p}:
      n_vos()
    case VoQ{p}:
      n_vos()
    case VoSl{w}:
      n_vo()
    case Sc{}:
      n_out()
    case NoD{}:
      n_y()
    case NoW{cb}:
      n_y()
    case NoS{q}:
      n_y()
    case NoGD{}:
      n_y()
    case NoGS{}:
      n_y()
    case BaE{ab, w, l, i, c, hb}:
      sel(ab, n_b(), n_a())
    case BaS{ab, l, m, c, hb}:
      sel(ab, n_b(), n_a())
    case BaB{ab}:
      sel(ab, n_b(), n_a())
    case Beta{}:
      n_beta()
    case GA{lin}:
      n_g()
    case GD{lin}:
      n_g()
    case GL{}:
      n_g()

# ==== Edge validity (index ranges of the served shapes, hypothesis H_shape) ====
def lt(+a: Nat, +b: Nat) -> Bool:
  Nat.is_lt(a, b)

# Edges both kernels have, with the same index ranges
def valid_common(s: Seg) -> Bool:
  match s:
    case ConvX{kk}:
      lt(kk, 4n)
    case ConvW{kk}:
      lt(kk, 4n)
    case L2D{qk}:
      lt(qk, 2n)
    case L2S{qk}:
      lt(qk, 2n)
    case D1K{p}:
      lt(p, 32n)
    case D1S{p}:
      lt(p, 32n)
    case D1Sl{w}:
      lt(w, 4n)
    case VoN{p}:
      lt(p, 32n)
    case VoQ{p}:
      lt(p, 32n)
    case VoSl{w}:
      lt(w, 4n)
    case NoS{q}:
      lt(q, 4n)
    case BaB{ab}:
      lt(ab, 2n)
    case BaE{ab, w, l, i, c, hb}:
      False{}
    case BaS{ab, l, m, c, hb}:
      False{}
    case other:
      True{}

# Elpis b/a term: E gdn.cu:3319 | const int j = warp_id * 32 + lane_id + i * THREADS;
# j < 16 * 32 + 4 * 512 = 2560 = k2 (k = 5120), so E gdn.cu:3320 | if (j < k2) always holds
def valid_e(s: Seg) -> Bool:
  match s:
    case BaE{+ab, +w, +l, +i, +c, hb}:
      Bool.and(lt(ab, 2n), Bool.and(lt(w, 16n), Bool.and(lt(l, 32n), Bool.and(lt(i, 5n), lt(c, 2n)))))
    case other:
      valid_common(other)

# Stock b/a term: S gdn.cu:1653 | for (int j = lane; j < k / 2; j += 32)
# iteration m reads half2 j = lane + 32 m; k / 2 = 2560 = 80 * 32, so m < 80 for every lane
def valid_s(s: Seg) -> Bool:
  match s:
    case BaS{+ab, +l, +m, +c, hb}:
      Bool.and(lt(ab, 2n), Bool.and(lt(l, 32n), Bool.and(lt(m, 80n), lt(c, 2n))))
    case other:
      valid_common(other)

# ==== Shared counting helpers (each side's paths below are written from its own source) ====
# A `sum = 0.0f; for j < 32: sum = sum + a[j] * b[j]` chain: term 0 takes its product and the 31
# later adds (0.0f + t0 is exact), term p >= 1 its product and the adds p..31 (33 - p).
def chain32(p: Nat) -> Nat:
  match p:
    case 0n:
      32n
    case 1n+q:
      Nat.sub(32n, q)

# `x = 0.0f; for w < 4: x += part[w]`: part 0 takes the adds of parts 1..3, part w >= 1 the adds w..3.
def slices4(w: Nat) -> Nat:
  match w:
    case 0n:
      3n
    case 1n+q:
      Nat.sub(3n, q)

# ==== elpis paths (patched tree) ====
# E gdn.cu:3195 | if (s < S) xb[s] = trunc_bf16(x_d[(size_t) s * F]);
# E gdn.cu:3175 | w[kk] = __bfloat162float(conv_weight[(size_t) c * K + kk]);
# E gdn.cu:3177 | float bias_d = conv_bias ? __bfloat162float(conv_bias[c]) : 0.0f;
# E gdn.cu:3216 | else win[K - 1] = __bfloat162float(xb[s]);
# E gdn.cu:3213 | win[kk] = __bfloat162float(seq[K + (i >= 0 ? (int) pth[i] : i)]);
# E gdn.cu:3218 | float acc = bias_d;
# E gdn.cu:3221 | acc = fmaf(w[kk], win[kk], acc);
# E gdn.cu:3223 | acc *= _sigmoid_fast_exp(acc);
# E gdn.cu:42 | return 1.0f / (1.0f + __expf(-x));
# E gdn.cu:3225 | bfloat16 o = __float2bfloat16_rn(acc);
# E gdn.cu:3227 | dst[s * HD] = __bfloat162float(o);
# l2 norm, one warp per vector (lane holds elements l, 32 + l, 64 + l, 96 + l):
# E gdn.cu:2755 | float p0 = x0 * x0;
# E gdn.cu:2762 | p0 += __shfl_xor_sync(0xffffffff, p0, offset);
# E gdn.cu:2767 | float rs = rsqrtf(((p0 + p2) + (p1 + p3)) + 1e-6f);
# E gdn.cu:2768 | vec[lane] = x0 * rs;
# rule (thread = k slice w, v column c; state in registers, fp32):
# E gdn.cu:2779 | sum = sum + k_rd[j] * state[j];
# E gdn.cu:2799 | for (int i = 0; i < SUBK; ++i) dot1 += dot1_col[i * 128];
# E gdn.cu:2800 | float v = v_in - dot1 * g_h;
# E gdn.cu:2805 | float ns = state[j] * g_h + k_rd[j] * v * beta_h;
# E gdn.cu:2807 | v_out = v_out + q_rd[j] * ns;
# E gdn.cu:2857 | for (int i = 0; i < SUBK; ++i) v_out += m.dot2[(s * SUBK + i) * 128 + c];
# E gdn.cu:2858 | m.out[s * 128 + c] = __float2bfloat16_rz(v_out * scale);
# E gdn.cu:2719 | gexp = __expf(g);
# E gdn.cu:2720 | beta_f = __bfloat162float(beta);
# gated norm, warp = token, lane = elements 4l..4l+3:
# E gdn.cu:2954 | sum = gdn_norm_sum_sq4(sum, x4);
# E gdn.cu:1104 | lsum = fma(f4.x, f4.x, lsum);
# E gdn.cu:2956 | for (int offset = warpSize / 2; offset > 0; offset /= 2) sum += __shfl_xor_sync(0xffffffff, sum, offset);
# E gdn.cu:2958 | float rmf = rsqrtf(sum / (float) dim + epsilon);
# E gdn.cu:2965 | w4.x += constant_bias;
# E gdn.cu:1113 | x4.x = x4.x * w4.x * rmf;
# E gdn.cu:2974 | x4.x *= _gate_fn(g4.x);
# E gdn.cu:1121 | float e     = __expf(-x);
# E gdn.cu:1122 | float recip = __fdividef(1.0f, 1.0f + e);
# E gdn.cu:1123 | return x * recip;
# E gdn.cu:1096 | __halves2half2(__float2half_rn(f4.x), __float2half_rn(f4.y)),
# b/a k-split GEMV (KS = 2): lane chain of 10 fmaf (i = 0..4, .x then .y), warp tree, warp sum, bias:
# E gdn.cu:3330 | pb[s] = fmaf(xf.x, wbf.x, pb[s]);
# E gdn.cu:3331 | pb[s] = fmaf(xf.y, wbf.y, pb[s]);
# E gdn.cu:3350 | for (int offset = 16; offset > 0; offset >>= 1)
# E gdn.cu:3352 | pb[s] += __shfl_down_sync(0xffffffff, pb[s], offset);
# E gdn.cu:3403 | bv = 0.0f;
# E gdn.cu:3406 | for (int w = 0; w < GR_WARPS; ++w)
# E gdn.cu:3408 | bv += ks_part[w * 2 * GR_KS_ROWS + t];
# E gdn.cu:3413 | bv += __half2float(ba_bias[h]);
# beta / g:
# E gdn.cu:3420 | float beta = _sigmoid_fast_exp(bv) * beta_scale;
# E gdn.cu:3422 | float gv = -softplus(av + dtb) * __expf(as_float(a_log[h]));
# E gdn.cu:67 | if (x > 20.0f) return x;
# E gdn.cu:68 | return log1pf(__expf(x));
# E gdn.cu:3425 | bfloat16 beta_b = trunc_bf16(beta);

# Elpis b/a term (w, i, c): fmaf chain from index 2 i + c of 10 (10 - (2 i + c)), the 5 tree adds,
# the warp sum (warp 0: adds of warps 1..15 = 15, 0.0f + part0 exact; warp w >= 1: adds w..15 =
# 16 - w), the bias add.
def e_wsum(w: Nat) -> Nat:
  match w:
    case 0n:
      15n
    case 1n+q:
      Nat.sub(15n, q)

def e_ba(+w: Nat, +i: Nat, +c: Nat, hb: Bool) -> Nat:
  Nat.add(Nat.sub(10n, Nat.add(Nat.mul(i, 2n), c)), Nat.add(5n, Nat.add(e_wsum(w), bit(hb))))

# -softplus(a + dtb) * __expf(a_log): the add, softplus (identity above 20, else __expf then
# log1pf: the log1pf is a common factor), the final multiply
def e_soft(lin: Bool) -> Eb.Path:
  match lin:
    case True{}:
      r32p(2n)
    case False{}:
      pth(3n, 1n, 0n, 0n, 0n)

def e_path(s: Seg) -> Eb.Path:
  match s:
    case Cast{}:
      Eb.zero()
    case ConvX{kk}:
      r32p(Nat.sub(4n, kk))
    case ConvW{kk}:
      r32p(Nat.sub(4n, kk))
    case ConvB{}:
      r32p(4n)
    case SiluD{}:
      r32p(1n)
    case SiluG{}:
      pth(3n, 1n, 1n, 0n, 0n)
    case ConvO{}:
      Eb.zero()
    case L2D{qk}:
      r32p(1n)
    case L2S{qk}:
      # square, 5 xor adds, (p0 + p2) + (p1 + p3), + 1e-6f, rsqrtf, x * rs
      pth(Nat.add(1n, Nat.add(5n, Nat.add(2n, Nat.add(1n, 1n)))), 0n, 0n, 1n, 0n)
    case D1K{p}:
      r32p(chain32(p))
    case D1S{p}:
      r32p(chain32(p))
    case D1Sl{w}:
      r32p(slices4(w))
    case VD{}:
      r32p(2n)
    case VI{}:
      r32p(1n)
    case VG{}:
      r32p(2n)
    case GX{}:
      pth(1n, 1n, 0n, 0n, 0n)
    case UpS{}:
      r32p(2n)
    case UpG{}:
      r32p(2n)
    case UpK{}:
      r32p(3n)
    case UpV{}:
      r32p(3n)
    case UpB{}:
      r32p(2n)
    case Carry{}:
      Eb.zero()
    case VoN{p}:
      r32p(chain32(p))
    case VoQ{p}:
      r32p(chain32(p))
    case VoSl{w}:
      r32p(slices4(w))
    case Sc{}:
      r32p(1n)
    case NoD{}:
      pth(3n, 0n, 0n, 0n, 1n)
    case NoW{cb}:
      pth(Nat.add(bit(cb), 3n), 0n, 0n, 0n, 1n)
    case NoS{q}:
      # sum_sq4 fma chain from element q of 4, 5 xor adds, + epsilon, * rmf, * gate; / dim, rsqrtf
      pth(Nat.add(Nat.sub(4n, q), Nat.add(5n, Nat.add(1n, Nat.add(1n, 1n)))), 0n, 1n, 1n, 1n)
    case NoGD{}:
      pth(2n, 0n, 0n, 0n, 1n)
    case NoGS{}:
      pth(4n, 1n, 1n, 0n, 1n)
    case BaE{ab, +w, l, +i, +c, hb}:
      r32p(e_ba(w, i, c, hb))
    case BaS{ab, l, m, c, hb}:
      Eb.zero()
    case BaB{ab}:
      r32p(1n)
    case Beta{}:
      pth(3n, 1n, 1n, 0n, 0n)
    case GA{lin}:
      e_soft(lin)
    case GD{lin}:
      e_soft(lin)
    case GL{}:
      pth(2n, 1n, 0n, 0n, 0n)

def e_com(s: Seg) -> Com:
  match s:
    case Cast{}:
      Com{1n, 0n, 0n}
    case ConvO{}:
      Com{1n, 0n, 0n}
    case Sc{}:
      Com{0n, 1n, 0n}
    case Beta{}:
      Com{1n, 0n, 0n}
    case GA{lin}:
      Com{0n, 0n, Nat.sub(1n, bit(lin))}
    case GD{lin}:
      Com{0n, 0n, Nat.sub(1n, bit(lin))}
    case other:
      com0()

# ==== stock paths (355c6ee) ====
# S gdn.cu:1543 | out_mixed_qkv[((size_t) b * F + f) * S + s] = trunc_bf16(in_qkv[idx]);
# S gdn.cu:1347 | if (k < K) w[k] = __bfloat162float(weight[(size_t) d * K + k]);
# S gdn.cu:1349 | float bias_d = bias ? __bfloat162float(bias[d]) : 0.0f;
# S gdn.cu:1363 | win[K - 1] = __bfloat162float(x_d[s]);
# S gdn.cu:1365 | float acc = bias_d;
# S gdn.cu:1368 | if (k < K) acc = fmaf(w[k], win[k], acc);
# S gdn.cu:1371 | acc *= _sigmoid_fast_exp(acc);
# S gdn.cu:24 | return 1.0f / (1.0f + __expf(-x));
# S gdn.cu:1373 | out[((size_t) b * seqlen + s) * dim + d] = __float2bfloat16_rn(acc);
# l2 norm, 4 warps per vector (thread t holds element t), second xor tree over [w0, w1, w2, w3, 0, ...]:
# its offsets 16, 8, 4 add exact zeros to lanes 0..3, offsets 2 and 1 give (w0 + w2) + (w1 + w3):
# S gdn.cu:747 | float sumq = q * q;
# S gdn.cu:752 | sumq += __shfl_xor_sync(0xffffffff, sumq, offset);
# S gdn.cu:762 | sumq = lane < HEAD_DIM / 32 ? sh_red[0][lane] : 0.0f;
# S gdn.cu:767 | sumq += __shfl_xor_sync(0xffffffff, sumq, offset);
# S gdn.cu:771 | q = q * rsqrtf(sumq + 1e-6f);
# rule (V_SPLIT 4: thread (t < 32, bt = k slice); state in global memory, fp32):
# S gdn.cu:797 | sum = sum + *sh_k_rd * *rs_rd;
# S gdn.cu:806 | float g_h = CHANNELWISE ? 1.0f : __expf(g[head]);
# S gdn.cu:807 | float beta_h = __bfloat162float(beta[head]);
# S gdn.cu:811 | for (int s = 0; s < SUBK; ++s) dot1 += sh_dot1[s][t];
# S gdn.cu:812 | float v = __bfloat162float(gl_v[t]) - dot1 * g_h;
# S gdn.cu:827 | state = state * (CHANNELWISE ? *sh_g_rd : g_h) + *sh_k_rd * v * beta_h;
# S gdn.cu:828 | *rs_w = state;
# S gdn.cu:829 | v_out = v_out + *sh_q_rd * state;
# S gdn.cu:840 | for (int s = 0; s < SUBK; ++s) v_out += sh_dot2[s][t];
# S gdn.cu:841 | out[t] = __float2bfloat16_rz(v_out * scale);
# gated norm (dim 128 <= 256: 32 threads, thread = elements 4t..4t+3):
# S norm.cu:643 | dim3 blockDim(small ? 32 : NUM_THREADS, 1, 1);
# S norm.cu:547 | sum = sum_sq4(sum, x4);
# S norm.cu:103 | lsum = fma(f4.x, f4.x, lsum);
# S norm.cu:19 | for(int offset = warpSize / 2; offset > 0; offset /= 2) sum += __shfl_xor_sync(0xffffffff, sum, offset);
# S norm.cu:552 | float rmf = rsqrtf(sum / (float)dim + epsilon);
# S norm.cu:569 | w4.x += constant_bias;
# S norm.cu:586 | apply4(x4, w4, rmf);
# S norm.cu:112 | x4.x = x4.x * w4.x * rmf;
# S norm.cu:588 | x4.x *= _gate_fn(g4.x);
# S norm.cu:128 | float e     = __expf(-x);
# S norm.cu:129 | float recip = __fdividef(1.0f, 1.0f + e);
# S norm.cu:130 | return x * recip;
# S norm.cu:79 | __halves2half2(__float2half_rn(f4.x), __float2half_rn(f4.y)),
# b/a GEMV (one warp per output row): lane chain of 160 fmaf (m = 0..79, .x then .y), warp tree, bias:
# S gdn.cu:1657 | sum = fmaf(xf.x, wf.x, sum);
# S gdn.cu:1658 | sum = fmaf(xf.y, wf.y, sum);
# S gdn.cu:1661 | for (int offset = 16; offset > 0; offset >>= 1)
# S gdn.cu:1662 | sum += __shfl_down_sync(0xffffffff, sum, offset);
# S gdn.cu:1666 | if (bias) sum += __half2float(bias[row]);
# beta / g:
# S gdn.cu:1554 | float beta = _sigmoid_fast_exp(bv) * beta_scale;
# S gdn.cu:1556 | float gv = -softplus(av + dt_bias) * __expf(as_float(in_a_log[h]));
# S gdn.cu:49 | if (x > 20.0f) return x;
# S gdn.cu:50 | return log1pf(__expf(x));
# S gdn.cu:1558 | out_beta[(size_t) row * H + h] = trunc_bf16(beta);

# Stock b/a term (m, c): fmaf chain from index 2 m + c of 160, the 5 tree adds, the bias add.
def s_ba(+m: Nat, +c: Nat, hb: Bool) -> Nat:
  Nat.add(Nat.sub(160n, Nat.add(Nat.mul(m, 2n), c)), Nat.add(5n, bit(hb)))

def s_soft(lin: Bool) -> Eb.Path:
  match lin:
    case True{}:
      r32p(2n)
    case False{}:
      pth(3n, 1n, 0n, 0n, 0n)

def s_path(s: Seg) -> Eb.Path:
  match s:
    case Cast{}:
      Eb.zero()
    case ConvX{kk}:
      r32p(Nat.sub(4n, kk))
    case ConvW{kk}:
      r32p(Nat.sub(4n, kk))
    case ConvB{}:
      r32p(4n)
    case SiluD{}:
      r32p(1n)
    case SiluG{}:
      pth(3n, 1n, 1n, 0n, 0n)
    case ConvO{}:
      Eb.zero()
    case L2D{qk}:
      r32p(1n)
    case L2S{qk}:
      # square, 5 xor adds, 2 rounding adds of the second tree, + 1e-6f, rsqrtf, q * rs
      pth(Nat.add(1n, Nat.add(5n, Nat.add(2n, Nat.add(1n, 1n)))), 0n, 0n, 1n, 0n)
    case D1K{p}:
      r32p(chain32(p))
    case D1S{p}:
      r32p(chain32(p))
    case D1Sl{w}:
      r32p(slices4(w))
    case VD{}:
      r32p(2n)
    case VI{}:
      r32p(1n)
    case VG{}:
      r32p(2n)
    case GX{}:
      pth(1n, 1n, 0n, 0n, 0n)
    case UpS{}:
      r32p(2n)
    case UpG{}:
      r32p(2n)
    case UpK{}:
      r32p(3n)
    case UpV{}:
      r32p(3n)
    case UpB{}:
      r32p(2n)
    case Carry{}:
      Eb.zero()
    case VoN{p}:
      r32p(chain32(p))
    case VoQ{p}:
      r32p(chain32(p))
    case VoSl{w}:
      r32p(slices4(w))
    case Sc{}:
      r32p(1n)
    case NoD{}:
      pth(3n, 0n, 0n, 0n, 1n)
    case NoW{cb}:
      pth(Nat.add(bit(cb), 3n), 0n, 0n, 0n, 1n)
    case NoS{q}:
      pth(Nat.add(Nat.sub(4n, q), Nat.add(5n, Nat.add(1n, Nat.add(1n, 1n)))), 0n, 1n, 1n, 1n)
    case NoGD{}:
      pth(2n, 0n, 0n, 0n, 1n)
    case NoGS{}:
      pth(4n, 1n, 1n, 0n, 1n)
    case BaE{ab, w, l, i, c, hb}:
      Eb.zero()
    case BaS{ab, l, +m, +c, hb}:
      r32p(s_ba(m, c, hb))
    case BaB{ab}:
      r32p(1n)
    case Beta{}:
      pth(3n, 1n, 1n, 0n, 0n)
    case GA{lin}:
      s_soft(lin)
    case GD{lin}:
      s_soft(lin)
    case GL{}:
      pth(2n, 1n, 0n, 0n, 0n)

def s_com(s: Seg) -> Com:
  match s:
    case Cast{}:
      Com{1n, 0n, 0n}
    case ConvO{}:
      Com{1n, 0n, 0n}
    case Sc{}:
      Com{0n, 1n, 0n}
    case Beta{}:
      Com{1n, 0n, 0n}
    case GA{lin}:
      Com{0n, 0n, Nat.sub(1n, bit(lin))}
    case GD{lin}:
      Com{0n, 0n, Nat.sub(1n, bit(lin))}
    case other:
      com0()

# ==== witnesses ====
# An elpis b/a term is matched with stock's worst b/a term of the same output (lane 0, iteration 0,
# .x: the head of the 160-fmaf chain); every other edge with itself.
def wit(s: Seg) -> Seg:
  match s:
    case BaE{ab, w, l, i, c, hb}:
      BaS{ab, 0n, 0n, 0n, hb}
    case other:
      other

# The exact-term correspondence: elpis term (w, l, i, c) reads the half element stock's lane l reads
# at iteration m = 16 i + w (component c); psi is its inverse.
def phi(s: Seg) -> Seg:
  match s:
    case BaE{ab, w, l, i, c, hb}:
      BaS{ab, l, Nat.add(Nat.mul(i, 16n), w), c, hb}
    case other:
      other

def psi(s: Seg) -> Seg:
  match s:
    case BaS{ab, l, +m, c, hb}:
      BaE{ab, Nat.mod(m, 16n), l, Nat.div(m, 16n), c, hb}
    case other:
      other

# Half element of x / w a b/a term multiplies: 2 j + c with j the half2 index of each loop.
def e_elem(s: Seg) -> Nat:
  match s:
    case BaE{ab, w, l, i, c, hb}:
      Nat.add(Nat.mul(Nat.add(Nat.add(Nat.mul(w, 32n), l), Nat.mul(i, 512n)), 2n), c)
    case other:
      0n

def s_elem(s: Seg) -> Nat:
  match s:
    case BaS{ab, l, m, c, hb}:
      Nat.add(Nat.mul(Nat.add(l, Nat.mul(m, 32n)), 2n), c)
    case other:
      0n

# The gap a witness adds on the r32 tier (0 for every identical edge).
def gap(s: Seg) -> Nat:
  match s:
    case BaE{ab, +w, l, +i, +c, +hb}:
      Nat.sub(s_ba(0n, 0n, hb), e_ba(w, i, c, hb))
    case other:
      0n

# ==== routes ====
def wits(r: List<&2, Seg>) -> List<&2, Seg>:
  match r:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      Con{wit(s), wits(t)}

def sum_e(r: List<&2, Seg>) -> Eb.Path:
  match r:
    case Nil{}:
      Eb.zero()
    case Con{s, t}:
      Eb.add(e_path(s), sum_e(t))

def sum_s(r: List<&2, Seg>) -> Eb.Path:
  match r:
    case Nil{}:
      Eb.zero()
    case Con{s, t}:
      Eb.add(s_path(s), sum_s(t))

def com_e(r: List<&2, Seg>) -> Com:
  match r:
    case Nil{}:
      com0()
    case Con{s, t}:
      com_add(e_com(s), com_e(t))

def com_s(r: List<&2, Seg>) -> Com:
  match r:
    case Nil{}:
      com0()
    case Con{s, t}:
      com_add(s_com(s), com_s(t))

def gaps(r: List<&2, Seg>) -> Nat:
  match r:
    case Nil{}:
      0n
    case Con{s, t}:
      Nat.add(gap(s), gaps(t))

def all_e(r: List<&2, Seg>) -> Bool:
  match r:
    case Nil{}:
      True{}
    case Con{s, t}:
      Bool.and(valid_e(s), all_e(t))

def all_s(r: List<&2, Seg>) -> Bool:
  match r:
    case Nil{}:
      True{}
    case Con{s, t}:
      Bool.and(valid_s(s), all_s(t))

# Consecutive edges connect: each edge's result is the next edge's operand.
def chain_go(r: List<&2, Seg>, +a: Seg) -> Bool:
  match r:
    case Nil{}:
      True{}
    case Con{+b, t}:
      Bool.and(Nat.is_eq(dst(a), src(b)), chain_go(t, b))

def chain(r: List<&2, Seg>) -> Bool:
  match r:
    case Nil{}:
      True{}
    case Con{a, t}:
      chain_go(t, a)
