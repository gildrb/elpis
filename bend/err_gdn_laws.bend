# Error-bound laws of the decode Gated DeltaNet (48 linear-attention layers): elpis verify
# (gdn_conv_rule_norm_kernel, ext 5101 / 5106 / 5108 / 5109) against stock ExLlamaV3 355c6ee M=1 decode
# (gdn_ba_gemv + fused_op_3 + conv1d_update + recurrent_gated_delta_rule_128<false, 4> + gated_rms_norm),
# over the model bend/err_gdn.bend and the vocabulary bend/err_bound.bend. Proofs: err_gdn_proof.bend;
# gate: err_gdn_gate.bend; source link: err_gdn_diff.py.
#
# Result. Both kernels compute the same exact recurrence with the same operations: every edge of the
# per-token DAG except the b/a GEMV performs the same rounding steps in the same order (Paths equal,
# err_gdn_diff.py checks the arithmetic text equal or cites both sides); the b/a GEMV sums the same
# products x[e] * w[e] once each (ba_into / ba_onto: a bijection of the terms preserving the element
# read), in a different order: elpis's k split takes at most 30 fp32 steps per term (+ bias), stock's
# 160-fmaf lane chain up to 165 (+ bias). Every elpis leaf-to-output path is dominated at x = 128 by the
# stock path of a real witness leaf (route_dom). No law is false.
#
# Named hypotheses (assumptions of the model, not proven here):
#   H_first_order  Composition across time steps and through the nonlinear stages (rsqrt, exp,
#                  sigmoid, softplus, the state recurrence): first-order forward error propagation is
#                  monotone in the local error bounds when both kernels compute the same exact
#                  recurrence (standard forward error analysis; Higham, Accuracy and Stability of
#                  Numerical Algorithms, 2nd ed., 2002, ch. 3, sections 3.1 - 3.4): a leaf's error
#                  reaches an output (y of any later token, or the state) along routes of the shared
#                  DAG, multiplied by the same exact partial derivatives on both sides, so per-route
#                  domination of the local bounds gives domination of the first-order output bound.
#                  Routes span tokens through Carry (state) and ConvX (conv window / conv_state).
#   H_dispatch     Served dispatch. Stock M=1: modules/gated_delta_net.py:1034-1045 takes the
#                  BC_GatedDeltaNetSplit path (split exl3 qkv / z / o, fp16 b / a, bf16 conv,
#                  gated_delta_net.py:657-669), run_bszN_gr (libtorch/gated_delta_net.cpp:278-319)
#                  with bsz 1, seqlen 1, history false: conv1d_update_kernel<true, false>,
#                  cuda_recurrent_gated_delta_rule_kernel_128<false, 4> (gdn.cu:928, 983),
#                  gated_rms_norm_kernel<32> (norm.cu:641-643; z fp32, y fp16). Elpis verify (rows
#                  m = 1..8, m1map kernel_map 'verify'): gdn_conv_rule_norm_kernel with KS = 2
#                  (EXL3_GDN_BA_KSPLIT unset: gdn.cu:3553 default GR_KS_DEFAULT = 2, the m1map run's env
#                  is empty; S <= 8 and k / 2 = 2560 <= 512 * 5 keep it, gdn.cu:3714); the m1map verify
#                  trace (m1map-map-route-verify.json.gz) launches gdn_conv_rule_norm_kernel<bf16, bf16,
#                  4, 2, false, true> (KS 2, TREE). The verify group's other launch,
#                  at::native::vectorized_elementwise_kernel (48, once per layer, just before the layer's
#                  first fused kernel), is FillFunctor<int>: the one-time conv_sync zero fill
#                  (libtorch/gated_delta_net.cpp:365), no activation arithmetic. The trace's 48 fp32 ->
#                  bf16 bfloat16_copy_kernel_cuda launches all precede the first verify kernel (prefill's
#                  torch path); none is in decode. TREE and chain verify run the same per-row arithmetic
#                  (the tree changes which rows a row's state and conv window come from: spec_inv_tree's
#                  concern).
#   H_shape        Qwen3.8-27B GDN shapes: hidden k = 5120 (k / 2 = 2560 half2), head dims 128, conv
#                  K = 4, SUBK = 4, gated-norm gate_act 0 (SiLU). The bias flags (b/a bias hb, norm
#                  constant_bias cb) and the softplus branch (lin) are free.
#   H_compile      Both extensions are built by the same nvcc with the same flags (setup.py
#                  identical, -O3 --use_fast_math): identical expression text compiles to the same
#                  rounding sequence (same FMA contraction; contraction can only drop a step). Paths
#                  count source-level operations (err_gdn.bend header).
# Common factors: bf16 RN (qkv cast, conv output, beta), bf16 RZ (rule output) and log1pf (softplus)
# are outside the vocabulary; they are left out of both Paths and com_same / route_dom prove each edge
# and route performs the same count of each on both sides.
import Base
import ./err_bound.bend as Eb
import ./err_gdn.bend as G

# ==== (1) same exact computation: the b/a GEMV terms ====
# Every elpis b/a term (warp w, lane l, iteration i, component c) is a stock term (lane l, iteration
# 16 i + w, component c) reading the same half element 2 j + c of x and of the weight row, and psi
# inverts the map.
law ba_into:
  for +ab: Nat
  for +w: Nat
  for +l: Nat
  for +i: Nat
  for +c: Nat
  for +hb: Bool
  for v: {G.valid_e(G.BaE{ab, w, l, i, c, hb}) == True{} : Bool}
  {G.valid_s(G.phi(G.BaE{ab, w, l, i, c, hb})) == True{} : Bool} &
  {G.s_elem(G.phi(G.BaE{ab, w, l, i, c, hb})) == G.e_elem(G.BaE{ab, w, l, i, c, hb}) : Nat} &
  {G.psi(G.phi(G.BaE{ab, w, l, i, c, hb})) == G.BaE{ab, w, l, i, c, hb} : G.Seg}

# ... and every stock b/a term is the image of an elpis term: phi is a bijection of the two kernels'
# term sets preserving the element read, so both GEMVs add the same products, each once.
law ba_onto:
  for +ab: Nat
  for +l: Nat
  for +m: Nat
  for +c: Nat
  for +hb: Bool
  for v: {G.valid_s(G.BaS{ab, l, m, c, hb}) == True{} : Bool}
  {G.valid_e(G.psi(G.BaS{ab, l, m, c, hb})) == True{} : Bool} &
  {G.phi(G.psi(G.BaS{ab, l, m, c, hb})) == G.BaS{ab, l, m, c, hb} : G.Seg}

# ==== (2) per-edge bounds ====
# The b/a GEMV: every elpis term takes at most 30 fp32 steps (+ the bias add) ...
law ba_bound:
  for +w: Nat
  for +i: Nat
  for +c: Nat
  for +hb: Bool
  {Nat.is_le(G.e_ba(w, i, c, hb), Nat.add(30n, G.bit(hb))) == True{} : Bool}

# ... and stock's witness term (lane 0, iteration 0, .x) is its worst one: 165 steps (+ bias).
law ba_stock_worst:
  for +m: Nat
  for +c: Nat
  for +hb: Bool
  {Nat.is_le(G.s_ba(m, c, hb), G.s_ba(0n, 0n, hb)) == True{} : Bool} &
  {G.s_ba(0n, 0n, hb) == Nat.add(165n, G.bit(hb)) : Nat}

# Witnesses keep the edge's operand and result node (a b/a term stays a b/a term of the same b or a).
law edge_nodes:
  for +s: G.Seg
  {G.src(G.wit(s)) == G.src(s) : Nat} &
  {G.dst(G.wit(s)) == G.dst(s) : Nat}

# Common factors: every edge and its witness perform the same bf16 RN, bf16 RZ and log1pf steps.
law com_same:
  for +s: G.Seg
  {G.s_com(G.wit(s)) == G.e_com(s) : G.Com}

# Every elpis edge's witness is a real stock edge, whose Path is the elpis Path plus `gap` extra fp32
# steps (gap 0: the same rounding steps), so it dominates the elpis Path at x = 128.
law edge_dom:
  for +s: G.Seg
  for v: {G.valid_e(s) == True{} : Bool}
  {G.valid_s(G.wit(s)) == True{} : Bool} &
  {G.s_path(G.wit(s)) == Eb.add(G.r32p(G.gap(s)), G.e_path(s)) : Eb.Path} &
  {Eb.dom(128n, G.e_path(s), G.s_path(G.wit(s))) == True{} : Bool}

# ==== (3) leaf-to-output paths ====
# For every route of elpis edges (in particular every connected route from an input leaf to an
# output y element or a state element, across any number of tokens): the witness route consists of
# real stock edges, is connected exactly when the route is, performs the same common-factor steps,
# and its Path dominates the route's Path at x = 128.
law route_dom:
  for +r: List<&2, G.Seg>
  for v: {G.all_e(r) == True{} : Bool}
  {G.all_s(G.wits(r)) == True{} : Bool} &
  {G.chain(G.wits(r)) == G.chain(r) : Bool} &
  {G.com_s(G.wits(r)) == G.com_e(r) : G.Com} &
  {Eb.dom(128n, G.sum_e(r), G.sum_s(G.wits(r))) == True{} : Bool}
