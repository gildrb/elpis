# Error-bound laws of the prefill arithmetic elpis changed vs stock ExLlamaV3 355c6ee (model: err_prefill.bend,
# vocabulary: err_bound.bend, exchange rate 128). Proven in err_prefill_proof.bend; gate err_prefill_gate.bend.
# Named hypotheses (model facts, not proven here; see err_prefill.bend and the report):
#   H_std      Higham's standard model per step (no underflow / overflow; err_bound.bend header).
#   H_ratio    o = N / l: the bound of o is that of the composite path num(leaf) + den(worst den key) + fixed.
#   H_common_kv  Q, the staged fp16 K / V (same CQ3 cache, same unpatched dequant_cache_paged_window) and the
#              score segments are the same values on both sides; they enter both composites as the common c.
#   H_masked_exact  a tile with no visible key for the row leaves its m, l, acc bit-unchanged (ex2(0) = 1,
#              p = 0, x * 1, fma(l, 1, 0), MMA of zero products), in both kernels.
#   H_ptx      PTX / CPTX / TTG (err_prefill.bend header) is what the served Triton runs for the stock kernels.
#   H_same_text  identical Triton / CUDA source text (modulo addressing; err_prefill_diff.py) compiles to the
#              same per-element arithmetic.
import Base
import ./err_bound.bend as Eb
import ./err_prefill.bend as Ep
import ./hgemm_wide.bend as HW

# ==== attention ====

# 1. The score segment (Q K^T over the k16 step s of the product, the fp32 scale, the exp2 argument, exp2) is the
# same path in both kernels, in the interior (fused fma) and the masked (mul then sub) form.
law score_eq:
  for interior: Bool
  for +s: Nat
  {Ep.score_e(interior, s) == Ep.score_s(interior, s) : Eb.Path}

# 2. Witness: stock's tile-0, first-half leaf is stock's worst leaf of the row (every stock leaf of a row with
# A + T later tiles is dominated by it), so it is the real leaf the domination laws compare against.
law stock_worst:
  for +T: Nat
  for +A: Nat
  for +h: Bool
  {Eb.dom(128n, Ep.stock_leaf(T, A, h), Ep.stock_leaf(0n, Nat.add(A, T), False{})) == True{} : Bool}

# 3. TRUE vs unsplit stock for rows seeing n >= 3 key tiles: every elpis 3022 v4 leaf (tile T, A later tiles,
# either k16 half) is dominated by stock's worst leaf of the same row, for every common segment c.
law pv_unsplit_dom:
  for +T: Nat
  for +A: Nat
  for +h: Bool
  for +c: Eb.Path
  for big: {Nat.is_le(2n, Nat.add(T, A)) == True{} : Bool}
  {Eb.dom(128n, Eb.add(c, Ep.elpis_leaf(T, A, h)), Eb.add(c, Ep.stock_leaf(0n, Nat.add(T, A), False{}))) == True{} : Bool}

# ==== GDN prefill conv ====

# 4. Per output element and tap, ext 5111's fused conv performs the stock route's step sequence (the same bf16
# input rounding, bf16 product, fp32 adds, bias, SiLU, bf16 store), so the class paths are equal and the
# out-of-class (bf16, sigmoid) steps are common to both sides.
law conv_trace_eq:
  for +K: Nat
  for +j: Nat
  for +b: Bool
  {Ep.elpis_conv(K, j, b) == Ep.stock_conv(K, j, b) : List<&2, Ep.St>}

law conv_path_eq:
  for +K: Nat
  for +j: Nat
  for +b: Bool
  {Ep.st_path(Ep.elpis_conv(K, j, b)) == Ep.st_path(Ep.stock_conv(K, j, b)) : Eb.Path}

# 5. Route: a chunk of more than 256 rows runs the fused conv exactly where stock runs the output kernel (whose
# step sequence law 4 matches); a chunk of at most 256 rows runs the stock route itself (the bf16 copy plus the
# same unpatched kernel), whatever the other 5111 conditions are.
law conv_route_long:
  for +r: Nat
  {Ep.elpis_route(Nat.add(257n, r), True{}) == Ep.KFused{} : Ep.Kern} &
  {Ep.stock_route(Nat.add(257n, r)) == Ep.KOut{} : Ep.Kern}

law conv_route_short:
  for +r: Nat
  for fc: Bool
  for short: {Nat.is_le(r, 256n) == True{} : Bool}
  {Ep.elpis_route(r, fc) == Ep.stock_route(r) : Ep.Kern}

# ==== prefill GEMM ====

# 6. Every product term of the 3011 wide kernel has the path it has in the served f16acc kernel (hgemm_wide's
# k_order: the same 32-wide slices, the same MMA pair, the same fp32 fold order), for every K = 64 L.
law gemm_paths_eq:
  for +L: Nat
  {Ep.wide_paths(Nat.mul(L, 64n)) == Ep.served_paths(Nat.mul(L, 64n)) : List<&2, Eb.Path>}
