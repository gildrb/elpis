# Rounding-error paths of the PREFILL arithmetic elpis changed vs stock ExLlamaV3 355c6ee, in the vocabulary of
# bend/err_bound.bend (Path = per-class step counts from one input term to one output element). Contract laws (TRUE):
# err_prefill_laws.bend / err_prefill_proof.bend; finding (refutations of the attention law for ext 3022 v4):
# err_prefill_finding_laws.bend / err_prefill_finding_proof.bend; gate: err_prefill_gate.bend; source links:
# err_prefill_diff.py (every "X:n" below is checked there).
#
# SCOPE: the elpis attention arithmetic modeled here (and the FINDING below) is ext 3022 v4 as it was BEFORE ext 3031
# (patches/exl3-ext/3031-prefill-pattn-dominate.patch). 3031 replaces it: the tile sum is a balanced tree (depth 5
# with the quad reduction) and a row runs as chains of E = ceil((q64 + 1) / 256) tiles combined as stock's split
# combine; that arithmetic is modeled by err_pfix.bend, whose contract is now err_pfix_laws.bend. The finding is
# kept until the GPU gates of 3031 pass, and then retired.
#
# FINDING: ext 3022 v4 prefill attention is NOT dominated by stock (law "elpis path dom stock worst-leaf path" is
# FALSE), for two causes:
#   (a) denominator depth, rows seeing n <= 2 key tiles (absolute position < 64), vs unsplit stock: elpis sums a
#       thread's 8 p sequentially (sum = 0 + p0, then 7 f_add, P3022:231-242) and quad-reduces once at the end
#       (2 f_add, P3022:283-284): 9 r32; stock's l = l * alpha + tl.sum(p) (TP:1346) is a depth-5 tree (PTX:2297-2440)
#       folded by one fma (PTX:2457). elpis's P V saves 2 t32 per later tile (P3022:268-272 vs TP:1376), which
#       pays the 4 r32 back only from n = 3 tiles on.
#   (b) rescale count, vs the served split stock (num_splits = 2 whenever the job's block table spans >= 8192
#       keys, TP:1849-1871): elpis runs one online-softmax chain over the whole row, so its worst leaf passes
#       2 (n - 1) alpha = ex2 rescales (numerator and denominator, P3022:230); stock's two split chains are half as
#       long (TP:1475-1478) and the combine adds one exp2 weight per split (TP:1628, CPTX:186-188), so every stock
#       composite has at most 2 max(N0, N1) of them: ex2 is compared kind by kind, FALSE once both splits hold
#       >= 2 tiles of the row.
#
# Sources (read-only):
#   TP   = stock modules/attention_fn/triton_paged.py (355c6ee)
#   PTX  = PTX_DIR/stock_prefill_sm86.ptx   (stock _paged_attn_prefill_kernel,
#          served constexprs, sm_86, compiled by bend/gen/stock_prefill_ptx.py with the image's Triton; IS_SPLIT = False)
#   CPTX = PTX_DIR/stock_combine_sm86.ptx    (stock split combine kernel)
#   TTG  = PTX_DIR/stock_prefill_sm86.ttgir  (layouts of the same compile)
#   P3010, P3022, P5111 = patches/exl3-ext/3010-prefill-pattn.patch, 3022-prefill-pattn-fp32acc.patch,
#          5111-gdn-prefill-fuse-nom4096.patch (series order; 3020 changes only the warp mapping, see
#          pattn8_sched_laws.bend, and 3022 patches pattn_kernel.cuh and pattn8_kernel.cuh identically)
#   CONV = stock modules/gated_delta_net_fn/conv1d.py;  GDN = stock modules/gated_delta_net.py
#   HF   = stock exllamav3_ext/hgemm_f16acc.cu
#
# Path field order: Eb.Path{r32, t32, r16, t16, q8, ex2, rcp, rsq}.
import Base
import ./err_bound.bend as Eb
import ./hgemm_wide.bend as HW

# n copies of segment s concatenated in front of p (a path is a multiset of steps: order is irrelevant)
def rep_add(n: Nat, +s: Eb.Path, p: Eb.Path) -> Eb.Path:
  match n:
    case 0n:
      p
    case 1n+k:
      Eb.add(s, rep_add(k, s, p))

# ======================================================================================================
# 1. Prefill attention, one output element o[row, d] = (sum_j P_j V[j, d]) / l, l = sum_j p_j.
#
# Row model: the row sees n = T + 1 + A key tiles of 32 (tiles with no visible key leave m, l, acc bit-unchanged
# in both kernels, hypothesis H_masked_exact). A numerator leaf is the term P_j V[j, d] of a key in tile T with
# A later tiles; h = False / True: the key is in the first / second k16 half of its tile (two chained m16n8k16
# MMAs per 32-key tile in both kernels: P3010:398-399 / P3022:269-270, PTX:2800-2893). The composite path of a
# leaf = its numerator path + the worst denominator path of the row (tile-0 key: most later tiles) + the fixed
# steps (P to fp16, the division, the fp16 store), hypothesis H_ratio. The score segment (Q K^T, scale, exp2 of
# both the numerator key and the denominator key) and the K / V / Q production are equal on both sides
# (law score_eq; H_common_kv) and enter both composites as the common segment c of the laws.
# ======================================================================================================

def own_t32(h: Bool) -> Nat:
  match h:
    case False{}:
      2n
    case True{}:
      1n

# ---- elpis ext 3022 v4 (pattn_kernel.cuh / pattn8_kernel.cuh) ----

# Own tile: the key's products enter a zero-C MMA pair (P3022:268-270: 2 or 1 t32), then the tile joins O by one
# fma.rn (P3022:271-272, f_fma_pv): a rounding (r32) except in tile 0, where O = 0 and alpha = 0 (m = -inf,
# P3022:230) make fma(0, 0, tile) exact. fold = (T >= 1).
def e_own(fold: Bool, h: Bool) -> Eb.Path:
  match fold:
    case False{}:
      Eb.Path{0n, own_t32(h), 0n, 0n, 0n, 0n, 0n, 0n}
    case True{}:
      Eb.Path{1n, own_t32(h), 0n, 0n, 0n, 0n, 0n, 0n}

# Each later tile, numerator: O = fma.rn(O, alpha, tile) (P3022:271-272: r32) with alpha = ex2(f_sub(m, m_new))
# (P3022:230: r32 + ex2). No tensor-core step touches the running O.
def e_later() -> Eb.Path:
  Eb.Path{2n, 0n, 0n, 0n, 0n, 1n, 0n, 0n}

# Each later tile, denominator (both kernels): l = fma.rn(l, alpha, sum) (P3022:245; TP:1346 -> PTX:2457-2464:
# r32) with the same alpha (r32 + ex2).
def den_later() -> Eb.Path:
  Eb.Path{2n, 0n, 0n, 0n, 0n, 1n, 0n, 0n}

# Denominator, worst key of its tile: per-thread sequential sum of its 8 p (sum = 0 + p0 exact, then 7 f_add,
# P3022:238-242) and, once at the end, the quad reduction (2 f_add, P3022:283-284). The tile-0 fma into l = 0 is
# exact (P3022:245 with alpha = 0).
def e_den_in() -> Eb.Path:
  Eb.Path{9n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

# Fixed: P rounded to fp16 for the P V MMA (P3010:364-367 pack_h2), O / l by div.full.f32 (P3022:294, rcp
# class), the fp16 store (P3022:294 pack_h2).
def fixed() -> Eb.Path:
  Eb.Path{0n, 0n, 2n, 0n, 0n, 0n, 1n, 0n}

def e_last(fold: Bool, h: Bool) -> Eb.Path:
  Eb.add(e_own(fold, h), Eb.add(e_den_in(), fixed()))

# a later tile of the row: one numerator step for the leaf and one denominator step for the worst den key
def e_row_later() -> Eb.Path:
  Eb.add(e_later(), den_later())

# leaf after A later tiles, given its own-tile part
def e_inner(A: Nat, fold: Bool, h: Bool) -> Eb.Path:
  rep_add(A, e_row_later(), e_last(fold, h))

# The elpis composite path of the leaf (tile T, A later tiles, half h): the T tiles before the leaf's tile add
# one denominator step each (the worst den key is in tile 0).
def elpis_leaf(T: Nat, A: Nat, h: Bool) -> Eb.Path:
  match T:
    case 0n:
      e_inner(A, False{}, h)
    case 1n+t:
      Eb.add(den_later(), rep_add(t, den_later(), e_inner(A, True{}, h)))

# ---- stock _paged_attn_prefill_kernel, unsplit (TP:1247-1378, 1381-1577; PTX loop 1252-2906) ----

# Own tile: C = acc * alpha (PTX:2703-2766) rounds only the old accumulator; the key's products enter the MMA
# pair with that C (PTX:2800-2893: 2 or 1 t32). In tile 0, acc = 0 and alpha = 0 (TP:1343), C = 0 exactly.
def s_own(h: Bool) -> Eb.Path:
  Eb.Path{0n, own_t32(h), 0n, 0n, 0n, 0n, 0n, 0n}

# Each later tile, numerator: acc * alpha (mul.f32, PTX:2703-2766: r32), the MMA pair with C = the running acc
# (TP:1376 -> TTG:213 tt.dot with C = acc_127, PTX:2800-2893: 2 t32), alpha = exp2(m - m_new) (TP:1345,
# PTX:2275-2291: sub.f32 r32 + ex2).
def s_later() -> Eb.Path:
  Eb.Path{2n, 2n, 0n, 0n, 0n, 1n, 0n, 0n}

# Denominator in-tile: tl.sum of the 32 p of a row (TP:1346) is a balanced tree of depth 5: one add of a thread's
# 2 values (PTX:2297-2304), two shuffle levels (PTX:2307-2400), the cross-warp pass over 4 warps through shared
# memory with two more shuffle levels (PTX:2404-2440). Then fma.rn(l, alpha, sum) (PTX:2457-2464), exact in
# tile 0 (l = 0, alpha = 0).
def s_den_in() -> Eb.Path:
  Eb.Path{5n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

# Fixed: p.to(fp16) (TP:1376, PTX:2768-2775 cvt.rn.f16x2), acc / l (TP:1573, PTX:5192 div.full.f32), fp16 store
# (TP:1577, TTG:327 truncf).
def s_last(h: Bool) -> Eb.Path:
  Eb.add(s_own(h), Eb.add(s_den_in(), fixed()))

def s_row_later() -> Eb.Path:
  Eb.add(s_later(), den_later())

def stock_leaf(T: Nat, A: Nat, h: Bool) -> Eb.Path:
  rep_add(A, s_row_later(), rep_add(T, den_later(), s_last(h)))

# ---- score segment of a key (equal on both sides) ----
# interior = the tile lies below n_full of stock's 64-row block (TP:1533-1545; P3022:127-128, 178): exp2 takes
# fma(raw, c, -m) (PTX:2234-2256: 1 r32); otherwise s = raw * c then s - m (PTX:4107, 4382: 2 r32). The Q K^T
# product of dimension group s (k16 step s < 16) passes 16 - s fp32-accumulate MMA steps (PTX:1838-2039;
# P3010:283-306 g < 8, s < 2). exp2: ex2.approx.ftz.f32 (PTX:2258; P3010:178-182).
def score_s(interior: Bool, s: Nat) -> Eb.Path:
  match interior:
    case True{}:
      Eb.Path{1n, Nat.sub(16n, s), 0n, 0n, 0n, 1n, 0n, 0n}
    case False{}:
      Eb.Path{2n, Nat.sub(16n, s), 0n, 0n, 0n, 1n, 0n, 0n}

# elpis: q stays unscaled fp16 (P3022:154), raw fp32 sums (P3010:305-306), interior: f_fma(x, c, -m)
# (P3022:239), else f_mul (P3022:190) then f_sub (P3022:239).
def score_e(interior: Bool, s: Nat) -> Eb.Path:
  match interior:
    case True{}:
      Eb.add(Eb.Path{1n, 0n, 0n, 0n, 0n, 1n, 0n, 0n}, Eb.Path{0n, Nat.sub(16n, s), 0n, 0n, 0n, 0n, 0n, 0n})
    case False{}:
      Eb.add(Eb.Path{2n, 0n, 0n, 0n, 0n, 1n, 0n, 0n}, Eb.Path{0n, Nat.sub(16n, s), 0n, 0n, 0n, 0n, 0n, 0n})

# ---- stock split route (served: num_splits = 2 whenever the job's block table spans >= 8192 keys, TP:1849-1871)
# Split k of a row holds N_k visible tiles; partial acc / m / l stored fp32 (TP:1554-1564, exact). Combine
# (TP:1622-1635; CPTX): w = exp2(m_s - m_max) (CPTX:186-188: r32 + ex2), acc = fma.rn(o_s, w, acc) and
# l = fma.rn(l_s, w, l) (CPTX:522, 587-591: r32; split 0 meets acc = 0, still a rounding of o_0 w), splits in
# order 0, 1; acc / l (CPTX:943 div.full), fp16 store (CPTX:1400 cvt.rn.f16).
def comb(k: Nat) -> Eb.Path:
  match k:
    case 0n:
      Eb.Path{3n, 0n, 0n, 0n, 0n, 1n, 0n, 0n}
    case 1n+j:
      Eb.Path{2n, 0n, 0n, 0n, 0n, 1n, 0n, 0n}

# numerator leaf in split k, tile t of the split, a later tiles inside the split
def ss_num(k: Nat, a: Nat, h: Bool) -> Eb.Path:
  rep_add(a, s_later(), Eb.add(s_own(h), comb(k)))

# worst denominator key of split k' (its tile 0, nk' - 1 later tiles inside the split)
def ss_den(k: Nat, later: Nat) -> Eb.Path:
  rep_add(later, den_later(), Eb.add(s_den_in(), comb(k)))

def stock_split_leaf(k: Nat, a: Nat, h: Bool, kd: Nat, later_d: Nat) -> Eb.Path:
  Eb.add(ss_num(k, a, h), Eb.add(ss_den(kd, later_d), fixed()))

# Every composite of a row with N0, N1 visible tiles in splits 0, 1: numerator key in split k at a later tiles
# (a < N_k), half h, denominator worst key of split k'.
def leaves_k(+k: Nat, +a: Nat, +nd0: Nat, +nd1: Nat) -> List<&2, Eb.Path>:
  match a:
    case 0n:
      []
    case 1n+b:
      List.append(&2, Eb.Path, [stock_split_leaf(k, b, False{}, 0n, nd0), stock_split_leaf(k, b, True{}, 0n, nd0),
        stock_split_leaf(k, b, False{}, 1n, nd1), stock_split_leaf(k, b, True{}, 1n, nd1)],
        leaves_k(k, b, nd0, nd1))

def split_leaves(+N0: Nat, +N1: Nat) -> List<&2, Eb.Path>:
  List.append(&2, Eb.Path, leaves_k(0n, N0, Nat.sub(N0, 1n), Nat.sub(N1, 1n)),
    leaves_k(1n, N1, Nat.sub(N0, 1n), Nat.sub(N1, 1n)))

# all stock unsplit composites of a row with n tiles (tile T, A = n - 1 - T later), both halves
def unsplit_leaves_t(+T: Nat, +n: Nat) -> List<&2, Eb.Path>:
  match T:
    case 0n:
      []
    case 1n+t:
      List.append(&2, Eb.Path, [stock_leaf(t, Nat.sub(Nat.sub(n, 1n), t), False{}),
        stock_leaf(t, Nat.sub(Nat.sub(n, 1n), t), True{})], unsplit_leaves_t(t, n))

def unsplit_leaves(+n: Nat) -> List<&2, Eb.Path>:
  unsplit_leaves_t(n, n)

# True iff no path of xs dominates e (at exchange rate x)
def none_dom(+x: Nat, +e: Eb.Path, xs: List<&2, Eb.Path>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{s, rest}:
      Bool.and(Bool.not(Eb.dom(x, e, s)), none_dom(x, e, rest))

def add_all(+c: Eb.Path, xs: List<&2, Eb.Path>) -> List<&2, Eb.Path>:
  match xs:
    case Nil{}:
      []
    case Con{s, rest}:
      Eb.add(c, s) <> add_all(c, rest)

# ======================================================================================================
# 2. GDN prefill causal conv (one output element (s, d), tap j of K). Rounding-step trace, in-class and
# out-of-class (bf16) steps kept apart: an out-of-class step is never folded into a class.
# ======================================================================================================

type St is Data:
  Bf16In{}    # fp32 qkv -> bf16, round to nearest even
  MulB{}      # bf16 tap product vals * w (Triton bf16 multiply)
  AddX{}      # fp32 add into the zero accumulator: exact
  Add32{}     # fp32 add (r32)
  Sig{}       # tl.sigmoid
  Mul32{}     # fp32 multiply (r32)
  StB{}       # fp32 -> bf16 store

# the accumulator adds a tap-j product meets: j = 0 enters 0 exactly, then K - 1 - j... later taps add
def adds_after(n: Nat) -> List<&2, St>:
  match n:
    case 0n:
      []
    case 1n+k:
      Add32{} <> adds_after(k)

def bias_step(b: Bool) -> List<&2, St>:
  match b:
    case True{}:
      [Add32{}]
    case False{}:
      []

# Stock: qkv.transpose(1, 2).to(torch.bfloat16) (GDN:1106), _causal_conv1d_update_slotted_output_kernel
# (seq_len > 256, CONV:280-306): acc = 0 (CONV:145), acc += vals * w per tap (CONV:165), acc += b (CONV:169),
# acc * sigmoid(acc) (CONV:171), bf16 store (CONV:173-177). Tap j: its add is exact iff j = 0.
def stock_conv(K: Nat, j: Nat, b: Bool) -> List<&2, St>:
  match j:
    case 0n:
      List.append(&2, St, [Bf16In{}, MulB{}, AddX{}],
        List.append(&2, St, adds_after(Nat.sub(K, 1n)), List.append(&2, St, bias_step(b), [Sig{}, Mul32{}, StB{}])))
    case 1n+i:
      List.append(&2, St, [Bf16In{}, MulB{}],
        List.append(&2, St, adds_after(Nat.sub(K, 1n+i)), List.append(&2, St, bias_step(b), [Sig{}, Mul32{}, StB{}])))

# elpis ext 5111 _conv1d_prefill_qkv_output_kernel: x loaded fp32 and .to(tl.bfloat16) in kernel (P5111:138-142),
# acc = 0 (P5111:125), acc += vals * w (P5111:145), acc += b (P5111:149), acc * sigmoid(acc) (P5111:151), bf16
# store at the q / k / v block offset (P5111:159).
def tap_add(j: Nat, +K: Nat) -> List<&2, St>:
  match j:
    case 0n:
      AddX{} <> adds_after(Nat.sub(K, 1n))
    case 1n+i:
      adds_after(Nat.sub(K, 1n+i))

def elpis_conv(K: Nat, j: Nat, b: Bool) -> List<&2, St>:
  Bf16In{} <> (MulB{} <> List.append(&2, St, tap_add(j, K),
    List.append(&2, St, bias_step(b), [Sig{}, Mul32{}, StB{}])))

# class path of a trace (out-of-class steps contribute nothing here; they are listed by the trace itself)
def st_path(xs: List<&2, St>) -> Eb.Path:
  match xs:
    case Nil{}:
      Eb.zero()
    case Con{Add32{}, rest}:
      Eb.add(Eb.Path{1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}, st_path(rest))
    case Con{Mul32{}, rest}:
      Eb.add(Eb.Path{1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}, st_path(rest))
    case Con{_, rest}:
      st_path(rest)

# Route of a prefill chunk of seqlen rows through the conv (fc = the other 5111 conditions of P5111:38-42 all
# hold: bsz 1, not history, conv_state, fp32 contiguous qkv, one slot, switch on).
type Kern is Data:
  KBc{}        # seqlen <= 16: BC graph (decode/verify kernels; not modelled here)
  KCuda{}      # 16 < seqlen <= 32: ext.cuda_causal_conv1d_update (CONV:385-405), unpatched
  KSlot{}      # 32 < seqlen <= 256: _causal_conv1d_update_slotted_kernel on the bf16 copy (CONV:280-283)
  KOut{}       # seqlen > 256: _causal_conv1d_update_slotted_output_kernel on the bf16 copy (CONV:303-306)
  KFused{}     # ext 5111 conv1d_prefill_qkv on the fp32 qkv

def pick(b: Bool, t: Kern, f: Kern) -> Kern:
  match b:
    case True{}:
      t
    case False{}:
      f

def stock_route(+seqlen: Nat) -> Kern:
  pick(Nat.is_le(seqlen, 16n), KBc{},
    pick(Nat.is_le(seqlen, 32n), KCuda{}, pick(Nat.is_le(seqlen, 256n), KSlot{}, KOut{})))

def elpis_route(+seqlen: Nat, fc: Bool) -> Kern:
  pick(Bool.and(Nat.is_lt(256n, seqlen), fc), KFused{}, stock_route(seqlen))

# The per-element trace of the kernels that differ; every other kernel is the same unpatched code on both sides.
def is_same_kernel(a: Kern, b: Kern) -> Bool:
  match a b:
    case KBc{} KBc{}:
      True{}
    case KCuda{} KCuda{}:
      True{}
    case KSlot{} KSlot{}:
      True{}
    case KOut{} KOut{}:
      True{}
    case KFused{} KFused{}:
      True{}
    case _ _:
      False{}

# ======================================================================================================
# 3. Prefill GEMM (ext 3011 wide tile, 5112's K loop is the same text): one product term of K slice i, MMA m
# (m = 0: offset 32 i, m = 1: 32 i + 16, HF:258-262): the fp16-accumulator MMA pair from +0 (2 or 1 t16), the
# exact fp16 -> fp32 conversion, the fp32 add into acc (HF:61-63, r32; exact for slice 0, acc = 0), one fp32
# add per later slice. Defined on the slice list of hgemm_wide.bend (Spec.slices form).
# ======================================================================================================

def len_l(xs: List<&2, List<&2, Nat>>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{_, rest}:
      1n+len_l(rest)

def len_n(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{_, rest}:
      1n+len_n(rest)

def mma_paths(ms: List<&2, Nat>, +r32: Nat) -> List<&2, Eb.Path>:
  match ms:
    case Nil{}:
      []
    case Con{_, +rest}:
      Eb.Path{r32, 0n, 0n, 1n+len_n(rest), 0n, 0n, 0n, 0n} <> mma_paths(rest, r32)

# slice 0 adds into acc = 0 exactly; every later slice's add rounds
def slice_fold(first: Bool) -> Nat:
  match first:
    case True{}:
      0n
    case False{}:
      1n

def gemm_paths(sl: List<&2, List<&2, Nat>>, first: Bool) -> List<&2, Eb.Path>:
  match sl:
    case Nil{}:
      []
    case Con{ms, +rest}:
      List.append(&2, Eb.Path, mma_paths(ms, Nat.add(slice_fold(first), len_l(rest))), gemm_paths(rest, False{}))

def wide_paths(+K: Nat) -> List<&2, Eb.Path>:
  gemm_paths(HW.wide_acc(K), True{})

def served_paths(+K: Nat) -> List<&2, Eb.Path>:
  gemm_paths(HW.served_acc(K), True{})
