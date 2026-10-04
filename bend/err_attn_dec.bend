# Rounding-error paths (vocabulary bend/err_bound.bend) of decode / verify attention after ext 3030
# (patches/exl3-ext/3030-attn-verify-dominate.patch) against stock ExLlamaV3 355c6ee M = 1 decode, for
# EVERY live length L (a row at absolute position L - 1). Laws: bend/err_attn_dec_laws.bend; proofs:
# bend/err_attn_dec_proof.bend; source link and scans: bend/err_attn_dec_diff.py. The stock side, the
# route kinds, the shared segments and the hypotheses H_model, H_mma, H_zero, H_ptx, H_common, H_route,
# H_dispatch are bend/err_attn.bend's (its model of the stock kernels is reused unchanged: Ea.stock_leaf).
#
# What 3030 changes (E3: the 3030 tree = stock + patches/exl3/series + patches/exl3-ext/series; the
# diff script checks every quoted fragment and the compiled instruction counts, H_sass3030):
#   1. Integer running max. m = fmaxf(m, floorf(tmax)) (E3:exllamav3_ext/attn_verify.cu:475): the
#      rescale alpha = pow2i(m - m_new) (E3:attn_verify.cu:481) and the combine weight
#      pow2i(sw[d] - m_use) (E3:attn_verify.cu:660) are powers of two built from the exponent bits
#      (pow2i, E3:attn_verify.cu:148-152), so every product with them is exact (H_model). p is taken
#      against the tile's own max (E3:attn_verify.cu:483-484: FADD + MUFU.EX2, after the FMUL by
#      scale_log2, E3:attn_verify.cu:451) and the tile joins the m-scaled state through one factor
#      cs = ex2(tmax - m) (E3:attn_verify.cu:482).
#   2. Tile sum: one balanced 6-level tree over the 64 keys (p0 + p1, two lane xors,
#      E3:attn_verify.cu:486-488; the 8 warp partials pairwise, E3:attn_verify.cu:501-502), then
#      l = fmaf(tsum, cs, l * alpha) (E3:attn_verify.cu:503): l * alpha exact, one rounding.
#   3. P V in a fresh fp32 accumulator: 4 k16 HMMA steps from zero (mma16816_z for kk = 0,
#      E3:attn_verify.cu:535-536), then acc = fmaf(pv, cs, acc * alpha) (E3:attn_verify.cu:545-548):
#      one rounding per tile, no tensor-core step on the running acc.
#   4. Combine: the merged slots' exact terms v w, l w (E3:attn_verify.cu:670-671) summed by the
#      binary-counter pairwise tree over the merge order (E3:attn_verify.cu:672-698, 9 levels).
#   5. Back-rotation: stock's _rot_h32, two k16 HMMA steps from zero (E3:attn_verify.cu:731-732) then
#      fp16, then the gate (unchanged).
# The tile / slot partition (S = 20 CTAs, CTA x takes the absolute 64-key tiles x, x + 20, ...) is
# 3006's (bend/attn_stride.bend), unchanged.
#
# Routes of out[row, head, d] for a live key j = 64 (x + 20 q) + 16 g + r (DKey{x, q, g, r}: CTA / slot
# x < 20, tile q of that CTA, k16 group g < 4 of the tile, key r < 16 of the group):
#   DQ{kh, ks, i} q element -> q-hat -> p_j -> P V -> fold -> later folds -> combine -> quotient ->
#                 rotation position i -> gate                     (stock counterpart Ea.AQ{kh, ks, i})
#   DK{ks, i}     K cache value -> p_j -> ...                     (Ea.AK{ks, i})
#   DV{i}         V cache value -> P V -> ...                     (Ea.AV{i})
#   DC{kh, ks, i} q element -> score -> tile max -> cs -> fold -> ... of key j's tile (the coefficient
#                 route; compared with Ea.AQ{kh, ks, i})
#   DG{}          the gate element                                (Ea.AG{})
# There is no route through alpha or the combine weights (exact powers of two); the tile max / running
# max enter p, cs and alpha as exact selections and integer parts (fmaxf, floorf: no rounding), and
# cancel between numerator and denominator as stock's m does (H_route).
#
# The paths, per segment (H_zero: steps whose other operands are structural zeros are not counted):
#   own    t32 steps of key j's P V: its own k16 group (1 when another live key shares the group or an
#          earlier group of the tile holds a live key, else 0: the fresh accumulator starts at 0) + the
#          later live k16 groups of the tile                                     (e_own)
#   fold   r32: the own tile's fmaf(pv, cs, acc alpha) (a rounding in every tile: pv cs is not exact)
#          + one per later tile of the CTA (each later fold adds to the running acc)  (e_fold)
#   depth  r32: the combine tree's adds with a non-empty sibling block            (e_depth)
#   den    the denominator's worst path (H_route), bounded by e_dr (law dec_den_bound): through p_k:
#          xs + the tile tree (tdepth over the tile's live keys) + l's folds + the combine tree; through
#          cs: FMUL + FADD + ex2 + folds + tree.
#
# The stock route compared (H_route): stock key 0's route, with stock's denominator replaced by one of
# the terms of its maximum (key 0's p route, geo_s0's dr32). Eb.dom only gets harder to satisfy as the
# dominating path shrinks (law dec_dom_mono), so domination of this path is domination of stock's.
#
# Hypotheses added for 3030:
#   H_sass3030 The 3030 kernels compile (nvcc 12.9, sm_86, -O3 --use_fast_math) as the diff script's
#              compile shows: per tile and thread 6 FRND (floorf), 12 MUFU.EX2 (p) + 6 (cs), no MUFU.EX2
#              for alpha, 7 FADD per row slot in the warp-partial tree, 6 l FFMA, 12 + 36 HMMA in the
#              P V (zero-C first step), 48 acc FFMA; the combine: no MUFU.EX2 but the gate's, FMUL for
#              v w and l w, FADD for the tree, 8 HMMA for the rotation, RCP + FMUL for acc / lsum.
#   H_pow2     pow2i(d) = 2^d exactly for the integer-valued d it receives (|d| < 2^24; below 2^-126 it
#              returns 0, as ex2.approx.ftz flushes: an underflow, excluded by H_model on both sides).
import Base
import ./err_bound.bend as Eb
import ./err_attn.bend as Ea
import ./attn_stride.bend as St

# ==== aligned binary trees ====
# A balanced binary tree over the positions 0, 1, 2, ... (blocks of 2^k aligned at multiples of 2^k), of
# which the first n are live: position x passes, at level k, one add with a live sibling block iff the
# sibling of x's level-k block holds a live position. tdepth counts these over K levels by halving
# (block index x >> k, live blocks ceil(n / 2^k)); tbound counts the levels whose block size is below n.

# floor(x / 2)
def half(x: Nat) -> Nat:
  match x:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+pp:
          1n+half(pp)

# ceil(n / 2)
def halfup(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          1n
        case 1n+pp:
          1n+halfup(pp)

# x xor 1: the sibling block index
def flip(x: Nat) -> Nat:
  match x:
    case 0n:
      1n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+pp:
          2n+flip(pp)

def tdepth(K: Nat, +x: Nat, +n: Nat) -> Nat:
  match K:
    case 0n:
      0n
    case 1n+k:
      Nat.add(St.bit(Nat.is_lt(flip(x), n)), tdepth(k, half(x), halfup(n)))

def tbound(K: Nat, +n: Nat) -> Nat:
  match K:
    case 0n:
      0n
    case 1n+k:
      Nat.add(St.bit(Nat.is_lt(1n, n)), tbound(k, halfup(n)))

# ==== elpis 3030 geometry ====

type DKey is Data:
  DKey{x: Nat, q: Nat, g: Nat, r: Nat}

type DLeaf is Data:
  DQ{kh: Nat, ks: Nat, i: Nat}
  DK{ks: Nat, i: Nat}
  DV{i: Nat}
  DC{kh: Nat, ks: Nat, i: Nat}
  DG{}

# The absolute tile of CTA x's tile q: n0 = (cta + it * S) * AV_T (E3:attn_verify.cu:359), S = 20
def tile_of(+x: Nat, +q: Nat) -> Nat:
  Nat.add(x, Nat.mul(q, 20n))

def key_pos(+x: Nat, +q: Nat, +g: Nat, +r: Nat) -> Nat:
  Nat.add(Nat.mul(tile_of(x, q), 64n), Nat.add(Nat.mul(g, 16n), r))

# A key of the row at position L - 1: x < S = 20, g < AV_T / 16 = 4, r < 16, position < L
def key_ok(+L: Nat, k: DKey) -> Bool:
  match k:
    case DKey{+x, +q, +g, +r}:
      Bool.and(Nat.is_lt(x, 20n), Bool.and(Nat.is_lt(g, 4n), Bool.and(Nat.is_lt(r, 16n), Nat.is_lt(key_pos(x, q, g, r), L))))

# Live tiles (av_live_tiles) and live slots (av_live_slots, S = 20)
def e_T(+L: Nat) -> Nat:
  St.live_tiles(L)

def e_nsl(+L: Nat) -> Nat:
  St.live_slots(e_T(L), 20n)

# Live keys of the key's tile and its live k16 groups
def e_nt(+L: Nat, +x: Nat, +q: Nat) -> Nat:
  Nat.min(64n, Nat.sub(L, Nat.mul(tile_of(x, q), 64n)))

def e_lg(+L: Nat, +x: Nat, +q: Nat) -> Nat:
  St.cdiv(e_nt(L, x, q), 16n)

def e_shared(+L: Nat, +x: Nat, +q: Nat, +g: Nat) -> Bool:
  Bool.or(Nat.is_lt(0n, g), Nat.is_le(Nat.add(Nat.mul(g, 16n), 2n), e_nt(L, x, q)))

def e_own(+L: Nat, +x: Nat, +q: Nat, +g: Nat) -> Nat:
  Nat.add(St.bit(e_shared(L, x, q, g)), Nat.sub(Nat.sub(e_lg(L, x, q), g), 1n))

# Tiles of CTA x after tile q (av_cta_tiles(n_tiles, x, S) - 1 - q); fold = the own tile's + those
def e_later(+L: Nat, +x: Nat, +q: Nat) -> Nat:
  Nat.sub(Nat.sub(St.cta_tiles(e_T(L), x, 20n), 1n), q)

def e_fold(+L: Nat, +x: Nat, +q: Nat) -> Nat:
  1n+e_later(L, x, q)

# The combine tree (9 binary-counter levels, MERGE_LV) over the row's live slots
def e_depth(+L: Nat, +x: Nat) -> Nat:
  tdepth(9n, x, e_nsl(L))

# The tile tree of key j's p: 6 levels over the tile's live keys (tile-local position 16 g + r)
def e_tsum(+L: Nat, +x: Nat, +q: Nat, +g: Nat, +r: Nat) -> Nat:
  tdepth(6n, Nat.add(Nat.mul(g, 16n), r), e_nt(L, x, q))

# Bounds over all keys: most tiles of a CTA (CTA 0's), the tree depths, the own groups
def e_n0(+L: Nat) -> Nat:
  St.cta_tiles(e_T(L), 0n, 20n)

def e_D(+L: Nat) -> Nat:
  tbound(9n, e_nsl(L))

def e_TE(+L: Nat) -> Nat:
  tbound(6n, L)

def e_OE(+L: Nat) -> Nat:
  Nat.sub(Nat.min(4n, St.cdiv(L, 16n)), St.bit(Nat.is_eq(L, 1n)))

# The denominator bound: xs (2) + tile tree + folds + combine tree
def e_dr(+L: Nat) -> Nat:
  Nat.add(2n, Nat.add(e_TE(L), Nat.add(e_n0(L), e_D(L))))

# ==== elpis 3030 path segments ====

# x = sc * scale_log2 (FMUL, E3:attn_verify.cu:451), p = ex2(x - tmax) (FADD + MUFU.EX2,
# E3:attn_verify.cu:483); for DC: FMUL, cs = ex2(tmax - m) (FADD + MUFU.EX2, E3:attn_verify.cu:482)
def e_xs() -> Eb.Path:
  Ea.cat(Ea.r32(2n), Ea.ex2(1n))

# oh = fp16(acc / lsum); _rot_h32 as stock (two k16 HMMA from zero, E3:attn_verify.cu:731-732):
# position i < 16 passes both; fp16 out; the gate __hmul2
def e_postb(lo: Bool) -> Eb.Path:
  Ea.cat(Ea.r16(1n), Ea.cat(Ea.t32(Ea.s_rot(lo)), Ea.r16(2n)))

# A key route's numerator steps from P V on: own + folds + combine tree
def e_cc(+L: Nat, +x: Nat, +q: Nat, +g: Nat) -> Eb.Path:
  Ea.cat(Ea.cat(Ea.t32(e_own(L, x, q, g)), Ea.r32(e_fold(L, x, q))), Ea.r32(e_depth(L, x)))

# The coefficient route's: folds + combine tree (cs multiplies the whole tile: no MMA step)
def e_cs(+L: Nat, +x: Nat, +q: Nat) -> Eb.Path:
  Ea.cat(Ea.r32(e_fold(L, x, q)), Ea.r32(e_depth(L, x)))

# The denominator's part beyond its q rotation (Ea.den's form): dr32 bound, Q.K^T 16 t32, one ex2
def e_dg(+L: Nat) -> Eb.Path:
  Eb.Path{e_dr(L), 16n, 0n, 0n, 0n, 1n, 0n, 0n}

# ==== the route skeletons (Ea.s_aq / s_ak / s_av's cat structure) ====
# sk4: numerator a + (b + (c + (d + X))), quotient (+ q rotation of the denominator + Y + div), post.
def sk4(a: Eb.Path, b: Eb.Path, c: Eb.Path, d: Eb.Path, X: Eb.Path, Y: Eb.Path, po: Eb.Path) -> Eb.Path:
  Ea.cat(Ea.cat(Ea.cat(a, Ea.cat(b, Ea.cat(c, Ea.cat(d, X)))), Ea.cat(Ea.cat(Ea.qrot(0n), Y), Ea.div())), po)

def sk1(a: Eb.Path, X: Eb.Path, Y: Eb.Path, po: Eb.Path) -> Eb.Path:
  Ea.cat(Ea.cat(Ea.cat(a, X), Ea.cat(Ea.cat(Ea.qrot(0n), Y), Ea.div())), po)

def elpis_route(+L: Nat, +x: Nat, +q: Nat, +g: Nat, l: DLeaf) -> Eb.Path:
  match l:
    case DQ{kh, ks, +i}:
      sk4(Ea.qrot(kh), Ea.qk(ks), e_xs(), Ea.pconv(), e_cc(L, x, q, g), e_dg(L), e_postb(Nat.is_lt(i, 16n)))
    case DK{ks, +i}:
      sk4(Ea.deq(), Ea.qk(ks), e_xs(), Ea.pconv(), e_cc(L, x, q, g), e_dg(L), e_postb(Nat.is_lt(i, 16n)))
    case DV{+i}:
      sk1(Ea.deq(), e_cc(L, x, q, g), e_dg(L), e_postb(Nat.is_lt(i, 16n)))
    case DC{kh, ks, +i}:
      sk4(Ea.qrot(kh), Ea.qk(ks), e_xs(), Eb.zero(), e_cs(L, x, q), e_dg(L), e_postb(Nat.is_lt(i, 16n)))
    case DG{}:
      Ea.gate()

def elpis_leaf(+L: Nat, k: DKey, l: DLeaf) -> Eb.Path:
  match k:
    case DKey{+x, +q, +g, r}:
      elpis_route(L, x, q, g, l)

# The stock route compared with each elpis route kind
def stock_of(l: DLeaf) -> Ea.ALeaf:
  match l:
    case DQ{kh, ks, i}:
      Ea.AQ{kh, ks, i}
    case DK{ks, i}:
      Ea.AK{ks, i}
    case DV{i}:
      Ea.AV{i}
    case DC{kh, ks, i}:
      Ea.AQ{kh, ks, i}
    case DG{}:
      Ea.AG{}

# ==== stock 355c6ee geometry, key 0 of a row at position L - 1 ====
# Block-table width 16 ceil(ceil(L / 256) / 16) pages (S:generator/generator.py:965-966; L = the job's
# sequence length, S:generator/job.py:371-378), bound = width * 256 + q_len (q_len 1),
# num_splits = max(1, min(41, ceil(bound / 128))), split_len = ceil(ceil(bound / num_splits) / 32) * 32
# (S:exllamav3_ext/libtorch/attention.cpp:391-393; splits_cap 41, BLOCK_N 32, S:bc_attn.py:278,287-288).
def s_bound(+L: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.mul(St.cdiv(St.cdiv(L, 256n), 16n), 16n), 256n), 1n)

# split_config of a given bound B (S:attention.cpp:391-393)
def s_nsB(+B: Nat) -> Nat:
  Nat.max(1n, Nat.min(41n, St.cdiv(B, 128n)))

def s_slB(+B: Nat) -> Nat:
  Nat.mul(St.cdiv(St.cdiv(B, s_nsB(B)), 32n), 32n)

def s_ns(+L: Nat) -> Nat:
  s_nsB(s_bound(L))

def s_sl(+L: Nat) -> Nat:
  s_slB(s_bound(L))

# Live splits (n_start = split * split_len < L) and split 0's live keys, 32-key tiles and k16 groups
def s_nlive(+L: Nat) -> Nat:
  St.cdiv(L, s_sl(L))

def s_ls0(+L: Nat) -> Nat:
  Nat.min(L, s_sl(L))

def s_tiles0(+L: Nat) -> Nat:
  St.cdiv(s_ls0(L), 32n)

def s_groups0(+L: Nat) -> Nat:
  St.cdiv(s_ls0(L), 16n)

def s_gtile0(+L: Nat) -> Nat:
  St.cdiv(Nat.min(L, 32n), 16n)

# Key 0: its own k16 group counts when another live key shares it (L >= 2), plus tile 0's later groups;
# later = the later 32-key tiles of split 0, laterk their live groups; after = the later live splits
def s_own0(+L: Nat) -> Nat:
  Nat.add(St.bit(Nat.is_lt(1n, L)), Nat.sub(s_gtile0(L), 1n))

def s_laterk0(+L: Nat) -> Nat:
  Nat.sub(s_groups0(L), s_gtile0(L))

def s_later0(+L: Nat) -> Nat:
  Nat.sub(s_tiles0(L), 1n)

def s_after0(+L: Nat) -> Nat:
  Nat.sub(s_nlive(L), 1n)

# tl.sum over the 32-key tile (in-thread pair, lane xor 2 / 1, warp xor 2 / 1: offsets 1, 4, 2, 16, 8,
# H_ptx): key 0's adds with a live partner set
def s_tsum0(+L: Nat) -> Nat:
  Nat.add(St.bit(Nat.is_lt(1n, L)), Nat.add(St.bit(Nat.is_lt(4n, L)), Nat.add(St.bit(Nat.is_lt(2n, L)),
    Nat.add(St.bit(Nat.is_lt(16n, L)), St.bit(Nat.is_lt(8n, L))))))

# Key 0's p route into the denominator: 2 (sub, log2e mul) + tile sum + l folds of the later tiles +
# the combine fma + later splits: one term of stock's denominator maximum (H_route)
def s_dr0(+L: Nat) -> Nat:
  Nat.add(2n, Nat.add(s_tsum0(L), Nat.add(s_later0(L), 1n+s_after0(L))))

def geo_s0(+L: Nat) -> Ea.Geo:
  Ea.Geo{s_own0(L), s_later0(L), s_laterk0(L), s_after0(L), s_dr0(L), 16n, 1n}

# ==== the compared totals ====
# Beyond the segments both routes share, a 3030 key route has t32 = own + 16 and r32 = fold + depth +
# dr; stock key 0's has t32 = (own + laterk) + 16 and r32 = (later + (1 + after)) + dr32 (both with one
# ex2, H_route). e_rt is the 3030 t32 + r32 with every key-dependent count replaced by its bound over
# all keys (own <= e_OE, fold <= e_n0, depth <= e_D: laws in bend/err_attn_dec_laws.bend), s_rt stock
# key 0's; dec_dom rests on e_OE <= own0 + laterk0 and e_rt <= s_rt for every L >= 1.
def e_rt(+L: Nat) -> Nat:
  Nat.add(Nat.add(e_OE(L), 16n), Nat.add(Nat.add(e_n0(L), e_D(L)), e_dr(L)))

def s_rt(+L: Nat) -> Nat:
  Nat.add(Nat.add(Nat.add(s_own0(L), s_laterk0(L)), 16n), Nat.add(Nat.add(s_later0(L), 1n+s_after0(L)), s_dr0(L)))

# Componentwise order of two paths (every class count of p at most q's)
def path_le(p: Eb.Path, q: Eb.Path) -> Bool:
  match p:
    case Eb.Path{a1, b1, c1, d1, h1, e1, f1, g1}:
      match q:
        case Eb.Path{a2, b2, c2, d2, h2, e2, f2, g2}:
          Bool.and(Nat.is_le(a1, a2), Bool.and(Nat.is_le(b1, b2), Bool.and(Nat.is_le(c1, c2),
            Bool.and(Nat.is_le(d1, d2), Bool.and(Nat.is_le(h1, h2), Bool.and(Nat.is_le(e1, e2),
              Bool.and(Nat.is_le(f1, f2), Nat.is_le(g1, g2))))))))

# ==== composite convention (coefficient errors on the key routes) ====
# A product with a computed coefficient carries the coefficient's own steps: elpis 3030's key routes
# carry cs (FADD + ex2) once; alpha and the combine weights are exact. Stock's key-0 routes carry the
# combine weight w = tl.exp(m_s - m_safe) (FADD + FMUL + ex2, S:triton_paged.py:1054) and one
# alpha = tl.exp(m - m_exp) (FADD + FMUL + ex2, S:triton_paged.py:961) per later tile of split 0.
def e_coef(l: DLeaf) -> Eb.Path:
  match l:
    case DQ{kh, ks, i}:
      Ea.cat(Ea.r32(1n), Ea.ex2(1n))
    case DK{ks, i}:
      Ea.cat(Ea.r32(1n), Ea.ex2(1n))
    case DV{i}:
      Ea.cat(Ea.r32(1n), Ea.ex2(1n))
    case DC{kh, ks, i}:
      Eb.zero()
    case DG{}:
      Eb.zero()

def s_coef(+L: Nat, l: DLeaf) -> Eb.Path:
  match l:
    case DQ{kh, ks, i}:
      Ea.cat(Ea.r32(Nat.mul(1n+s_later0(L), 2n)), Ea.ex2(1n+s_later0(L)))
    case DK{ks, i}:
      Ea.cat(Ea.r32(Nat.mul(1n+s_later0(L), 2n)), Ea.ex2(1n+s_later0(L)))
    case DV{i}:
      Ea.cat(Ea.r32(Nat.mul(1n+s_later0(L), 2n)), Ea.ex2(1n+s_later0(L)))
    case DC{kh, ks, i}:
      Eb.zero()
    case DG{}:
      Eb.zero()
