# Rounding-error paths of the ext 3031 prefill attention (exllamav3_ext/pattn_kernel.cuh, pattn8_kernel.cuh) and of stock
# ExLlamaV3 355c6ee's Triton prefill (served route: unsplit or split + combine), in the vocabulary of bend/err_bound.bend.
# Laws: err_pfix_laws.bend (contract), proofs: err_pfix_proof.bend, gate: err_pfix_gate.bend, source link:
# err_pfix_diff.py (every "X:n" below is checked there).
#
# Sources (read-only): TP = stock modules/attention_fn/triton_paged.py; PTX / CPTX = the served stock prefill / combine
# kernels compiled for sm_86 (paths in err_prefill.bend's header; the stock segments are the ones err_prefill.bend
# transcribes and err_prefill_diff.py links); K = patched exllamav3_ext/pattn_kernel.cuh after ext 3031 (pattn8_kernel.cuh
# runs the same per-warp text, bend/pattn8_sched_laws.bend); P = patches/exl3-ext/3031-prefill-pattn-dominate.patch.
#
# Row model. A row at absolute position p sees keys 0 .. p: n = p / 32 + 1 key tiles of 32. Tiles with no visible key
# leave m, l, acc bit-unchanged in both kernels (hypothesis H_masked_exact of err_prefill_laws.bend). Stock's 64-row block
# of the row starts at q64; its maskless tiles are those below n_full = ((q64 + 1) / 32) * 32 (TP:1533, K: n_full), the
# same in both kernels (the score segment is stock's: err_prefill_laws.bend score_eq): tile T is interior iff T < I,
# I = (q64 + 1) / 32.
#
# elpis 3031: the row's tiles form chains of E = (q64 + 256) / 256 tiles (K: ch_tiles), chain k = tiles k E .. k E + E - 1;
# each chain is an online softmax from zero (K: park_chain), its partial (O, m, l) is parked in fp32 (exact) and the
# epilogue combines the K = ceil(n / E) chains (K: pattn_chain_combine) with stock's weights w = exp2(m_k - m_max) and the
# pairs + tail fold of chain_step. One chain (K = 1): the 3022 v4 epilogue, no combine.
# stock: unsplit (num_splits = 1, TP:1849-1857), or num_splits = ns in 2 .. 8 (TP:1859-1871: candidates 1 .. 6, 8): split
# k of the row's block holds the tiles k S .. k S + S - 1, S = ceil(ceil(n_hi / ns) / 32) (TP:1476-1478), each an online
# softmax from zero, stored fp32 (TP:1554-1564), combined in split order (TP:1610-1635).
#
# Path field order: Eb.Path{r32, t32, r16, t16, q8, ex2, rcp, rsq}.
import Base
import ./err_bound.bend as Eb

# n copies of segment s concatenated in front of p (a path is a multiset of steps)
def rep_add(n: Nat, +s: Eb.Path, p: Eb.Path) -> Eb.Path:
  match n:
    case 0n:
      p
    case 1n+k:
      Eb.add(s, rep_add(k, s, p))

# p if b, else the empty path
def when(b: Bool, p: Eb.Path) -> Eb.Path:
  match b:
    case True{}:
      p
    case False{}:
      Eb.zero()

def own_t32(h: Bool) -> Nat:
  match h:
    case False{}:
      2n
    case True{}:
      1n

# ==== segments ====

# The key's P V products in their tile: two chained m16n8k16 fp32 MMAs (K: tp from zero C, 2 or 1 t32; stock TP:1376 ->
# PTX:2800-2893 with C = acc * alpha: 2 or 1 t32 on the leaf). h = False / True: key in the first / second k16 half.
def own(h: Bool) -> Eb.Path:
  Eb.Path{0n, own_t32(h), 0n, 0n, 0n, 0n, 0n, 0n}

# elpis: a tile that is not its chain's first joins O by one fma.rn (K: o = f_fma_pv(o, alpha, tp)); in the chain's first
# tile O = 0 and alpha = 0 (m = -inf after park_chain or at start), so fma(0, 0, tp) is exact. Same for the denominator:
# l = fma.rn(l, alpha, sum) rounds the tile's sum except in the chain's first tile (both kernels: K, TP:1346 -> PTX:2457).
def fold() -> Eb.Path:
  Eb.Path{1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

# elpis, each later tile of the chain, numerator: o = fma.rn(o, alpha, tp) (r32), alpha = ex2(f_sub(m, m_use)) (r32, ex2)
def e_later() -> Eb.Path:
  Eb.Path{2n, 0n, 0n, 0n, 0n, 1n, 0n, 0n}

# stock, each later tile of the split, numerator: acc * alpha (PTX:2703, r32), the MMA pair with C = acc (2 t32),
# alpha = exp2(m - m_new) (PTX:2275-2291: r32, ex2)
def s_later() -> Eb.Path:
  Eb.Path{2n, 2n, 0n, 0n, 0n, 1n, 0n, 0n}

# both, each later tile, denominator: l = fma.rn(l, alpha, sum) (r32) with the same alpha (r32, ex2)
def den_later() -> Eb.Path:
  Eb.Path{2n, 0n, 0n, 0n, 0n, 1n, 0n, 0n}

# denominator in-tile depth, every key: elpis 3031 sums a lane's 8 p as a balanced tree (K: depth 3) and quad-reduces the
# lane partials once at the end (K: 2 f_add); stock's tl.sum is a depth-5 tree (PTX:2297-2440). Both 5.
def den_in() -> Eb.Path:
  Eb.Path{5n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

# P to fp16 for the P V MMA (r16), the division O / l (div.full: rcp class), the fp16 store (r16): both kernels
def fixed() -> Eb.Path:
  Eb.Path{0n, 0n, 2n, 0n, 0n, 0n, 1n, 0n}

# score segment of a key (both kernels, err_prefill.bend score_s / score_e): interior: fma(raw, c, -m) (1 r32), masked:
# s = raw * c then s - m (2 r32); the Q K^T product term of k16 step s passes 16 - s fp32 MMA steps; exp2 (ex2)
def score(interior: Bool, s: Nat) -> Eb.Path:
  match interior:
    case True{}:
      Eb.Path{1n, Nat.sub(16n, s), 0n, 0n, 0n, 1n, 0n, 0n}
    case False{}:
      Eb.Path{2n, Nat.sub(16n, s), 0n, 0n, 0n, 1n, 0n, 0n}

# combine of a chain / split that passes c roundings of the fold: w = exp2(m_k - m_safe) (r32 sub, ex2), then c fp32
# roundings (stock CPTX:186-188 / 522, 587-591; K: chain_w, chain_step)
def comb(c: Nat) -> Eb.Path:
  Eb.Path{1n+c, 0n, 0n, 0n, 0n, 1n, 0n, 0n}

# ==== elpis 3031 combine: roundings of chain k's term when K >= 2 chains are folded (K: chain_step) ====
# B = (K > 4 ? K - 3 : 1) body chains: pairs fma(x_c, w_c, x_{c+1} * w_{c+1}) (chain c: 1 rounding, c + 1: 2), a lone last
# body chain x_c * w_c (1); the P = ceil(B / 2) body steps are added in order (step 0 starts the sum: its chains get
# P - 1 adds, step j >= 1 gets P - j); then the K - B tail chains folded by fma in order (chain k >= B: K - k).

def pick(b: Bool, +x: Nat, +y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

def body_b(+K: Nat) -> Nat:
  pick(Nat.is_lt(4n, K), Nat.sub(K, 3n), 1n)

# roundings inside the body for chain k < B (step j = k / 2)
def body_c(+k: Nat, +B: Nat) -> Nat:
  +j = Nat.div(k, 2n)
  +steps = Nat.div(Nat.add(B, 1n), 2n)
  +base = pick(Nat.is_eq(Nat.mod(k, 2n), 1n), 2n, 1n)
  +adds = pick(Nat.is_eq(j, 0n), Nat.sub(steps, 1n), Nat.sub(steps, j))
  Nat.add(base, adds)

def chain_c(+k: Nat, +K: Nat) -> Nat:
  +B = body_b(K)
  pick(Nat.is_lt(k, B), Nat.add(body_c(k, B), Nat.sub(K, B)), Nat.sub(K, k))

# ==== the leaf composites ====
# elpis 3031: numerator key in chain k at chain-local tile t with a later tiles of the chain, half h, k16 step s of its
# score product; denominator key in chain kd at local tile td with b later tiles, score step s2; the row has K chains of
# E tiles and I interior tiles (key tile kE + t interior iff kE + t < I).
def e_num(+E: Nat, +K: Nat, +I: Nat, +k: Nat, +t: Nat, +a: Nat, h: Bool, +s: Nat) -> Eb.Path:
  Eb.add(own(h), Eb.add(when(Nat.is_lt(0n, t), fold()), Eb.add(rep_add(a, e_later(), Eb.zero()),
    Eb.add(when(Nat.is_lt(1n, K), comb(chain_c(k, K))), score(Nat.is_lt(Nat.add(Nat.mul(k, E), t), I), s)))))

def e_den(+E: Nat, +K: Nat, +I: Nat, +k: Nat, +t: Nat, +a: Nat, +s: Nat) -> Eb.Path:
  Eb.add(den_in(), Eb.add(when(Nat.is_lt(0n, t), fold()), Eb.add(rep_add(a, den_later(), Eb.zero()),
    Eb.add(when(Nat.is_lt(1n, K), comb(chain_c(k, K))), score(Nat.is_lt(Nat.add(Nat.mul(k, E), t), I), s)))))

def elpis_leaf(+E: Nat, +K: Nat, +I: Nat, +k: Nat, +t: Nat, +a: Nat, h: Bool, +s: Nat,
    +kd: Nat, +td: Nat, +b: Nat, +s2: Nat) -> Eb.Path:
  Eb.add(e_num(E, K, I, k, t, a, h, s), Eb.add(e_den(E, K, I, kd, td, b, s2), fixed()))

# stock: numerator key in split k of the row's Ks non-empty splits of S tiles, split-local tile t with a later tiles of
# the split, half h; denominator key likewise (kd, td, b). The numerator key's own tile adds no rounding to it (the MMA C
# operand acc * alpha rounds only older terms); the denominator key's tile sum joins l by one fma unless it is the
# split's first tile. With sp (num_splits >= 2) split k passes Ks - k combine roundings, split 0 Ks (its fma into acc = 0,
# CPTX:522, then one per later non-empty split; an empty split has w = 0 and o_s = 0 and changes nothing). Unsplit
# (sp = False): one chain over the row, no combine.
def s_comb_c(+k: Nat, +Ks: Nat) -> Nat:
  match k:
    case 0n:
      Ks
    case 1n+j:
      Nat.sub(Ks, 1n+j)

def s_num(+S: Nat, sp: Bool, +Ks: Nat, +I: Nat, +k: Nat, +t: Nat, +a: Nat, h: Bool, +s: Nat) -> Eb.Path:
  Eb.add(own(h), Eb.add(rep_add(a, s_later(), Eb.zero()),
    Eb.add(when(sp, comb(s_comb_c(k, Ks))), score(Nat.is_lt(Nat.add(Nat.mul(k, S), t), I), s))))

def s_den(+S: Nat, sp: Bool, +Ks: Nat, +I: Nat, +k: Nat, +t: Nat, +a: Nat, +s: Nat) -> Eb.Path:
  Eb.add(den_in(), Eb.add(when(Nat.is_lt(0n, t), fold()), Eb.add(rep_add(a, den_later(), Eb.zero()),
    Eb.add(when(sp, comb(s_comb_c(k, Ks))), score(Nat.is_lt(Nat.add(Nat.mul(k, S), t), I), s)))))

def stock_leaf(+S: Nat, sp: Bool, +Ks: Nat, +I: Nat, +k: Nat, +t: Nat, +a: Nat, h: Bool, +s: Nat,
    +kd: Nat, +td: Nat, +b: Nat, +s2: Nat) -> Eb.Path:
  +p = sp
  Eb.add(s_num(S, p, Ks, I, k, t, a, h, s), Eb.add(s_den(S, p, Ks, I, kd, td, b, s2), fixed()))

# stock's witness: numerator and denominator keys in tile 0 (first k16 half), the head of split 0 with N tiles of the row
# (N = n unsplit). A real stock leaf of the row: tile 0 lies in split 0 and every row sees key 0.
def stock_witness(+N: Nat, sp: Bool, +Ks: Nat, +I: Nat, +s: Nat, +s2: Nat) -> Eb.Path:
  stock_leaf(1n, sp, Ks, I, 0n, 0n, Nat.sub(N, 1n), False{}, s, 0n, 0n, Nat.sub(N, 1n), s2)

# ==== kernel geometry (C int arithmetic on the non-negative values used is Nat arithmetic) ====
# K: ch_tiles = (q_abs64 + 256) / 256
def e_len(+q64: Nat) -> Nat:
  Nat.div(Nat.add(q64, 256n), 256n)

# keys 0 .. p visible: tiles 0 .. p / 32
def n_tiles(+p: Nat) -> Nat:
  1n+Nat.div(p, 32n)

# n_full / 32 (TP:1533; K: n_full)
def interior_tiles(+q64: Nat) -> Nat:
  Nat.div(Nat.add(q64, 1n), 32n)

# ceil division as written (a + b - 1) / b
def cdiv(+a: Nat, +b: Nat) -> Nat:
  Nat.div(Nat.sub(Nat.add(a, b), 1n), b)

# K: nch = (ntiles + ch_tiles - 1) / ch_tiles (the row's chains: the same formula over its own tiles)
def n_chains(+n: Nat, +E: Nat) -> Nat:
  cdiv(n, E)

# chain length of chain k
def chain_len(+n: Nat, +E: Nat, +k: Nat) -> Nat:
  Nat.min(E, Nat.sub(n, Nat.mul(k, E)))

# stock split length in tiles: span / 32 with span = cdiv(cdiv(n_hi, ns), 32) * 32 (TP:1476)
def split_len(+nh: Nat, +ns: Nat) -> Nat:
  cdiv(cdiv(nh, ns), 32n)

# stock's split-0 length for the row (all n tiles when unsplit) and its non-empty split count
def stock_n(+n: Nat, +nh: Nat, +ns: Nat) -> Nat:
  pick(Nat.is_lt(1n, ns), Nat.min(split_len(nh, ns), n), n)

def stock_ks(+n: Nat, +nh: Nat, +ns: Nat) -> Nat:
  pick(Nat.is_lt(1n, ns), cdiv(n, split_len(nh, ns)), 1n)

# The elpis composite of a row at absolute position p of the 64-row block starting at q64: numerator key in tile T
# (half h, score step s), denominator key in tile Td (score step s2).
def elpis_at(+q64: Nat, +p: Nat, +T: Nat, h: Bool, +s: Nat, +Td: Nat, +s2: Nat) -> Eb.Path:
  +E = e_len(q64)
  +n = n_tiles(p)
  +K = n_chains(n, E)
  +k = Nat.div(T, E)
  +t = Nat.mod(T, E)
  +kd = Nat.div(Td, E)
  +td = Nat.mod(Td, E)
  elpis_leaf(E, K, interior_tiles(q64), k, t, Nat.sub(Nat.sub(chain_len(n, E, k), 1n), t), h, s,
    kd, td, Nat.sub(Nat.sub(chain_len(n, E, kd), 1n), td), s2)

# stock's witness for the same row in a block with n_hi = nh and num_splits = ns
def stock_at(+q64: Nat, +nh: Nat, +p: Nat, +ns: Nat, +s: Nat, +s2: Nat) -> Eb.Path:
  +n = n_tiles(p)
  stock_witness(stock_n(n, nh, ns), Nat.is_lt(1n, ns), stock_ks(n, nh, ns), interior_tiles(q64), s, s2)
