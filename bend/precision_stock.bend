# Stock ExLlamaV3 355c6ee (r0b0tlab/exllamav3 355c6ee10fbd25b79070316a81ea0708cc18155a) decode GEMM
# dispatch and accumulation schedules, transcribed over Nat from the unpatched sources. This model is
# INDEPENDENT of the elpis models: it imports only the class vocabulary bend/precision_order.bend.
# Line references (paths under exllamav3/):
#   G:   exllamav3_ext/quant/exl3_gemm.cu            GI: exllamav3_ext/quant/exl3_gemm_inner.cuh
#   GK:  exllamav3_ext/quant/exl3_gemm_kernel.cuh     KM: exllamav3_ext/quant/exl3_kernel_map.cuh
#   V:   exllamav3_ext/quant/exl3_gemv.cu             VK: exllamav3_ext/quant/exl3_gemv_kernel.cuh
#   I8:  exllamav3_ext/quant/exl3_gemv_int8.cu        CF: model/config.py   ML: modules/multilinear.py
# No elpis patch touches G, GI, GK, KM, V, VK, I8, coop_autotune.cu, CF or ML (patches/exl3-ext/series
# and patches/exl3/series: no hunk on these files), so the stock kernels elpis still runs are these.
#
# Nat model of accumulation SCHEDULES: which kernel runs, how many k-values each thread accumulates in
# fp16 before folding into fp32, and whether block partials cross in fp32 -- never a float value.
# Served device: sm_86 (RTX 3090, 82 SMs): EXL3_GEMM_H_ACC = 1 (GI:16-17: fp16 MMA accumulators folded
# into fp32 by reduce(), GI:799-827), CC_AMPERE, default env (EXL3_INT8_GEMV unset = 2, EXL3_GEMV unset
# = 1, no forced shape / SM count).
import Base
import ./precision_order.bend as Ord

# ==== shape tables (KM:67-70) ====

def sel(c: Bool, t: Nat, f: Nat) -> Nat:
  match c:
    case True{}:
      t
    case False{}:
      f

# KM:68 EXL3_GEMM_TILESIZE_K  0, 16, 32, 32, 16, 32, 32
def tilesize_k(+s: Nat) -> Nat:
  sel(Bool.or(Nat.is_eq(s, 1n), Nat.is_eq(s, 4n)), 16n, 32n)

# KM:69 EXL3_GEMM_TILESIZE_N  0, 128, 128, 256, 512, 256, 128
def tilesize_n(+s: Nat) -> Nat:
  sel(Nat.is_eq(s, 4n), 512n, sel(Bool.or(Nat.is_eq(s, 3n), Nat.is_eq(s, 5n)), 256n, 128n))

# ==== tensor-core kernel: slice partition and fold schedule (exl3_gemm_kernel_inner) ====

# GI:91-92 tiles_k = size_k / TILESIZE_K, tiles_n = size_n / TILESIZE_N; the slice space is
# tiles_k * tiles_n tiles, column-major (k fastest): GI:105-106 index_k = i % tiles_k,
# index_n = i / tiles_k.
def tiles_k(+k: Nat, +s: Nat) -> Nat:
  Nat.div(k, tilesize_k(s))

def tiles_n(+n: Nat, +s: Nat) -> Nat:
  Nat.div(n, tilesize_n(s))

def tiles(+k: Nat, +n: Nat, +s: Nat) -> Nat:
  Nat.mul(tiles_k(k, s), tiles_n(n, s))

# GI:98-100 slice_beg = tiles_k * tiles_n * blockIdx.x / num_slices (num_slices = gridDim.x)
def slice_beg(+b: Nat, +T: Nat, +G: Nat) -> Nat:
  Nat.div(Nat.mul(T, b), G)

# GI:100 slice_end = tiles_k * tiles_n * (blockIdx.x + 1) / num_slices
def slice_end(+b: Nat, +T: Nat, +G: Nat) -> Nat:
  Nat.div(Nat.mul(T, 1n+b), G)

# Events of one block's main loop: Tile = one k-tile MMA into the fp16 accumulators frag_c_h
# (GI:884-896; each thread's sub_k group, GI:85 / GI:290 / GI:305, multiplies one 16-deep k block per
# tile, so a tile adds 16 k-values to a thread's fp16 run); Reduce = reduce(): fold frag_c_h into the
# fp32 frag_c (GI:801-827), cross-block partial exchange (GI:829-871) and clear_frag_c (GI:873).
type Ev is Data:
  Tile{n: Nat, k: Nat}
  Reduce{n: Nat}

def red(c: Bool, +n: Nat, rest: List<&2, Ev>) -> List<&2, Ev>:
  match c:
    case True{}:
      Reduce{n} <> rest
    case False{}:
      rest

# The main loop (GI:929-945, FSTAGE / FSTAGE_OLD; the fragment-stage unrolling does not change the event
# order) from the pipe-2 state slice2_k = k, slice2_n = n, slice2_iters = iters (GI:202-205):
#   matmul; if (slice2_k == tiles_k - 1 || slice2_iters == 1) reduce(); advance2(); if (!slice2_iters) break;
# advance2 (GI:223-232): slice2_k++; slice2_iters--; if (slice2_k >= tiles_k) { slice2_k = 0; slice2_n++; }
def loop(+iters: Nat, +k: Nat, +n: Nat, +tk: Nat) -> List<&2, Ev>:
  match iters:
    case 0n:
      Nil{}
    case 1n+r:
      +wrap = Nat.is_le(tk, 1n+k)
      Tile{n, k} <> red(Bool.or(Nat.is_eq(k, Nat.sub(tk, 1n)), Nat.is_eq(1n+r, 1n)), n,
        loop(r, sel(wrap, 0n, 1n+k), sel(wrap, 1n+n, n), tk))

# Block b's loop: slice0_k = index_k(slice_beg), slice0_n = index_n(slice_beg), slice0_iters =
# slice_len (GI:114-116), nothing when slice_len < 1 (GI:102).
def block(+b: Nat, +T: Nat, +G: Nat, +tk: Nat) -> List<&2, Ev>:
  +s = slice_beg(b, T, G)
  loop(Nat.sub(slice_end(b, T, G), s), Nat.mod(s, tk), Nat.div(s, tk), tk)

# fp16 run lengths (in tiles) of an event list: the tiles between two reduce() calls. `open` counts the
# tiles since the last reduce; a trailing open run is emitted too (the loop never leaves one: its last
# iteration has slice2_iters == 1).
def runs(evs: List<&2, Ev>, +open: Nat) -> List<&2, Nat>:
  match evs:
    case Nil{}:
      match open:
        case 0n:
          Nil{}
        case 1n+p:
          [1n+p]
    case ev <> rest:
      match ev:
        case Tile{n, k}:
          runs(rest, 1n+open)
        case Reduce{n}:
          open <> runs(rest, 0n)

# Column runs of a tile range (the intended schedule): the tiles x .. x + left - 1 split into maximal
# pieces of consecutive tiles of one output column: tile x + 1 starts a new column iff its k index
# (x + 1) % tk (GI:105 index_k) is 0, and the range ends after its last tile. `open` counts the current
# piece.
def col_runs.close(c: Bool, +open: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case True{}:
      open <> rest
    case False{}:
      rest

def col_runs.next(c: Bool, +open: Nat) -> Nat:
  match c:
    case True{}:
      0n
    case False{}:
      open

def col_runs(+left: Nat, +x: Nat, +tk: Nat, +open: Nat) -> List<&2, Nat>:
  match left:
    case 0n:
      Nil{}
    case 1n+r:
      +cut = Bool.or(Nat.is_eq(Nat.mod(1n+x, tk), 0n), Nat.is_eq(r, 0n))
      col_runs.close(cut, 1n+open, col_runs(r, 1n+x, tk, col_runs.next(cut, 1n+open)))

# min / max of a run list (min of the empty list: `lo` unchanged).
def lmin(xs: List<&2, Nat>, +lo: Nat) -> Nat:
  match xs:
    case Nil{}:
      lo
    case x <> rest:
      lmin(rest, Nat.min(lo, x))

def lmax(xs: List<&2, Nat>, +hi: Nat) -> Nat:
  match xs:
    case Nil{}:
      hi
    case x <> rest:
      lmax(rest, Nat.max(hi, x))

# Shortest / longest fp16 run (tiles) and column alignment over a grid, accumulated block by block.
type Stat is Data:
  Stat{lo: Nat, hi: Nat, al: Bool}

def stat_add(st: Stat, +rs: List<&2, Nat>, al: Bool) -> Stat:
  match st:
    case Stat{lo, hi, a}:
      Stat{lmin(rs, lo), lmax(rs, hi), Bool.and(a, al)}

# Reference: blocks b .. b + left - 1, each block's loop from its own slice_beg (block above); `al`:
# the block starts on a column boundary (if every block does, no column is shared by two blocks and no
# partial crosses blocks: reduce() is first && last, GI:840-862).
def grid_ref(left: Nat, +b: Nat, +T: Nat, +G: Nat, +tk: Nat, st: Stat) -> Stat:
  match left:
    case 0n:
      st
    case 1n+r:
      grid_ref(r, 1n+b, T, G, tk, stat_add(st, runs(block(b, T, G, tk), 0n),
        Nat.is_eq(Nat.mod(slice_beg(b, T, G), tk), 0n)))

# The same pass with block b's slice_beg handed over from block b - 1's slice_end (GI:99-100 are one
# expression at blockIdx.x = b and b - 1 + 1), so each block costs one product (law grid_stat_is_ref).
def grid_stat(left: Nat, +b: Nat, +s: Nat, +T: Nat, +G: Nat, +tk: Nat, st: Stat) -> Stat:
  match left:
    case 0n:
      st
    case 1n+r:
      +e = slice_end(b, T, G)
      grid_stat(r, 1n+b, e, T, G, tk, stat_add(st, runs(loop(Nat.sub(e, s), Nat.mod(s, tk), Nat.div(s, tk), tk), 0n),
        Nat.is_eq(Nat.mod(s, tk), 0n)))

def stat_acc(st: Stat, +fp32: Bool) -> Ord.Acc:
  match st:
    case Stat{lo, hi, al}:
      Ord.Runs{Nat.mul(16n, lo), Nat.mul(16n, hi), Bool.or(fp32, al)}

# Class of the tensor-core kernel on one (k, n) matrix, shape s, grid G: fp16 runs of 16 k-values per
# tile, from the shortest to the longest over every block; partials crossing blocks are the C dtype
# (GI:692-705 read_sum_gl, GI:724-735 write_sum_gl: fp32 when c_fp32 else __floats2half2_rn), so they
# stay fp32 iff c_fp32 or no column is split between blocks.
def gemm_acc(+k: Nat, +n: Nat, +s: Nat, +G: Nat, +fp32: Bool) -> Ord.Acc:
  +tk = tiles_k(k, s)
  +T = tiles(k, n, s)
  stat_acc(grid_stat(G, 0n, slice_beg(0n, T, G), T, G, tk, Stat{T, 0n, True{}}), fp32)

# ==== QTIP GEMV (VK) ====

# VK:143 WK (k-split warps) = CFG == 0 ? 16 : 8; VK:146 FOLD = CFG == 0 ? 4 : 2; VK:145 PF = FOLD.
def gemv_wk(+cfg: Nat) -> Nat:
  sel(Nat.is_eq(cfg, 0n), 16n, 8n)

def gemv_fold(+cfg: Nat) -> Nat:
  sel(Nat.is_eq(cfg, 0n), 4n, 2n)

# One warp's k-slice loop (VK:245-334) over i = 0 .. myn - 1 (one 16-deep k-slice MMA pair into the fp16
# accumulators ch, VK:318-319), folding into the fp32 acc0 (VK:322-333) when
# (d + 1) % FOLD == 0 || i + 1 == myn, d = i - ib = i % PF (ib steps by PF, VK:245-250).
# Event list with the same vocabulary: Tile per slice, Reduce per fold.
def gemv_loop(left: Nat, +i: Nat, +myn: Nat, +fo: Nat) -> List<&2, Ev>:
  match left:
    case 0n:
      Nil{}
    case 1n+r:
      Tile{0n, i} <> red(Bool.or(Nat.is_eq(Nat.mod(1n+Nat.mod(i, fo), fo), 0n), Nat.is_eq(1n+i, myn)), 0n,
        gemv_loop(r, 1n+i, myn, fo))

# VK:181-186 kslices = size_k / 16; chunk = ceil(kslices / WK); ks0 = warp * chunk;
# myn = max(0, min(chunk, kslices - ks0)).
def gemv_myn(+w: Nat, +k: Nat, +cfg: Nat) -> Nat:
  +ks = Nat.div(k, 16n)
  +chunk = Nat.div(Nat.sub(Nat.add(ks, gemv_wk(cfg)), 1n), gemv_wk(cfg))
  Nat.min(chunk, Nat.sub(ks, Nat.mul(w, chunk)))

def gemv_runs(+w: Nat, +k: Nat, +cfg: Nat) -> List<&2, Nat>:
  +myn = gemv_myn(w, k, cfg)
  runs(gemv_loop(myn, 0n, myn, gemv_fold(cfg)), 0n)

def gemv_lo(left: Nat, +w: Nat, +k: Nat, +cfg: Nat, +lo: Nat) -> Nat:
  match left:
    case 0n:
      lo
    case 1n+r:
      gemv_lo(r, 1n+w, k, cfg, lmin(gemv_runs(w, k, cfg), lo))

def gemv_hi(left: Nat, +w: Nat, +k: Nat, +cfg: Nat, +hi: Nat) -> Nat:
  match left:
    case 0n:
      hi
    case 1n+r:
      gemv_hi(r, 1n+w, k, cfg, lmax(gemv_runs(w, k, cfg), hi))

# GEMV class: 16 k-values per slice; the WK warp partials are summed in fp32 in shared memory
# (VK:337-370, float sh_red / float sum) inside one block per column group (VK:221), so nothing crosses
# blocks in fp16.
def gemv_acc(+k: Nat, +cfg: Nat) -> Ord.Acc:
  Ord.Runs{Nat.mul(16n, gemv_lo(gemv_wk(cfg), 0n, k, cfg, k)), Nat.mul(16n, gemv_hi(gemv_wk(cfg), 0n, k, cfg, 0n)),
    True{}}

# ==== dispatch ====

# Configs of exl3_gemv_cfg: -1 = not eligible, 0 = narrow, 1 = wide (V:44-45).
type Cfg is Data:
  NoGemv{}
  Narrow{}
  Wide{}

def cfg_pick(c: Bool, t: Cfg, f: Cfg) -> Cfg:
  match c:
    case True{}:
      t
    case False{}:
      f

# V:46-72 exl3_gemv_cfg at cc = CC_AMPERE, mode 1 (V:29-34 default), after its hard constraints
# (repeated by V:110-114). `nc` = narrow_coresident = occupancy(narrow kernel, 512) * num_sms (V:142).
def gemv_cfg(+m: Nat, +k: Nat, +n: Nat, +K: Nat, +cb: Nat, +nc: Nat) -> Cfg:
  +hard = Bool.and(Nat.is_le(2n, K), Bool.and(Nat.is_le(K, 4n),
    Bool.and(Bool.or(Nat.is_eq(K, 4n), Bool.not(Nat.is_eq(cb, 0n))),
    Bool.and(Nat.is_le(m, 8n), Bool.and(Nat.is_eq(Nat.mod(k, 128n), 0n), Nat.is_eq(Nat.mod(n, 128n), 0n))))))
  cfg_pick(Bool.not(hard), NoGemv{},
    cfg_pick(Nat.is_eq(K, 2n), cfg_pick(Nat.is_le(n, 8192n), Narrow{}, Wide{}),
    cfg_pick(Nat.is_le(Nat.div(n, 32n), nc), Narrow{},
    cfg_pick(Bool.and(Nat.is_le(k, 2048n), Nat.is_le(n, 8192n)), Narrow{},
    cfg_pick(Nat.is_eq(K, 3n), NoGemv{},
    cfg_pick(Bool.and(Nat.is_le(8192n, n), Nat.is_le(k, 4096n)), Wide{},
    cfg_pick(Bool.and(Nat.is_le(8192n, n), Bool.and(Nat.is_le(n, 10240n), Nat.is_le(k, 5120n))), Wide{},
      NoGemv{})))))))

# I8:46-51 exl3_gemv_int8_max_k: 5 on Ampere (EXL3_INT8_GEMV_MAX_K unset).
def int8_max_k() -> Nat:
  5n

# The int8 gate on the served path: G:196 mul1 && int8 enabled (I8:24-35: mode 2 by default); I8:240-241
# n % 256 == 0, k % 128 == 0; I8:245 1 <= K <= max_k; I8:254 m <= 2 (mode 2 is not residual). Whether
# the launch then succeeds (I8:127-186 sq decomposition / workspace checks, I8:260-356 m = 1 coop path) is
# a runtime outcome, the Env field i8.
def int8_gate(+m: Nat, +k: Nat, +n: Nat, +K: Nat, mul1: Bool) -> Bool:
  Bool.and(mul1, Bool.and(Nat.is_eq(Nat.mod(n, 256n), 0n), Bool.and(Nat.is_eq(Nat.mod(k, 128n), 0n),
    Bool.and(Nat.is_le(1n, K), Bool.and(Nat.is_le(K, int8_max_k()), Nat.is_le(m, 2n))))))

# Runtime outcomes the source leaves to the device: i8 = the int8 launch succeeded when its gate held;
# nc = narrow GEMV co-residency (V:142, cudaOccupancyMaxActiveBlocksPerMultiprocessor * num_sms);
# wc = the wide config's co-resident blocks (V:153). Autotuned tensor-core configs are the Tune records.
type Env is Data:
  Env{i8: Bool, nc: Nat, wc: Nat}

# A persisted autotune record: kernel shape index and grid.x (num_sms field).
type Tune is Data:
  Tune{shape: Nat, grid: Nat}

def env_i8(e: Env) -> Bool:
  match e:
    case Env{i8, nc, wc}:
      i8

def env_nc(e: Env) -> Nat:
  match e:
    case Env{i8, nc, wc}:
      nc

def env_wc(e: Env) -> Nat:
  match e:
    case Env{i8, nc, wc}:
      wc

def tune_acc(+k: Nat, +n: Nat, t: Tune, +fp32: Bool) -> Ord.Acc:
  match t:
    case Tune{shape, grid}:
      gemm_acc(k, n, shape, grid, fp32)

def acc_pick(c: Bool, t: Ord.Acc, f: Ord.Acc) -> Ord.Acc:
  match c:
    case True{}:
      t
    case False{}:
      f

# V:150-155: the GEMV launches only with grid = min(n / cols, co-resident blocks) >= 1 (cols 32 / 64).
def gemv_launch(c: Cfg, +k: Nat, +n: Nat, +nc: Nat, +wc: Nat, rest: Ord.Acc) -> Ord.Acc:
  match c:
    case NoGemv{}:
      rest
    case Narrow{}:
      acc_pick(Nat.is_le(1n, Nat.min(Nat.div(n, 32n), nc)), gemv_acc(k, 0n), rest)
    case Wide{}:
      acc_pick(Nat.is_le(1n, Nat.min(Nat.div(n, 64n), wc)), gemv_acc(k, 1n), rest)

# exl3_gemm_gr (G:137-323), cb = 2 for mul1 (G:188-190): the int8 GEMV (G:196-200), else the QTIP GEMV
# (G:234-249, has_su_sv: EXL3 linears pass suh, A_had, svh), else the autotuned tensor-core kernel
# (G:252-292, the persisted record `t`).
def gemm_gr(+m: Nat, +k: Nat, +n: Nat, +K: Nat, +mul1: Bool, +fp32: Bool, +e: Env, t: Tune) -> Ord.Acc:
  +cb = sel(mul1, 2n, 0n)
  acc_pick(Bool.and(int8_gate(m, k, n, K, mul1), env_i8(e)), Ord.Int8{},
    gemv_launch(gemv_cfg(m, k, n, K, cb, env_nc(e)), k, n, env_nc(e), env_wc(e), tune_acc(k, n, t, fp32)))

# exl3_mgemm_gr (G:400-681): no GEMV route; the autotuned exl3_mgemm_kernel runs exl3_gemm_kernel_inner
# once per matrix with the matrix's own width n_j (GK:217-236), gridDim.x slices per matrix.
def mgemm(+k: Nat, +w: Nat, +fp32: Bool, t: Tune) -> Ord.Acc:
  tune_acc(k, w, t, fp32)

# ==== callers ====

# CF:61-77 InferParams.use_mgemm with EXL3_INT8_GEMV on (CF:30-32): K_thr = exl3_gemv_int8_max_k + 1 = 6
# on Ampere (CF:70-76), n_thr = 8192: mul1 tensors fuse iff K >= K_thr or out_features < n_thr.
def use_mgemm(+K: Nat, +out: Nat, mul1: Bool) -> Bool:
  match mul1:
    case False{}:
      True{}
    case True{}:
      Bool.or(Nat.is_le(Nat.add(int8_max_k(), 1n), K), Nat.is_lt(out, 8192n))

# The target's linears (hidden 5120; attention q|gate 12288, k 1024, v 1024, o 6144 -> 5120; GDN qkv
# 10240, z 6144, out 6144 -> 5120; MLP 5120 -> 17408 -> 5120; lm_head 5120 -> 248320 at 6 bpw; every
# other linear 4 bpw mul1 -- the elpis tail and m16g routes require exactly these, 8202 patch
# exl3_tail_m16_sched.h K0/N0 and 2102 g_routes).
# Bundles: SlicedMultiLinear width = gcd(widths) (ML:86): gcd(12288, 1024, 1024) = 1024 (attention,
# modules/attn.py:505-511, C carrier fp16 attn.py:531) and gcd(10240, 6144) = 2048 (GDN,
# modules/gated_delta_net.py:717-726, C carrier fp32); called as one sliced exl3_mgemm
# (libtorch/attention.cpp:437-446, libtorch/gated_delta_net.cpp:234-242) when use_mgemm(K, width).
# Separate projections go through exl3_gemm_gr (attention.cpp:835 o_proj, gated_delta_net.cpp:321
# out_proj, mlp.cpp:72-73 gate / up when the gate/up pair is not fused (modules/mlp.py:642-645
# use_mgemm(K, out_features)), mlp.cpp:88 down).
# Output dtype (fp32 flag) of o_proj / out_proj / down (True) and gate / up / lm_head (False): taken from
# the untracked analyze_a.py:35-47 of the decode-accuracy work, UNVERIFIED here; no law depends on them
# (elpis keeps fp32 partials, and lm_head is the same kernel on both sides).
# lm_head mul1: UNVERIFIED; irrelevant at K = 6 (int8_gate needs K <= 5, gemv_cfg needs K <= 4).
type Op is Data:
  AttnQG{}
  AttnK{}
  AttnV{}
  AttnO{}
  GdnQkv{}
  GdnZ{}
  GdnOut{}
  MlpGate{}
  MlpUp{}
  MlpDown{}
  LmHead{}

# Persisted stock autotune records (the served containers' coop_autotune_v1.bin, decoded by
# the untracked tunecache.py of the decode-accuracy work; per partA.md = bend/gen/precision_parta.txt
# the record is the same for every m = 1 .. 8):
#   attention sliced bundle (k 5120, slice 1024, fp16 C): shape 4, grid 4 (x z 14)   partA.md:3-26
#   GDN sliced bundle (k 5120, slice 2048, fp32 C):      shape 4, grid 10 (x z 8)    partA.md:35-50
#   MLP gate / up (5120 -> 17408, m >= 2 key):           shape 4, grid 82            partA.md:61-74
#   lm_head (5120 -> 248320, K 6):                       shape 4, grid 82            partA.md:83-90
# o_proj / out_proj / down have no record (never tuned: the GEMV takes them); `fb` is any (shape, grid)
# the runtime autotuner might pick for them. The gate / up and lm_head records are passed as values
# (tunes below) so that laws can bind them through equations on variables: the checker's Nat is unary and
# normalizes closed terms (bend/gemm_m16_wpart.bend:96-98), and lm_head's slice products (155200 tiles x
# 81) exhaust its stack.
type Tunes is Data:
  Tunes{qkv: Tune, gdn: Tune, gu: Tune, head: Tune, fb: Tune}

def gu_shape() -> Nat:
  4n

def gu_grid() -> Nat:
  82n

def head_shape() -> Nat:
  4n

def head_grid() -> Nat:
  82n

# The record set with gate / up = Tune{gs, gg} and lm_head = Tune{hs, hg}; the persisted one is
# tunes(gu_shape(), gu_grid(), head_shape(), head_grid(), fb).
def tunes(+gs: Nat, +gg: Nat, +hs: Nat, +hg: Nat, fb: Tune) -> Tunes:
  Tunes{Tune{4n, 4n}, Tune{4n, 10n}, Tune{gs, gg}, Tune{hs, hg}, fb}

def tune.of(ts: Tunes, op: Op) -> Tune:
  match ts:
    case Tunes{qkv, gdn, gu, head, fb}:
      match op:
        case AttnQG{}:
          qkv
        case AttnK{}:
          qkv
        case AttnV{}:
          qkv
        case GdnQkv{}:
          gdn
        case GdnZ{}:
          gdn
        case MlpGate{}:
          gu
        case MlpUp{}:
          gu
        case LmHead{}:
          head
        case AttnO{}:
          fb
        case GdnOut{}:
          fb
        case MlpDown{}:
          fb

def tune(op: Op, ts: Tunes) -> Tune:
  tune.of(ts, op)

def bundle(+K: Nat, +k: Nat, +w: Nat, +n: Nat, +fp32: Bool, +m: Nat, +e: Env, +t: Tune) -> Ord.Acc:
  acc_pick(use_mgemm(K, w, True{}), mgemm(k, w, fp32, t), gemm_gr(m, k, n, K, True{}, fp32, e, t))

# The stock class of every served (op, m) under runtime outcomes e and autotune records ts.
def acc(op: Op, +m: Nat, +e: Env, +ts: Tunes) -> Ord.Acc:
  match op:
    case AttnQG{}:
      bundle(4n, 5120n, 1024n, 12288n, False{}, m, e, tune(AttnQG{}, ts))
    case AttnK{}:
      bundle(4n, 5120n, 1024n, 1024n, False{}, m, e, tune(AttnK{}, ts))
    case AttnV{}:
      bundle(4n, 5120n, 1024n, 1024n, False{}, m, e, tune(AttnV{}, ts))
    case GdnQkv{}:
      bundle(4n, 5120n, 2048n, 10240n, True{}, m, e, tune(GdnQkv{}, ts))
    case GdnZ{}:
      bundle(4n, 5120n, 2048n, 6144n, True{}, m, e, tune(GdnZ{}, ts))
    case AttnO{}:
      gemm_gr(m, 6144n, 5120n, 4n, True{}, True{}, e, tune(AttnO{}, ts))
    case GdnOut{}:
      gemm_gr(m, 6144n, 5120n, 4n, True{}, True{}, e, tune(GdnOut{}, ts))
    case MlpGate{}:
      acc_pick(use_mgemm(4n, 17408n, True{}), mgemm(5120n, 17408n, False{}, tune(MlpGate{}, ts)),
        gemm_gr(m, 5120n, 17408n, 4n, True{}, False{}, e, tune(MlpGate{}, ts)))
    case MlpUp{}:
      acc_pick(use_mgemm(4n, 17408n, True{}), mgemm(5120n, 17408n, False{}, tune(MlpUp{}, ts)),
        gemm_gr(m, 5120n, 17408n, 4n, True{}, False{}, e, tune(MlpUp{}, ts)))
    case MlpDown{}:
      gemm_gr(m, 17408n, 5120n, 4n, True{}, True{}, e, tune(MlpDown{}, ts))
    case LmHead{}:
      gemm_gr(m, 5120n, 248320n, 6n, False{}, False{}, e, tune(LmHead{}, ts))

# The served runtime outcomes: int8 launches succeed (the sq decomposition passes its caps at these
# shapes, I8:135-186 -- arithmetic in the report, not proven here) and the narrow GEMV has 2 blocks /
# SM x 82 = 164 co-resident (64 registers, cuobjdump; partA.json gemv_narrow_coresident = 164);
# wide co-residency is never consulted at the served shapes (law gemv_never_wide).
def served_env() -> Env:
  Env{True{}, 164n, 0n}

def is_wide(c: Cfg) -> Bool:
  match c:
    case NoGemv{}:
      False{}
    case Narrow{}:
      False{}
    case Wide{}:
      True{}
