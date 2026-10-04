# The served verify head (final RMSNorm -> stock lm_head exl3_gemm_gr -> fused greedy argmax) as a
# per-row SCHEDULE (plan), over Nat. Source: stock ExLlamaV3 355c6ee (r0b0tlab/exllamav3), files not
# touched by any patch of patches/exl3-ext/series (the only patch touching exl3_gemm.cu /
# coop_autotune.cu / exl3_gemv.cu / exl3_kernel_map.cu, 1001-gemm-fused-gate-up-silu, is not in the
# series). Line references (paths under exllamav3/exllamav3_ext/):
#   G:  quant/exl3_gemm.cu        GI: quant/exl3_gemm_inner.cuh   GK: quant/exl3_gemm_kernel.cuh
#   KM: quant/exl3_kernel_map.cuh KC: quant/exl3_kernel_map.cu    CA: quant/coop_autotune.cu
#   V:  quant/exl3_gemv.cu        I8: quant/exl3_gemv_int8.cu     SF: generator/sampling_fused.cu
#   SH: generator/sampling_fused.cuh
# What is modelled: which kernel / (shape, grid) runs for an m-row call (dispatch + persisted autotune
# records passed as VALUES), and, for the tensor-core kernel, the per-output-element reduction order
# of element (row r, column tile nt): each block's k-tiles and fold points in that column (the event
# lists of bend/precision_stock.bend, precision-law 1a2733d, lines 20-91, copied unchanged), the
# order in which block partials meet (lock order), the in-block sub_k combine tree, whether the row
# is written, and its M tile. Float VALUES are not modelled: the plan is what fixes the arithmetic.
# Not modelled (named in the laws / proposal): the m16n8k16 MMA computing row r from A row r, B and
# C row r only, in a row-independent internal order (hardware); the lane / register slot of an
# element (GI:808-811, 359, 389 treat the four accumulator slots identically); the input / output
# Hadamard warps (GK:16-30, 55-75: one warp per 128-chunk of one row, the same code for every chunk).
import Base
import ./norm_fuse_spec.bend as NSpec

def sel(c: Bool, t: Nat, f: Nat) -> Nat:
  match c:
    case True{}:
      t
    case False{}:
      f

# ==== shape tables (KM:67-70) ====

# KM:67 EXL3_GEMM_TILESIZE_M  0, 16, 16, 16, 16, 32, 64
def tilesize_m(+s: Nat) -> Nat:
  sel(Nat.is_eq(s, 5n), 32n, sel(Nat.is_eq(s, 6n), 64n, 16n))

# KM:68 EXL3_GEMM_TILESIZE_K  0, 16, 32, 32, 16, 32, 32
def tilesize_k(+s: Nat) -> Nat:
  sel(Bool.or(Nat.is_eq(s, 1n), Nat.is_eq(s, 4n)), 16n, 32n)

# KM:69 EXL3_GEMM_TILESIZE_N  0, 128, 128, 256, 512, 256, 128
def tilesize_n(+s: Nat) -> Nat:
  sel(Nat.is_eq(s, 4n), 512n, sel(Bool.or(Nat.is_eq(s, 3n), Nat.is_eq(s, 5n)), 256n, 128n))

# GI:47 TILEBLOCKS_K = TILESIZE_K / 16 (sub_k groups of a block)
def tbk(+s: Nat) -> Nat:
  Nat.div(tilesize_k(s), 16n)

# ==== dispatch of exl3_gemm_gr (G:124-323) for an m-row call, m <= 16 ====

# G:40-50 roundup_pow2 and G:58-60 gemm_autotune_m_key: size_m <= 16 -> MIN(roundup_pow2(size_m), 16)
def m_key(+m: Nat) -> Nat:
  sel(Nat.is_le(m, 1n), 1n, sel(Nat.is_le(m, 2n), 2n, sel(Nat.is_le(m, 4n), 4n, sel(Nat.is_le(m, 8n), 8n, 16n))))

# G:255 autotune_key = gemm_autotune_hash(MAX(size_m, 2), size_k, size_n, K, c_fp32, device, cc,
# num_sms, cb): for a fixed matrix and device only the m bucket varies with m.
def key(+m: Nat) -> Nat:
  m_key(Nat.max(m, 2n))

# A persisted record (CA:205-262 DiskCacheRecordV1: tag = shape_idx, num_sms = grid; block_dim and
# concurrency are checked below) or none.
type Rec is Data:
  Hit{tag: Nat, grid: Nat}
  Miss{}

type Entry is Data:
  Entry{key: Nat, rec: Rec}

def lookup.pick(c: Bool, a: Rec, b: Rec) -> Rec:
  match c:
    case True{}:
      a
    case False{}:
      b

# CA:215 disk_cache.find(hash): the record of a key, Miss if absent (keys are unique in the file).
def lookup(tab: List<&2, Entry>, +k: Nat) -> Rec:
  match tab:
    case Nil{}:
      Miss{}
    case e <> rest:
      match e:
        case Entry{+ek, r}:
          lookup.pick(Nat.is_eq(ek, k), r, lookup(rest, k))

# The persisted records of the lm_head matrix (size_k 5120, size_n 248320, K 6, fp16 C, device 0,
# CC_AMPERE, 82 SMs, cb 2) in coop_autotune_v1.bin (sha256 bf27ff75f0d3fe09...c0e3, 78 unique
# records; decoded by the untracked tunecache.py of the decode-accuracy work): record #66 (m key 2), #67 (key 4),
# #11 (key 8), #73 (key 16), each tag 4, block_dim 256, num_sms 82, concurrency 1.
def served_tab() -> List<&2, Entry>:
  [Entry{2n, Hit{4n, 82n}}, Entry{4n, Hit{4n, 82n}}, Entry{8n, Hit{4n, 82n}}, Entry{16n, Hit{4n, 82n}}]

# CA:231-240 launch_from_disk_cache accepts a record iff a candidate has its tag and block_dim,
# num_sms <= max_num_sms and the expected concurrency. Candidates (G:264-285): every shape with
# exl3_gemm_shape_compat (KC:98-108: TILESIZE_M > 16 needs size_m >= TILESIZE_M; size_k % TILESIZE_K
# and size_n % TILESIZE_N, not m), block_dim / max_num_sms from the shape table and num_sms (not m).
# So the only m-dependent acceptance condition is the TILESIZE_M one; the others are properties of
# the record and the matrix (true for the served records: 5120 % 16 = 248320 % 512 = 0, 82 <=
# MIN(155200, 82), concurrency MAX(MIN(82 / 82, 1), 1) = 1).
def accept(+tag: Nat, +m: Nat) -> Bool:
  Bool.or(Nat.is_le(tilesize_m(tag), 16n), Nat.is_le(tilesize_m(tag), m))

# Launch of one call: the cooperative tensor-core kernel on a (shape, grid); runtime autotune of a
# key (CA:656-661: a timing-dependent choice, persisted per key; not modelled beyond its key); a
# non-cooperative route (GEMV / int8 GEMV), not modelled here.
type Launch is Data:
  Coop{s: Nat, G: Nat}
  Tune{k: Nat}
  Other{}

def launch_pick(c: Bool, +tag: Nat, +G: Nat, +k: Nat) -> Launch:
  match c:
    case True{}:
      Coop{tag, G}
    case False{}:
      Tune{k}

def launch_of(r: Rec, +m: Nat) -> Launch:
  match r:
    case Hit{+tag, +G}:
      launch_pick(accept(tag, m), tag, G, key(m))
    case Miss{}:
      Tune{key(m)}

def dispatch.pick(coop: Bool, tab: List<&2, Entry>, +m: Nat) -> Launch:
  match coop:
    case True{}:
      launch_of(lookup(tab, key(m)), m)
    case False{}:
      Other{}

# G:196-200 int8 GEMV (mul1) declines for K > exl3_gemv_int8_max_k = 5 on CC_AMPERE (I8:46-51,
# I8:245, default env); G:236-250 exl3_gemv_try_launch declines for K < 2 || K > 4 (V:111). For
# K > 5 the call is the cooperative kernel (G:252-291) for every m; for K <= 5 other gates (m, cb,
# env) decide, which this model does not transcribe (Other).
def dispatch(tab: List<&2, Entry>, +K: Nat, +m: Nat) -> Launch:
  dispatch.pick(Nat.is_lt(5n, K), tab, m)

# ==== tensor-core kernel: slice partition and fold schedule (precision_stock.bend:39-91) ====

# GI:91-92 tiles_k = size_k / TILESIZE_K, tiles_n = size_n / TILESIZE_N; slice space tiles_k * tiles_n,
# column-major (k fastest): GI:105-106 index_k = i % tiles_k, index_n = i / tiles_k.
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

# Tile = one k-tile MMA into the fp16 accumulators (GI:884-896); Reduce = reduce(): fold the fp16
# accumulators into fp32 (GI:801-827), sub_k combine (GI:830), cross-block exchange (GI:834-871).
type Ev is Data:
  Tile{n: Nat, k: Nat}
  Reduce{n: Nat}

def red(c: Bool, +n: Nat, rest: List<&2, Ev>) -> List<&2, Ev>:
  match c:
    case True{}:
      Reduce{n} <> rest
    case False{}:
      rest

# The main loop (GI:929-945): matmul; if (slice2_k == tiles_k - 1 || slice2_iters == 1) reduce();
# advance2 (GI:223-232): slice2_k++; slice2_iters--; if (slice2_k >= tiles_k) { slice2_k = 0; slice2_n++; }
def loop(+iters: Nat, +k: Nat, +n: Nat, +tk: Nat) -> List<&2, Ev>:
  match iters:
    case 0n:
      Nil{}
    case 1n+r:
      +wrap = Nat.is_le(tk, 1n+k)
      Tile{n, k} <> red(Bool.or(Nat.is_eq(k, Nat.sub(tk, 1n)), Nat.is_eq(1n+r, 1n)), n,
        loop(r, sel(wrap, 0n, 1n+k), sel(wrap, 1n+n, n), tk))

# Block b's loop from slice_beg (GI:114-116), nothing when slice_len < 1 (GI:102).
def block(+b: Nat, +T: Nat, +G: Nat, +tk: Nat) -> List<&2, Ev>:
  +s = slice_beg(b, T, G)
  loop(Nat.sub(slice_end(b, T, G), s), Nat.mod(s, tk), Nat.div(s, tk), tk)

# ==== per-element reduction order ====

def only_col.keep(c: Bool, ev: Ev, rest: List<&2, Ev>) -> List<&2, Ev>:
  match c:
    case True{}:
      ev <> rest
    case False{}:
      rest

# The events of one block that touch output column tile nt (its k-tiles there and its fold points).
def only_col(evs: List<&2, Ev>, +nt: Nat) -> List<&2, Ev>:
  match evs:
    case Nil{}:
      Nil{}
    case ev <> rest:
      match ev:
        case Tile{+en, +ek}:
          only_col.keep(Nat.is_eq(en, nt), Tile{en, ek}, only_col(rest, nt))
        case Reduce{+en}:
          only_col.keep(Nat.is_eq(en, nt), Reduce{en}, only_col(rest, nt))

def push(xs: List<&2, Ev>, acc: List<&2, List<&2, Ev>>) -> List<&2, List<&2, Ev>>:
  match xs:
    case Nil{}:
      acc
    case x <> rest:
      (x <> rest) <> acc

# The blocks' segments of column tile nt in lock order. reduce() (GI:834-841, 871): lock_i =
# tiles_k - slice2_k - 1 (slice2_k = the segment's last k), barrier_acquire(lock, lock_i), then
# barrier_release(lock, lock_d = segment length): the segment ending at k = tiles_k - 1 (highest
# block) goes first (first = lock_i == 0 writes its partial, GI:850-853), each later one reads the
# running partial back (GI:844-847), the lowest block is last (GI:856-862). Blocks b = 0 .. G - 1 are
# visited in ascending order and prepended, so the list is in descending block = lock order.
def col_segs(left: Nat, +b: Nat, +T: Nat, +G: Nat, +tk: Nat, +nt: Nat,
    acc: List<&2, List<&2, Ev>>) -> List<&2, List<&2, Ev>>:
  match left:
    case 0n:
      acc
    case 1n+r:
      col_segs(r, 1n+b, T, G, tk, nt, push(only_col(block(b, T, G, tk), nt), acc))

# In-block sub_k combine of one accumulator element (threadblock_reduce, GI:346-527): Leaf i =
# sub_k group i's partial, Add{a, b} = `a += b` (the stored value b added into the adder's a).
type Tree is Data:
  Leaf{i: Nat}
  Add{a: Tree, b: Tree}

# Full path (GI:503-525): TILEBLOCKS_K 2: store(1) add(0); 3: store(1) add(0) store(2) add(0);
# 4: store(3) add(2) store(1) add(0) store(2) add(0). 1: no combine.
def tsel(c: Bool, a: Tree, b: Tree) -> Tree:
  match c:
    case True{}:
      a
    case False{}:
      b

def tb_full(+t: Nat) -> Tree:
  tsel(Nat.is_eq(t, 2n), Add{Leaf{0n}, Leaf{1n}},
    tsel(Nat.is_eq(t, 3n), Add{Add{Leaf{0n}, Leaf{1n}}, Leaf{2n}},
      tsel(Nat.is_eq(t, 4n), Add{Add{Leaf{0n}, Leaf{1n}}, Add{Leaf{2n}, Leaf{3n}}}, Leaf{0n})))

# Small path (GI:479-501, size_m <= 8): the same store / add sequence, but store_small / add_small
# (GI:407-477) move only slots [0], [1] (row lane_id / 4) and only in lanes with lane_id / 4 <
# size_m. With size_m <= 8 a row r < 16 is combined iff r < size_m (rows 8..15 are slots [2], [3],
# never rows of a size_m <= 8 call); an uncombined element keeps its own partial.
def tb_small(+t: Nat, part: Bool) -> Tree:
  match part:
    case True{}:
      tb_full(t)
    case False{}:
      Leaf{0n}

def tb_pick(small: Bool, +t: Nat, part: Bool) -> Tree:
  match small:
    case True{}:
      tb_small(t, part)
    case False{}:
      tb_full(t)

# GI:479 `if (size_m <= 8)` picks the path; size_m = MIN(size_m_, TILESIZE_M) (GK:41) = m for m <= 16.
def tb_elem(+t: Nat, +m: Nat, +r: Nat) -> Tree:
  tb_pick(Nat.is_le(m, 8n), t, Nat.is_lt(r, m))

def tb_of(l: Launch, +m: Nat, +r: Nat) -> Tree:
  match l:
    case Coop{+s, +G}:
      tb_elem(tbk(s), m, r)
    case Tune{k}:
      Leaf{0n}
    case Other{}:
      Leaf{0n}

# Row r of an m-row call: its launch, its sub_k combine, whether it is written (GI:537-548, 628-647,
# 719-737: rows r0 / r1 < size_m), whether it lies in the first M tile of 16 rows (GK:37-50: the
# while loop runs tiles of TILESIZE_M rows; for every shape the dispatch admits at m <= 16,
# TILESIZE_M = 16 by accept).
type RowSched is Data:
  RowSched{launch: Launch, tb: Tree, wr: Bool, tile0: Bool}

def row_sched(tab: List<&2, Entry>, +K: Nat, +m: Nat, +r: Nat) -> RowSched:
  +l = dispatch(tab, K, m)
  RowSched{l, tb_of(l, m, r), Nat.is_lt(r, m), Nat.is_lt(r, 16n)}

# The reduction order of element (row r, column tile nt) of a size_k x size_n matrix: the blocks'
# segments in lock order (fp16 runs between fold points inside each), the sub_k tree, the row flags.
type Order is Data:
  Order{segs: List<&2, List<&2, Ev>>, tb: Tree, wr: Bool, tile0: Bool}

def segs_of(l: Launch, +k: Nat, +n: Nat, +nt: Nat) -> List<&2, List<&2, Ev>>:
  match l:
    case Coop{+s, +G}:
      col_segs(G, 0n, tiles(k, n, s), G, tiles_k(k, s), nt, Nil{})
    case Tune{kk}:
      Nil{}
    case Other{}:
      Nil{}

def order_of(rs: RowSched, +k: Nat, +n: Nat, +nt: Nat) -> Order:
  match rs:
    case RowSched{l, t, w, z}:
      Order{segs_of(l, k, n, nt), t, w, z}

# Element order of row r of an m-row call on a FIXED record (shape s, grid G), i.e. the Coop launch.
def order(+s: Nat, +G: Nat, +k: Nat, +n: Nat, +m: Nat, +r: Nat, +nt: Nat) -> Order:
  order_of(RowSched{Coop{s, G}, tb_elem(tbk(s), m, r), Nat.is_lt(r, m), Nat.is_lt(r, 16n)}, k, n, nt)

# Element order of row r of an m-row call through the dispatch (records passed as values).
def elem_order(tab: List<&2, Entry>, +K: Nat, +k: Nat, +n: Nat, +m: Nat, +r: Nat, +nt: Nat) -> Order:
  order_of(row_sched(tab, K, m, r), k, n, nt)

# ==== the head plan of a row ====

# SF:839 num_blocks = MIN(CEIL_DIVIDE(size, FS_THREADS * 4), FUSED_SAMPLER_MAX_BLOCKS), FS_THREADS
# 256 (SF:37), FUSED_SAMPLER_MAX_BLOCKS 128 (SH:5): the block split of every row (grid.y = row,
# SF:861, 667) from the vocabulary bound only.
def fs_blocks(+size: Nat) -> Nat:
  Nat.min(Nat.div(Nat.add(size, 1023n), 1024n), 128n)

# Head plan of row r (logical depth d) of an m-row verify launch whose row 0 sits at base: the final
# norm's launch shape (norm_fuse: one block per row, blockDim 32 W with W = warps_for(dim / 4)), the
# row's lm_head schedule, the argmax block split. No positional input enters the head.
type HeadPlan is Data:
  HeadPlan{norm_w: Nat, gemm: RowSched, am_blocks: Nat}

def hp_head(tab: List<&2, Entry>, +K: Nat, +dim: Nat, +size: Nat, +base: Nat, +m: Nat, +r: Nat,
    +d: Nat) -> HeadPlan:
  HeadPlan{NSpec.warps_for(Nat.div(dim, 4n)), row_sched(tab, K, m, r), fs_blocks(size)}
