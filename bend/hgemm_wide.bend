# Wide-tile prefill GEMM of ext patch 3011 (3011-hgemm-f16acc-wide.patch), transcribed from the CUDA
# integer expressions over Nat (W: = exllamav3_ext/hgemm_f16acc_wide.cuh, H: = exllamav3_ext/hgemm_f16acc.cu,
# both post-patch; S: = the served f16acc::gemm_kernel, hgemm_f16acc.cu). The shipped configuration is
# H: using Wide = f16acc_wide::Cfg<128, 128, 32, 2, 2, 3,  8, 2>;  i.e. BM = BN = 128, BK = 32, WARPS_M =
# WARPS_N = 2 (THREADS = 128, WM = WN = 64, MT = 4, NT = 8, A_CPR = 4, B_CPR = 16), GROUP_M = 8.
# C `>> k` / `& (2^k - 1)` on these non-negative values are Nat.div / Nat.mod by 2^k; `x ^ k` of the swizzle
# is `xor` below (bitwise, on the bits it touches). C int arithmetic is Nat arithmetic while no value
# overflows (the host passes M, N, K < 2^31 and the grid sizes it launched). The group size GROUP_M is kept a
# parameter G (the kernel passes 8). Reference: hgemm_wide_spec.bend; laws: hgemm_wide_laws.bend.
import Base
import ./hgemm_wide_spec.bend as Spec

# ==== raster (W: lines 91-99) ====

# W: const int bid = blockIdx.y * grid_n + blockIdx.x;
def bid(+by: Nat, +bx: Nat, +gn: Nat) -> Nat:
  Nat.add(Nat.mul(by, gn), bx)

# W: const int group_size = GROUP_M * grid_n;  const int group = bid / group_size;
def group(+b: Nat, +G: Nat, +gn: Nat) -> Nat:
  Nat.div(b, Nat.mul(G, gn))

# W: const int first_m = group * GROUP_M;
def first_m(+b: Nat, +G: Nat, +gn: Nat) -> Nat:
  Nat.mul(group(b, G, gn), G)

# W: const int gm_eff = min(GROUP_M, grid_m - first_m);
def gm_eff(+b: Nat, +G: Nat, +gn: Nat, +gm: Nat) -> Nat:
  Nat.min(G, Nat.sub(gm, first_m(b, G, gn)))

# W: const int in_group = bid - group * group_size;
def in_group(+b: Nat, +G: Nat, +gn: Nat) -> Nat:
  Nat.sub(b, Nat.mul(group(b, G, gn), Nat.mul(G, gn)))

# W: const int bm = (first_m + in_group % gm_eff) * BM;   (tile_m = bm / BM)
def tile_m(+b: Nat, +G: Nat, +gn: Nat, +gm: Nat) -> Nat:
  Nat.add(first_m(b, G, gn), Nat.mod(in_group(b, G, gn), gm_eff(b, G, gn, gm)))

# W: const int bn = (in_group / gm_eff) * BN;             (tile_n = bn / BN)
def tile_n(+b: Nat, +G: Nat, +gn: Nat, +gm: Nat) -> Nat:
  Nat.div(in_group(b, G, gn), gm_eff(b, G, gn, gm))

# H: dim3 grid(N / Wide::BN, (M + Wide::BM - 1) / Wide::BM, 1);
def grid_n(+N: Nat) -> Nat:
  Nat.div(N, 128n)

def grid_m(+M: Nat) -> Nat:
  Nat.div(Nat.sub(Nat.add(M, 128n), 1n), 128n)

# ==== thread decomposition and the epilogue store map (W: lines 101-102, 195-206) ====

# W: const int tid = threadIdx.x, warp = tid >> 5, lane = tid & 31;
def warp(+tid: Nat) -> Nat:
  Nat.div(tid, 32n)

def lane(+tid: Nat) -> Nat:
  Nat.mod(tid, 32n)

# W: const int wm = warp / WARPS_N, wn = warp % WARPS_N;
def wm(+tid: Nat) -> Nat:
  Nat.div(warp(tid), 2n)

def wn(+tid: Nat) -> Nat:
  Nat.mod(warp(tid), 2n)

# W: const int g = lane >> 2, t = lane & 3;
def gq(+tid: Nat) -> Nat:
  Nat.div(lane(tid), 4n)

def tq(+tid: Nat) -> Nat:
  Nat.mod(lane(tid), 4n)

# W: int row = bm + wm * WM + i * 16 + g + h * 8;   (C evaluates + left to right)
def row_of(+bm: Nat, +tid: Nat, +i: Nat, +h: Nat) -> Nat:
  Nat.add(Nat.add(Nat.add(Nat.add(bm, Nat.mul(wm(tid), 64n)), Nat.mul(i, 16n)), gq(tid)), Nat.mul(h, 8n))

# W: int col = bn + wn * WN + j * 8 + t * 2;  the pair store writes col + e, e < 2 (float2 / half2).
def col_of(+bn: Nat, +tid: Nat, +j: Nat, +e: Nat) -> Nat:
  Nat.add(Nat.add(Nat.add(Nat.add(bn, Nat.mul(wn(tid), 64n)), Nat.mul(j, 8n)), Nat.mul(tq(tid), 2n)), e)

# The element a thread tuple (block (by, bx), thread tid, fragment i < MT, j < NT, h < 2, pair element e < 2)
# stores, in a launch over grid (gn, gm) with row bound M.
def grow(+by: Nat, +bx: Nat, +tid: Nat, +i: Nat, +h: Nat, +G: Nat, +gn: Nat, +gm: Nat) -> Nat:
  row_of(Nat.mul(tile_m(bid(by, bx, gn), G, gn, gm), 128n), tid, i, h)

def gcol(+by: Nat, +bx: Nat, +tid: Nat, +j: Nat, +e: Nat, +G: Nat, +gn: Nat, +gm: Nat) -> Nat:
  col_of(Nat.mul(tile_n(bid(by, bx, gn), G, gn, gm), 128n), tid, j, e)

# W: if (row >= M) continue;   the store happens iff row < M.
def stored(+by: Nat, +bx: Nat, +tid: Nat, +i: Nat, +h: Nat, +G: Nat, +gn: Nat, +gm: Nat, +M: Nat) -> Bool:
  Nat.is_lt(grow(by, bx, tid, i, h, G, gn, gm), M)

# ==== cp.async stage writes (W: lines 62-74, 110-126); `^` is Spec.xor on the bits it touches ====

# W: int c = tid + i * THREADS;  (THREADS = 128)
def ld_c(+tid: Nat, +i: Nat) -> Nat:
  Nat.add(tid, Nat.mul(i, 128n))

# W: int row = c / A_CPR, chunk = c % A_CPR;  a_off: pc = chunk ^ ((row >> 1) & 3); return row * BK + pc * 8;
def a_pc(+row: Nat, +chunk: Nat) -> Nat:
  Spec.xor(2n, chunk, Nat.mod(Nat.div(row, 2n), 4n))

def a_dest(+tid: Nat, +i: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div(ld_c(tid, i), 4n), 32n), Nat.mul(a_pc(Nat.div(ld_c(tid, i), 4n), Nat.mod(ld_c(tid, i), 4n)), 8n))

# W: int row = c / B_CPR, chunk = c % B_CPR;  b_off: return row * BN + (chunk ^ (row & 7)) * 8;
def b_pc(+row: Nat, +chunk: Nat) -> Nat:
  Spec.xor(4n, chunk, Nat.mod(row, 8n))

def b_dest(+tid: Nat, +i: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div(ld_c(tid, i), 16n), 128n), Nat.mul(b_pc(Nat.div(ld_c(tid, i), 16n), Nat.mod(ld_c(tid, i), 16n)), 8n))

# ==== per-element accumulation order (W: lines 129-134, 147-192; S: gemm_kernel, untuned branch) ====

# A fp16-accumulator partial is the list of k offsets of the m16n8k16 MMAs issued into it since it was +0,
# in order; the fp32 accumulator of an output element is the list of the partials added into it, in order.

# W: for (int kk = 0; kk < BK / 16; kk += 2) { uint32_t h[2] = {0u, 0u}; mma_h(h, af[0][i], bf[0][j]);
#    mma_h(h, af[1][i], bf[1][j]); acc += h; }   with fragments s = 0, 1 of k16 step kk + s, i.e. k offset
#    kt * BK + (kk + s) * 16 (W: lines 165-169: (kk + s) * 2 + a_ch counts 8-wide chunks). `left` counts the
#    remaining kk iterations.
def wide_kk(left: Nat, +kt: Nat, +kk: Nat) -> List<&2, List<&2, Nat>>:
  match left:
    case 0n:
      Nil{}
    case 1n+rest:
      [Nat.add(Nat.mul(kt, 32n), Nat.mul(kk, 16n)), Nat.add(Nat.mul(kt, 32n), Nat.mul(Nat.add(kk, 1n), 16n))] <>
      wide_kk(rest, kt, Nat.add(kk, 2n))

# W: const int KT = K / BK;  for (int kt = 0; kt < KT; ++kt): BK / 16 / 2 = 1 kk iteration per k tile.
def wide_kt(left: Nat, +kt: Nat) -> List<&2, List<&2, Nat>>:
  match left:
    case 0n:
      Nil{}
    case 1n+rest:
      List.append(&2, List<&2, Nat>, wide_kk(1n, kt, 0n), wide_kt(rest, 1n+kt))

def wide_acc(+K: Nat) -> List<&2, List<&2, Nat>>:
  wide_kt(Nat.div(K, 32n), 0n)

# S (untuned layout, BK = 64, KK = 4): hacc starts at 0; for (kt = 0; kt < KT; ++kt) { for (kk = 0;
#    kk < KK; ++kk) { mma_f16(hacc, k16 step kk: k offset kt * BK + kk * 16); if (kk & 1) flush(); } }
#    where flush adds hacc to acc and sets it to 0. `tiles` counts the k tiles left including the current one,
#    `kks` the kk iterations left in it; `odd` is kk & 1 (kk restarts at 0 in every tile); hacc is threaded
#    through both loops.
def served_loop(+tiles: Nat, kks: Nat, odd: Bool, +kt: Nat, +kk: Nat, hacc: List<&2, Nat>)
  -> List<&2, List<&2, Nat>>:
  match tiles:
    case 0n:
      Nil{}
    case 1n+t:
      match kks:
        case 0n:
          served_loop(t, 4n, False{}, 1n+kt, 0n, hacc)
        case 1n+r:
          match odd:
            case True{}:
              List.append(&2, Nat, hacc, [Nat.add(Nat.mul(kt, 64n), Nat.mul(kk, 16n))]) <>
              served_loop(tiles, r, False{}, kt, Nat.add(kk, 1n), Nil{})
            case False{}:
              served_loop(tiles, r, True{}, kt, Nat.add(kk, 1n),
                List.append(&2, Nat, hacc, [Nat.add(Nat.mul(kt, 64n), Nat.mul(kk, 16n))]))

# S: const int KT = K / BK;  (BK = 64)
def served_acc(+K: Nat) -> List<&2, List<&2, Nat>>:
  served_loop(Nat.div(K, 64n), 4n, False{}, 0n, 0n, Nil{})

# ==== route (H: wide_shapes, wide_enabled, wide_route, launch) ====

# H: static constexpr WideShape wide_shapes[] = { {K, N, out_f32}, ... };
def wide_shapes() -> List<&2, Spec.HwShape>:
  Spec.HwShape{5120, 1024, False{}} <>
  Spec.HwShape{5120, 6144, True{}} <>
  Spec.HwShape{5120, 10240, True{}} <>
  Spec.HwShape{5120, 12288, False{}} <>
  Spec.HwShape{5120, 17408, False{}} <>
  Spec.HwShape{6144, 5120, True{}} <>
  Spec.HwShape{17408, 5120, True{}} <>
  Spec.HwShape{25600, 5120, False{}} <>
  Nil{}

# H: for (const WideShape& s : wide_shapes) if (s.K == K && s.N == N && s.out_f32 == out_f32) return true;
def shape_in(xs: List<&2, Spec.HwShape>, +K: U32, +N: U32, +f: Bool) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Spec.HwShape{k, n, g} <> rest:
      Bool.or(Bool.and(U32.is_eq(k, K), Bool.and(U32.is_eq(n, N), Bool.not(Bool.xor(g, f)))), shape_in(rest, K, N, f))

# H: wide_route after wide_enabled() returned true: device (major, minor) == (8, 6); a.dim() == 3 &&
# a.size(0) != 1 -> false; M < 1024 -> false; then the table. Each `return false` is a Served launch.
def route_on(on_device: Bool, unbatched: Bool, long: Bool, hit: Bool) -> Spec.HwRoute:
  match on_device:
    case False{}:
      Spec.HwServed{}
    case True{}:
      match unbatched:
        case False{}:
          Spec.HwServed{}
        case True{}:
          match long:
            case False{}:
              Spec.HwServed{}
            case True{}:
              match hit:
                case False{}:
                  Spec.HwServed{}
                case True{}:
                  Spec.HwWide{}

# H: wide_enabled(): unset or "1" -> true; "0" -> false (-> launch_config); anything else -> TORCH_CHECK error.
def route(env: Spec.HwEnv, +major: U32, +minor: U32, +batch: U32, +M: U32, +K: U32, +N: U32, +f: Bool) -> Spec.HwRoute:
  match env:
    case Spec.HwOther{}:
      Spec.HwError{}
    case Spec.HwZero{}:
      Spec.HwServed{}
    case Spec.HwUnset{}:
      route_on(Bool.and(U32.is_eq(major, 8), U32.is_eq(minor, 6)), U32.is_eq(batch, 1), U32.is_ge(M, 1024),
        shape_in(wide_shapes(), K, N, f))
    case Spec.HwOne{}:
      route_on(Bool.and(U32.is_eq(major, 8), U32.is_eq(minor, 6)), U32.is_eq(batch, 1), U32.is_ge(M, 1024),
        shape_in(wide_shapes(), K, N, f))
