# Independent reference for the wide-tile prefill GEMM of ext patch 3011 (hgemm_wide.bend is the model of the
# CUDA code; hgemm_wide_laws.bend relates the two). Written from what the kernel must do, not from its code:
#   - output ownership: tile (tm, tn) of a grouped raster is computed by the block whose id counts, inside
#     group g = tm / G, the group's min(G, gm - g G) M-stripes column by column; inside a 128 x 128 tile the
#     m16n8 accumulator layout of 2 x 2 warps with 64 x 64 warp tiles gives each element one (thread,
#     fragment, half, pair element) owner;
#   - accumulation: every output element adds, in order, one fp16 partial per 32-wide K slice, each partial
#     being two m16n8k16 MMAs (k offsets x, x + 16) issued into a +0 accumulator;
#   - stage slots: a swizzle is its own inverse, so slot s of a stage row holds logical chunk (s % CPR) ^ key;
#   - route: the wide kernel serves exactly the projection shapes of Qwen3.8-27B and its DFlash2 draft.
import Base

# Bitwise xor of the low `bits` bits of a and b.
def xor(bits: Nat, +a: Nat, +b: Nat) -> Nat:
  match bits:
    case 0n:
      0n
    case 1n+f:
      Nat.add(Nat.mod(Nat.add(Nat.mod(a, 2n), Nat.mod(b, 2n)), 2n), Nat.mul(2n, xor(f, Nat.div(a, 2n), Nat.div(b, 2n))))

# ==== output ownership ====

# The M-stripes of group g: min(G, gm - g G).
def stripes(+g: Nat, +G: Nat, +gm: Nat) -> Nat:
  Nat.min(G, Nat.sub(gm, Nat.mul(g, G)))

# The block id that computes tile (tm, tn).
def bid_of(+tm: Nat, +tn: Nat, +G: Nat, +gn: Nat, +gm: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.div(tm, G), Nat.mul(G, gn)),
    Nat.add(Nat.mul(tn, stripes(Nat.div(tm, G), G, gm)), Nat.mod(tm, G)))

# The block (blockIdx.y, blockIdx.x) that stores output element (R, C): the block of tile (R / 128, C / 128).
def own_block(+R: Nat, +C: Nat, +G: Nat, +gn: Nat, +gm: Nat) -> Nat:
  bid_of(Nat.div(R, 128n), Nat.div(C, 128n), G, gn, gm)

def own_by(+R: Nat, +C: Nat, +G: Nat, +gn: Nat, +gm: Nat) -> Nat:
  Nat.div(own_block(R, C, G, gn, gm), gn)

def own_bx(+R: Nat, +C: Nat, +G: Nat, +gn: Nat, +gm: Nat) -> Nat:
  Nat.mod(own_block(R, C, G, gn, gm), gn)

# Owner of element (r, c) of a 128 x 128 tile: warp (r / 64, c / 64) of the 2 x 2 warp grid, lane
# 4 (r % 8) + (c % 8) / 2 of the m16n8 accumulator fragment, fragment row block i = (r % 64) / 16, half
# h = (r % 16) / 8, fragment column block j = (c % 64) / 8, pair element e = c % 2.
def own_tid(+r: Nat, +c: Nat) -> Nat:
  Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.div(r, 64n), 2n), Nat.div(c, 64n)), 32n),
    Nat.add(Nat.mul(Nat.mod(r, 8n), 4n), Nat.div(Nat.mod(c, 8n), 2n)))

def own_i(+r: Nat) -> Nat:
  Nat.div(Nat.mod(r, 64n), 16n)

def own_h(+r: Nat) -> Nat:
  Nat.div(Nat.mod(r, 16n), 8n)

def own_j(+c: Nat) -> Nat:
  Nat.div(Nat.mod(c, 64n), 8n)

def own_e(+c: Nat) -> Nat:
  Nat.mod(c, 2n)

# ==== accumulation order ====

# n consecutive 32-wide K slices starting at k offset x: each partial is [x, x + 16].
def slices(n: Nat, +x: Nat) -> List<&2, List<&2, Nat>>:
  match n:
    case 0n:
      Nil{}
    case 1n+rest:
      [x, Nat.add(x, 16n)] <> slices(rest, Nat.add(x, 32n))

# ==== stage slots ====

# A stage (128 rows x 4 chunks of 8 halves): slot s is row s / 4, logical chunk (s % 4) ^ ((row / 2) % 4),
# i.e. linear chunk index c = 4 row + chunk, written by thread c % 128 in iteration c / 128.
def a_row(+s: Nat) -> Nat:
  Nat.div(s, 4n)

def a_chunk(+s: Nat) -> Nat:
  xor(2n, Nat.mod(s, 4n), Nat.mod(Nat.div(a_row(s), 2n), 4n))

def a_own_c(+s: Nat) -> Nat:
  Nat.add(Nat.mul(a_row(s), 4n), a_chunk(s))

# B stage (32 rows x 16 chunks): slot s is row s / 16, logical chunk (s % 16) ^ (row % 8).
def b_row(+s: Nat) -> Nat:
  Nat.div(s, 16n)

def b_chunk(+s: Nat) -> Nat:
  xor(4n, Nat.mod(s, 16n), Nat.mod(b_row(s), 8n))

def b_own_c(+s: Nat) -> Nat:
  Nat.add(Nat.mul(b_row(s), 16n), b_chunk(s))

# ==== route ====

# EXL3_HGEMM_F16ACC_WIDE: unset, "1", "0", anything else.
type HwEnv is Data:
  HwUnset{}
  HwOne{}
  HwZero{}
  HwOther{}

type HwRoute is Data:
  HwWide{}
  HwServed{}
  HwError{}

type HwShape is Data:
  HwShape{k: U32, n: U32, out_f32: Bool}

# The projection shapes of one prefill chunk of Qwen3.8-27B (hidden 5120, MLP 17408, GDN 16 key heads and
# 48 value heads of 128, attention 24 q / 4 kv heads of 256 with an interleaved gate) and of its DFlash2
# draft (8 kv heads of 128, fc over 5 tapped layers); fp32 output where the projection feeds the residual
# or the GDN recurrence.
def served_shapes() -> List<&2, HwShape>:
  HwShape{5120, (4 * 256 : U32), False{}} <>
  HwShape{5120, (48 * 128 : U32), True{}} <>
  HwShape{5120, ((2 * 16 * 128 : U32) + (48 * 128 : U32) : U32), True{}} <>
  HwShape{5120, (2 * 24 * 256 : U32), False{}} <>
  HwShape{5120, 17408, False{}} <>
  HwShape{(48 * 128 : U32), 5120, True{}} <>
  HwShape{17408, 5120, True{}} <>
  HwShape{(5 * 5120 : U32), 5120, False{}} <>
  Nil{}

def shape_eq(+a: HwShape, +b: HwShape) -> Bool:
  match a b:
    case HwShape{k1, n1, f1} HwShape{k2, n2, f2}:
      Bool.and(U32.is_eq(k1, k2), Bool.and(U32.is_eq(n1, n2), Bool.not(Bool.xor(f1, f2))))

def member(xs: List<&2, HwShape>, +s: HwShape) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(shape_eq(y, s), member(rest, s))

# The kernel's shape requirements (N % BN == 0, K % BK == 0) hold for every shape of a list.
def all_fit(xs: List<&2, HwShape>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case HwShape{k, n, f} <> rest:
      Bool.and(U32.is_eq((n % 128 : U32), 0), Bool.and(U32.is_eq((k % 32 : U32), 0), all_fit(rest)))

def pick(wide: Bool) -> HwRoute:
  match wide:
    case True{}:
      HwWide{}
    case False{}:
      HwServed{}

# The intended route: an error for a malformed switch; otherwise the wide kernel exactly when it is on,
# the device is sm86, the GEMM is unbatched, M >= 1024 and the shape is a served one.
def route(env: HwEnv, on_device: Bool, unbatched: Bool, long: Bool, served: Bool) -> HwRoute:
  match env:
    case HwOther{}:
      HwError{}
    case HwZero{}:
      HwServed{}
    case HwUnset{}:
      pick(Bool.and(on_device, Bool.and(unbatched, Bool.and(long, served))))
    case HwOne{}:
      pick(Bool.and(on_device, Bool.and(unbatched, Bool.and(long, served))))

