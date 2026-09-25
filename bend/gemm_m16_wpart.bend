# Slot-weighted split-K partition of the grouped m16 GEMM, ext 2105 (patches/exl3-ext/
# 2105-proj-m16g-weighted-on9003b.patch; the same formula is 8205's 8201/8202 schedule generator),
# transcribed from the C integer expressions over Nat. K = exllamav3_ext/quant/exl3_gemm_m16g_kernel.cuh,
# H = exllamav3_ext/quant/exl3_gemm_m16g.cu (line numbers of the pinned tree fefa0be + series).
# Block b < G has weight w0 if b < nsm (the first CTA on each SM) else w1; W(b) is the weight of the
# blocks before b and block b owns the iterations [start(b), start(b + 1)), start(b) = total W(b) / W(G).
# The C evaluates W, the products and the quotients in int64 (K:56, K:61, K:68-71, H:85, H:90, H:96-99);
# Nat arithmetic is that arithmetic while no int64 overflows (the served products are below 2^28),
# `std::max(b - nsm, 0)` is Nat.sub(b, nsm), and the owner's `P - w0 * nsm` runs only when P >= w0 * nsm.
# Every def is generic in total, G, nsm, w0 and w1; the host guard (H:103-109 weights_valid) is
# weights_valid below. (w, w) is ext 2001's v2 partition (gemm_m16_partition.bend), proven in
# gemm_m16_wpart_proof.bend. Reference: gemm_m16_wpart_spec.bend; laws: gemm_m16_wpart_laws.bend.
import Base
import ./gemm_m16_partition.bend as V2

# K:54-57 exl3_m16g_wpre (= H:83-86 wpre): w0 * min(b, nsm) + w1 * max(b - nsm, 0)
def wpre(+b: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Nat:
  Nat.add(Nat.mul(w0, Nat.min(b, nsm)), Nat.mul(w1, Nat.sub(b, nsm)))

# K:59-62 exl3_m16g_start (= H:88-91 wstart): total * W(b) / W(G)
def start(+b: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Nat:
  Nat.div(Nat.mul(total, wpre(b, nsm, w0, w1)), wpre(G, nsm, w0, w1))

# K:69 (= H:97) P = ((x + 1) * WG + total - 1) / total - 1: the largest weight prefix p with
# total * p / WG <= x
def wprefix(+x: Nat, +total: Nat, +WG: Nat) -> Nat:
  Nat.sub(Nat.div(Nat.sub(Nat.add(Nat.mul(1n+x, WG), total), 1n), total), 1n)

# K:70-71 (= H:98-99): P < w0 * nsm ? P / w0 : nsm + (P - w0 * nsm) / w1
def owner.pick(below: Bool, +P: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Nat:
  match below:
    case True{}:
      Nat.div(P, w0)
    case False{}:
      Nat.add(nsm, Nat.div(Nat.sub(P, Nat.mul(w0, nsm)), w1))

# K:66-72 exl3_m16g_owner (= H:94-100 owner): WG = W(G) (K:68), P (K:69), the two segments (K:70-71)
def owner(+x: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Nat:
  owner.pick(Nat.is_lt(wprefix(x, total, wpre(G, nsm, w0, w1)), Nat.mul(w0, nsm)),
    wprefix(x, total, wpre(G, nsm, w0, w1)), nsm, w0, w1)

# H:106-107: for (b = 0; b < G; ++b) if (wstart(b + 1) <= wstart(b)) return false; `left` counts the
# remaining blocks.
def weights_valid.go(left: Nat, +b: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat)
    -> Bool:
  match left:
    case 0n:
      True{}
    case 1n+rest:
      Bool.and(Nat.is_lt(start(b, total, G, nsm, w0, w1), start(1n+b, total, G, nsm, w0, w1)),
        weights_valid.go(rest, 1n+b, total, G, nsm, w0, w1))

# H:103-109 weights_valid: w0, w1, nsm >= 1, nsm <= G <= 2 nsm (H:105), every slice non-empty (H:106-107)
def weights_valid(+total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Bool:
  Bool.and(Nat.is_le(1n, w0), Bool.and(Nat.is_le(1n, w1), Bool.and(Nat.is_le(1n, nsm),
    Bool.and(Nat.is_le(nsm, G), Bool.and(Nat.is_le(G, Nat.mul(2n, nsm)),
      weights_valid.go(G, 0n, total, G, nsm, w0, w1))))))

# K:279 cidx base first_contrib(g) = owner(g * KT) (also K:376, H:118)
def first_contrib(g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Nat:
  owner(Nat.mul(g, KT), total, G, nsm, w0, w1)

# K:375 owner((g + 1) * KT - 1) (also H:118)
def last_contrib(g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Nat:
  owner(Nat.sub(Nat.mul(1n+g, KT), 1n), total, G, nsm, w0, w1)

# K:375-376 nc = owner((g + 1) * KT - 1) - owner(g * KT) + 1 (H:118 the same expression)
def nc(+g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Nat:
  Nat.add(Nat.sub(last_contrib(g, KT, total, G, nsm, w0, w1), first_contrib(g, KT, total, G, nsm, w0, w1)),
    1n)

# K:279-280: partial slot of block b for group g: g * max_contrib + (b - first_contrib(g))
def address(g: Nat, +mc: Nat, b: Nat, lo: Nat) -> Nat:
  Nat.add(Nat.mul(g, mc), Nat.sub(b, lo))

# H:115-120: for g in [0, groups): nc = owner((g+1)*KT-1) - owner(g*KT) + 1; if (nc > mc) mc = nc
# (the same update as 2001's, V2.max_contrib.pick). `left` counts the remaining groups.
def max_contrib.go(left: Nat, +g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat,
    +w1: Nat, +mc: Nat) -> Nat:
  match left:
    case 0n:
      mc
    case 1n+rest:
      +n = nc(g, KT, total, G, nsm, w0, w1)
      max_contrib.go(rest, 1n+g, KT, total, G, nsm, w0, w1, V2.max_contrib.pick(Nat.is_gt(n, mc), n, mc))

# H:112-122 max_contrib(groups, KT, G, w): total = groups * KT (H:114), mc = 1 (H:115)
def max_contrib(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Nat:
  max_contrib.go(groups, 0n, KT, Nat.mul(groups, KT), G, nsm, w0, w1, 1n)

# EXL3_M16_SLOT_FLOATS = 16 * EXL3_M16_GW, EXL3_M16_GW = EXL3_M16_WARPS * EXL3_M16_TILES_W * 16 = 8 * 4 * 16
# (exl3_gemm_m16_kernel.cuh:37-39)
def slot_floats() -> Nat:
  Nat.mul(16n, Nat.mul(Nat.mul(8n, 4n), 16n))

# H:20 EXL3_M16G_SLOT_BYTES = 8ull * 1024 * 1024, written as 8 * k * k at k = 1024. The capacity stays
# a parameter (launch_fits_cap) in the laws: the checker's Nat is unary and normalizes closed terms,
# so an 8 Mi-long numeral in a checked type exhausts its stack; the served law binds cap = 8 k k, k = 1024.
def slot_bytes_of(+k: Nat) -> Nat:
  Nat.mul(Nat.mul(8n, k), k)

def slot_bytes() -> Nat:
  slot_bytes_of(1024n)

# H:144 (uint64_t) groups * max_contrib * EXL3_M16_SLOT_FLOATS * sizeof(float)
def ws_bytes(+groups: Nat, +mc: Nat) -> Nat:
  Nat.mul(Nat.mul(Nat.mul(groups, mc), slot_floats()), 4n)

# H:141-145 launch_fits with the slot workspace size as `cap`: groups * KT >= G && the partial slots fit
def launch_fits_cap(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +cap: Nat) -> Bool:
  Bool.and(Nat.is_ge(Nat.mul(groups, KT), G),
    Nat.is_le(ws_bytes(groups, max_contrib(groups, KT, G, nsm, w0, w1)), cap))

# H:141-145 launch_fits (cap = EXL3_M16G_SLOT_BYTES)
def launch_fits(+groups: Nat, +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> Bool:
  launch_fits_cap(groups, KT, G, nsm, w0, w1, slot_bytes())

# ---- served instance (RTX 3090: 82 SMs x 2 CTAs; H:195-196 g_weights rows) ----

# SM count and grid of the m <= 8 launches (H:124-128 grid_size: nsm * blocks_per_sm = 82 * 2)
def nsm_served() -> Nat:
  82n

def grid_served() -> Nat:
  Nat.mul(82n, 2n)

# k 5120: KT = size_k / 16 (H:343)
def kt_served() -> Nat:
  Nat.div(5120n, 16n)

# GDN in_proj_qkv + in_proj_z, widths { 10240, 6144 }: groups = sum n / EXL3_M16_GW (H:336)
def groups_gdn() -> Nat:
  Nat.add(Nat.div(10240n, 512n), Nat.div(6144n, 512n))

# attention q + k + v, widths { 12288, 1024, 1024 }
def groups_attn() -> Nat:
  Nat.add(Nat.div(12288n, 512n), Nat.add(Nat.div(1024n, 512n), Nat.div(1024n, 512n)))

# H:195-196: both rows' weights (w0, w1) = (100, 91)
def w0_served() -> Nat:
  100n

def w1_served() -> Nat:
  91n
