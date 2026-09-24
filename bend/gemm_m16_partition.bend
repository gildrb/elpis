# Work partition of the EXL3 m16 swap-AB GEMM (patches/exl3-ext/2001-gemm-m16-swapab.patch),
# transcribed from the CUDA integer expressions over Nat. K = exllamav3_ext/quant/
# exl3_gemm_m16_kernel.cuh, H = exllamav3_ext/quant/exl3_gemm_m16.cu (post-patch line numbers).
# C `int` arithmetic on the non-negative values used here is Nat arithmetic while no product
# overflows (the kernel widens b * total and (x + 1) * G to int64); `>> 4` / `>> 7` / `>> 1` are
# `/ 16` / `/ 128` / `/ 2` and `& 1` is `% 2` on non-negative ints. The independent reference is
# gemm_m16_partition_spec.bend; the laws are gemm_m16_partition_laws.bend.
import Base
import ./gemm_m16_partition_spec.bend as Spec

# K:90 KT = size_k >> 4 (16-deep k-tiles)
def kt(k: Nat) -> Nat:
  Nat.div(k, 16n)

# K:92 NG = size_n >> 7 (128-column output groups per matrix)
def ng(n: Nat) -> Nat:
  Nat.div(n, 128n)

# H:182 groups = num_mats * (size_n / 128)
def groups(mats: Nat, n: Nat) -> Nat:
  Nat.mul(mats, ng(n))

# K:93 total = p.num_mats * NG * KT (H:183 groups * KT); iteration x = group * KT + k-tile
def total(mats: Nat, n: Nat, k: Nat) -> Nat:
  Nat.mul(groups(mats, n), kt(k))

# K:96 s_b = (int64) b * total / G; K:97 e_b = start(b + 1)
def start(b: Nat, +total: Nat, G: Nat) -> Nat:
  Nat.div(Nat.mul(b, total), G)

# K:65-68 (= H:83-86) owner(x, total, G) = ((int64) x + 1) * G + total - 1) / total - 1
def owner(x: Nat, +total: Nat, +G: Nat) -> Nat:
  Nat.sub(Nat.div(Nat.sub(Nat.add(Nat.mul(1n+x, G), total), 1n), total), 1n)

# K:84 nh = warp & 1 (64-column half)
def half(w: Nat) -> Nat:
  Nat.mod(w, 2n)

# K:85 kp = warp >> 1 (k-phase)
def phase(w: Nat) -> Nat:
  Nat.div(w, 2n)

def nj.pick(big: Bool, span: Nat, kp: Nat) -> Nat:
  match big:
    case True{}:
      Nat.div(Nat.add(Nat.sub(span, kp), 3n), 4n)
    case False{}:
      0n

# K:103 nj = e_b - s_b > kp ? (e_b - s_b - kp + 3) / 4 : 0 (iterations issued by phase kp)
def nj(+s: Nat, +e: Nat, +kp: Nat) -> Nat:
  nj.pick(Nat.is_gt(Nat.sub(e, s), kp), Nat.sub(e, s), kp)

# K:131 / K:164 / K:175 / K:199 + K:207: j-th iteration of phase kp is s_b + kp + 4 * j
def iter(s: Nat, kp: Nat, +j: Nat) -> Nat:
  Nat.add(Nat.add(s, kp), Nat.mul(4n, j))

# Warp w's issued/computed tiles: iter(s_b, kp, j) for j < nj(s_b, e_b, kp), kp = w >> 1.
def handles.go(left: Nat, +j: Nat, +x: Nat, +s: Nat, +kp: Nat) -> Bool:
  match left:
    case 0n:
      False{}
    case 1n+rest:
      Bool.or(Nat.is_eq(iter(s, kp, j), x), handles.go(rest, 1n+j, x, s, kp))

def handles(+w: Nat, +x: Nat, +s: Nat, +e: Nat) -> Bool:
  handles.go(nj(s, e, phase(w)), 0n, x, s, phase(w))

# Number of the warps w < count (EXL3_M16_WARPS = 8, K:30) of 64-column half h that run
# tile x of the block range [s, e).
def handlers(+count: Nat, +x: Nat, +h: Nat, +s: Nat, +e: Nat) -> Nat:
  match count:
    case 0n:
      0n
    case 1n+w:
      Nat.add(handlers(w, x, h, s, e),
        Spec.bit(Bool.and(Nat.is_eq(half(w), h), handles(w, x, s, e))))

def runs.pick(nonempty: Bool, +s: Nat, +e: Nat, +KT: Nat, +g: Nat) -> Bool:
  match nonempty:
    case True{}:
      Bool.and(Nat.is_le(Nat.div(s, KT), g), Nat.is_le(g, Nat.div(Nat.sub(e, 1n), KT)))
    case False{}:
      False{}

# K:200-203: g_first = e_b > s_b ? s_b / KT : 0; g_last = e_b > s_b ? (e_b - 1) / KT : -1;
# the group loop runs g iff g_first <= g <= g_last (never for an empty range).
def runs(+s: Nat, +e: Nat, +KT: Nat, +g: Nat) -> Bool:
  runs.pick(Nat.is_gt(e, s), s, e, KT, g)

# K:205 seg_hi = min(e_b, (g + 1) * KT): the segment loop K:207 runs `it` while it < seg_hi
def seg_hi(e: Nat, g: Nat, +KT: Nat) -> Nat:
  Nat.min(e, Nat.mul(1n+g, KT))

type Cursor is Data:
  Cursor{g: Nat, kt: Nat}

# K:176-177 (and K:132-133, K:165-166): g = it / KT; kt = it - g * KT
def decode(+it: Nat, +KT: Nat) -> Cursor:
  Cursor{Nat.div(it, KT), Nat.sub(it, Nat.mul(Nat.div(it, KT), KT))}

def advance.pick(wrap: Bool, g: Nat, kt: Nat, KT: Nat) -> Cursor:
  match wrap:
    case True{}:
      Cursor{1n+g, Nat.sub(kt, KT)}
    case False{}:
      Cursor{g, kt}

# K:213-214: iss_kt += 4; if (iss_kt >= KT) { iss_kt -= KT; iss_g++; }
def advance(c: Cursor, +KT: Nat) -> Cursor:
  match c:
    case Cursor{g, kt}:
      +k4 = Nat.add(kt, 4n)
      advance.pick(Nat.is_ge(k4, KT), g, k4, KT)

# K:261-262: shared reduction slot (which, nh) of the in-block tree is red + (which * 2 + nh)
def red_slot(which: Nat, nh: Nat) -> Nat:
  Nat.add(Nat.mul(which, 2n), nh)

# K:284-292: in-block fixed tree over the four k-phase partials of one half.
def tree(p0: Spec.Sum, p1: Spec.Sum, p2: Spec.Sum, p3: Spec.Sum) -> Spec.Sum:
  # K:284-285: kp 2 puts slot0, kp 3 puts slot1
  s0 = p2
  s1 = p3
  # K:287-288: kp 0 adds slot0, kp 1 adds slot1 (acc += s)
  a0 = {Spec.Add{p0, s0} : Spec.Sum}
  a1 = {Spec.Add{p1, s1} : Spec.Sum}
  # K:290: kp 1 puts slot0; K:292: kp 0 adds slot0
  s0b = a1
  Spec.Add{a0, s0b}

# K:321 b_lo = owner(g * KT, total, G)
def b_lo(g: Nat, +KT: Nat, +total: Nat, +G: Nat) -> Nat:
  owner(Nat.mul(g, KT), total, G)

# K:322 b_hi = owner((g + 1) * KT - 1, total, G)
def b_hi(g: Nat, +KT: Nat, +total: Nat, +G: Nat) -> Nat:
  owner(Nat.sub(Nat.mul(1n+g, KT), 1n), total, G)

# K:323 nc = b_hi - b_lo + 1
def nc(+g: Nat, +KT: Nat, +total: Nat, +G: Nat) -> Nat:
  Nat.add(Nat.sub(b_hi(g, KT, total, G), b_lo(g, KT, total, G)), 1n)

# K:328: partial slot of block b for group g: g * max_contrib + (b - b_lo)
def address(g: Nat, +mc: Nat, b: Nat, lo: Nat) -> Nat:
  Nat.add(Nat.mul(g, mc), Nat.sub(b, lo))

def max_contrib.pick(bigger: Bool, n: Nat, mc: Nat) -> Nat:
  match bigger:
    case True{}:
      n
    case False{}:
      mc

# H:186-191: max_contrib = 1; for g in [0, groups): nc = owner((g+1)*KT-1) - owner(g*KT) + 1;
# if (nc > max_contrib) max_contrib = nc. `left` counts the remaining groups.
def max_contrib.go(left: Nat, +g: Nat, +KT: Nat, +total: Nat, +G: Nat, +mc: Nat) -> Nat:
  match left:
    case 0n:
      mc
    case 1n+rest:
      +n = Nat.add(Nat.sub(owner(Nat.sub(Nat.mul(1n+g, KT), 1n), total, G),
        owner(Nat.mul(g, KT), total, G)), 1n)
      max_contrib.go(rest, 1n+g, KT, total, G, max_contrib.pick(Nat.is_gt(n, mc), n, mc))

def max_contrib(groups: Nat, +KT: Nat, +total: Nat, +G: Nat) -> Nat:
  max_contrib.go(groups, 0n, KT, total, G, 1n)

# K:328-331: one arriving contributor b stores its partial into its group slot b - b_lo
# (workspace of one group, slot-indexed; slots past the list are never written here).
def store(ws: List<&2, Spec.Sum>, idx: Nat, v: Spec.Sum) -> List<&2, Spec.Sum>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      match idx:
        case 0n:
          v <> rest
        case 1n+i:
          w <> store(rest, i, v)

# Contributors arrive in any order; each stores Part{b} at b - lo.
def arrive(order: List<&2, Nat>, ws: List<&2, Spec.Sum>, +lo: Nat) -> List<&2, Spec.Sum>:
  match order:
    case Nil{}:
      ws
    case +b <> rest:
      arrive(rest, store(ws, Nat.sub(b, lo), Spec.Part{b}), lo)

def slot_at(ws: List<&2, Spec.Sum>, idx: Nat) -> Spec.Sum:
  match ws:
    case Nil{}:
      Spec.Part{0n}
    case w <> rest:
      match idx:
        case 0n:
          w
        case 1n+i:
          slot_at(rest, i)

def finish.go(left: Nat, +c: Nat, v: Spec.Sum, +ws: List<&2, Spec.Sum>) -> Spec.Sum:
  match left:
    case 0n:
      v
    case 1n+rest:
      finish.go(rest, 1n+c, Spec.Add{v, slot_at(ws, c)}, ws)

# K:344-354: the last arriver reads slot 0, then adds slots 1 .. nc - 1 in slot order
# (v = slot 0; for c = 1; c < nc; ++c: v += slot c). Uses neither the arrival order nor
# the finishing block's id.
def finish(+ws: List<&2, Spec.Sum>, cnt: Nat) -> Spec.Sum:
  finish.go(Nat.sub(cnt, 1n), 1n, slot_at(ws, 0n), ws)
