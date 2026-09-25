# The b/a GEMV of ext 5106 (exllamav3_ext/gdn.cu, gdn_conv_rule_norm_kernel<a_log_T, norm_w_T, K, KS,
# STAMP>, KS = 1, 2: the k split), transcribed from the kernel's index expressions over Nat, with fp32
# arithmetic kept symbolic: a b/a value is the expression tree (Ex) of the fmaf / add operations that
# produce it, so two values are equal iff the kernel performs the same operations on the same operands
# in the same order. C int arithmetic on the non-negative values here is Nat arithmetic (t < 512,
# i < 5, s < 8, k2 <= 2560, h < H <= 2^10: no overflow).
#   - thread t = (warp_id t / 32, lane_id t % 32); `j = warp_id * 32 + lane_id + i * THREADS`, THREADS
#     = 512, i < GR_KS_ITERS = 5, guarded `if (j < k2)`, k2 = k / 2
#   - x half2 `x2[s * k2 + j]` (x2 = ba_x + b * S * k), w half2 `wb[j]` / `wa[j]` (ba_w + h * k and
#     ba_w + (H + h) * k: half2 index h * k2 + j / (H + h) * k2 + j); `.x` = component 0, `.y` = 1
#   - per i, for s < GR_KS_ROWS = 8 with `if (s < S)`: pb[s] = fmaf(xf.x, wbf.x, pb[s]);
#     pb[s] = fmaf(xf.y, wbf.y, pb[s]); pa[s] likewise with waf; pb, pa start at 0.0f
#   - per s < S: `pb[s] += __shfl_down_sync(0xffffffff, pb[s], offset)` for offset 16, 8, 4, 2, 1
#     (lanes whose source lane is >= 32 read their own value), then lane 0 writes
#     ks_part[warp_id * 2 * GR_KS_ROWS + s] = pb[s], ks_part[warp_id * 2 * GR_KS_ROWS + GR_KS_ROWS + s] = pa[s]
#   - thread t < S after the barrier: bv = 0.0f; for w < 16: bv += ks_part[w * 2 * GR_KS_ROWS + t];
#     av likewise at + GR_KS_ROWS; `if (ba_bias)` bv += bias[h], av += bias[H + h]
#   - launcher: `if (S > GR_KS_ROWS || k / 2 > 512 * GR_KS_ITERS) ks = 0;`
# Block event order of the kernel around the partial exchange (prog). bend/gdn_ba_ksplit_diff.py
# re-derives the index table and the event order from a 5106 tree and compares them with
# GDN_BA_KSPLIT_TABLE.bend. Reference: gdn_ba_ksplit_spec.bend; laws: gdn_ba_ksplit_laws.bend.
# Proof model only (not shipped).
import Base

# An fp32 value as the operations that produced it.
type Ex is Data:
  Zero{}                                 # 0.0f
  Fma{x2: Nat, w2: Nat, c: Nat, acc: Ex}   # fmaf(x half2 x2 component c, w half2 w2 component c, acc)
  Add{a: Ex, b: Ex}                      # a + b (fp32)
  Bias{e: Ex, o: Nat}                    # e + __half2float(ba_bias[o])
  Stale{q: Nat}                          # ks_part[q] not written by this launch

# (pb[s], pa[s]) of one thread
type P is Data:
  P{b: Ex, a: Ex}

# C ternary `c ? x : y`
def pick(c: Bool, +x: Nat, +y: Nat) -> Nat:
  match c:
    case True{}:
      x
    case False{}:
      y

def warp(+t: Nat) -> Nat:
  Nat.div(t, 32n)

def lane(+t: Nat) -> Nat:
  Nat.mod(t, 32n)

# j = warp_id * 32 + lane_id + i * THREADS
def ks_j(+t: Nat, +i: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(warp(t), 32n), lane(t)), Nat.mul(i, 512n))

# the two fmaf of one half2 (x2 = s * k2 + j, w2 = row * k2 + j), .x then .y
def fma2(+s: Nat, +row: Nat, +j: Nat, +k2: Nat, acc: Ex) -> Ex:
  +x2 = Nat.add(Nat.mul(s, k2), j)
  +w2 = Nat.add(Nat.mul(row, k2), j)
  Fma{x2, w2, 1n, Fma{x2, w2, 0n, acc}}

def upd(c: Bool, +s: Nat, +j: Nat, +k2: Nat, +h: Nat, +H: Nat, b: Ex, a: Ex) -> P:
  match c:
    case True{}:
      P{fma2(s, h, j, k2, b), fma2(s, Nat.add(H, h), j, k2, a)}
    case False{}:
      P{b, a}

# for (s = 0; s < GR_KS_ROWS; ++s) if (s < S) { pb[s] ...; pa[s] ... }  (xs = pb/pa of rows s.., 8 entries)
def srows(xs: List<&2, P>, +s: Nat, +S: Nat, +j: Nat, +k2: Nat, +h: Nat, +H: Nat) -> List<&2, P>:
  match xs:
    case Nil{}:
      Nil{}
    case P{b, a} <> rest:
      upd(Nat.is_lt(s, S), s, j, k2, h, H, b, a) <> srows(rest, 1n+s, S, j, k2, h, H)

def iguard(c: Bool, +j: Nat, +S: Nat, +k2: Nat, +h: Nat, +H: Nat, xs: List<&2, P>) -> List<&2, P>:
  match c:
    case True{}:
      srows(xs, 0n, S, j, k2, h, H)
    case False{}:
      xs

# for (i = i0; i < GR_KS_ITERS; ++i) { j = ...; if (j < k2) ... }  (fuel = remaining iterations)
def iloop(fuel: Nat, +i: Nat, +t: Nat, +S: Nat, +k2: Nat, +h: Nat, +H: Nat, xs: List<&2, P>) -> List<&2, P>:
  match fuel:
    case 0n:
      xs
    case 1n+more:
      iloop(more, 1n+i, t, S, k2, h, H, iguard(Nat.is_lt(ks_j(t, i), k2), ks_j(t, i), S, k2, h, H, xs))

def zeros(n: Nat) -> List<&2, P>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      P{Zero{}, Zero{}} <> zeros(m)

# pb[0..7], pa[0..7] of thread t after the FMA loop (GR_KS_ITERS = 5, GR_KS_ROWS = 8)
def accs(+t: Nat, +S: Nat, +k2: Nat, +h: Nat, +H: Nat) -> List<&2, P>:
  iloop(5n, 0n, t, S, k2, h, H, zeros(8n))

def get_ab(p: P, ab: Nat) -> Ex:
  match p:
    case P{b, a}:
      match ab:
        case 0n:
          b
        case 1n+z:
          a

# pb[n] (ab = 0) or pa[n] (ab = 1)
def get_p(xs: List<&2, P>, n: Nat, ab: Nat) -> Ex:
  match xs:
    case Nil{}:
      Zero{}
    case p <> rest:
      match n:
        case 0n:
          get_ab(p, ab)
        case 1n+m:
          get_p(rest, m, ab)

# task (s, ab) accumulator of thread t
def acc(+t: Nat, +S: Nat, +s: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat) -> Ex:
  get_p(accs(t, S, k2, h, H), s, ab)

def at(xs: List<&2, Ex>, n: Nat) -> Ex:
  match xs:
    case Nil{}:
      Zero{}
    case x <> rest:
      match n:
        case 0n:
          x
        case 1n+m:
          at(rest, m)

# the 32 lanes of warp w: lane l holds acc of thread 32 w + l
def wlanes(fuel: Nat, +l: Nat, +w: Nat, +S: Nat, +s: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat) -> List<&2, Ex>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+more:
      acc(Nat.add(Nat.mul(w, 32n), l), S, s, ab, k2, h, H) <> wlanes(more, 1n+l, w, S, s, ab, k2, h, H)

# v += __shfl_down_sync(0xffffffff, v, off): lane l reads lane l + off, its own value past lane 31
def shfl_go(fuel: Nat, +l: Nat, +vs: List<&2, Ex>, +off: Nat) -> List<&2, Ex>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+more:
      Add{at(vs, l), at(vs, pick(Nat.is_lt(Nat.add(l, off), 32n), Nat.add(l, off), l))} <> shfl_go(more, 1n+l, vs, off)

def shfl(+vs: List<&2, Ex>, +off: Nat) -> List<&2, Ex>:
  shfl_go(32n, 0n, vs, off)

# for (offset = 16; offset > 0; offset >>= 1) ...; lane 0's value
def tree(+vs: List<&2, Ex>) -> Ex:
  at(shfl(shfl(shfl(shfl(shfl(vs, 16n), 8n), 4n), 2n), 1n), 0n)

# ks_part slot lane 0 of warp w writes for row s: warp_id * 2 * GR_KS_ROWS + s (b), + GR_KS_ROWS (a)
def wslot(+w: Nat, +s: Nat, +ab: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(Nat.mul(w, 2n), 8n), Nat.mul(ab, 8n)), s)

# slot q -> (warp, b|a, row)
def dec_w(+q: Nat) -> Nat:
  Nat.div(q, 16n)

def dec_ab(+q: Nat) -> Nat:
  Nat.div(Nat.mod(q, 16n), 8n)

def dec_s(+q: Nat) -> Nat:
  Nat.mod(q, 8n)

# ks_part[q] after the barrier: written iff its row is < S (lane 0 writes rows s < S only)
def smem_row(c: Bool, +q: Nat, +S: Nat, +k2: Nat, +h: Nat, +H: Nat) -> Ex:
  match c:
    case True{}:
      tree(wlanes(32n, 0n, dec_w(q), S, dec_s(q), dec_ab(q), k2, h, H))
    case False{}:
      Stale{q}

def smem(+q: Nat, +S: Nat, +k2: Nat, +h: Nat, +H: Nat) -> Ex:
  smem_row(Nat.is_lt(dec_s(q), S), q, S, k2, h, H)

# reader index of thread t for warp w: w * 2 * GR_KS_ROWS + t (b), + GR_KS_ROWS (a)
def rslot(+w: Nat, +t: Nat, +ab: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(Nat.mul(w, 2n), 8n), Nat.mul(ab, 8n)), t)

# for (w = w0; w < GR_WARPS; ++w) v += ks_part[...]
def rsum(fuel: Nat, +w: Nat, +t: Nat, +ab: Nat, +S: Nat, +k2: Nat, +h: Nat, +H: Nat, v: Ex) -> Ex:
  match fuel:
    case 0n:
      v
    case 1n+more:
      rsum(more, 1n+w, t, ab, S, k2, h, H, Add{v, smem(rslot(w, t, ab), S, k2, h, H)})

def with_bias(hb: Bool, +o: Nat, v: Ex) -> Ex:
  match hb:
    case True{}:
      Bias{v, o}
    case False{}:
      v

# b (ab = 0) or a (ab = 1) of row t < S, as stored to ba_out
def task(+S: Nat, +t: Nat, +ab: Nat, +k2: Nat, +h: Nat, +H: Nat, hb: Bool) -> Ex:
  with_bias(hb, pick(Nat.is_eq(ab, 0n), h, Nat.add(H, h)), rsum(16n, 0n, t, ab, S, k2, h, H, Zero{}))

# ==== launcher: the variant that runs (0 = the per-warp GEMV) ====
def variant(+ks: Nat, +S: Nat, +k: Nat) -> Nat:
  pick(Bool.or(Nat.is_lt(8n, S), Nat.is_lt(2560n, Nat.div(k, 2n))), 0n, ks)

# ==== block event order around the partial exchange ====
type Ev is Data:
  KsLoad{}     # ks_load(): the b/a operand loads of the k split
  State{}      # gdn_rule_load_state
  NormOps{}    # gdn_rule_norm_prefetch
  Conv{}       # the conv (reads the windows, writes m.q / m.k / m.v / m.seq, conv_out)
  Gemv{}       # KS 0: the per-warp GEMV (writes m.ba)
  KsFma{}      # KS > 0: the partial FMAs
  KsTree{}     # KS > 0: the shfl trees
  PartW{}      # KS > 0: lane 0 writes ks_part (m.dot2)
  Bar{}        # __syncthreads()
  Arrive{}     # non-owner conv_sync arrival
  WinV{}       # v-window write-back
  PartR{}      # KS > 0: thread t < S reads ks_part; KS 0: reads m.ba (beta/g)
  L2{}         # gdn_rule_tokens: q/k l2 norms
  Dot2W{}      # gdn_rule_tokens: token loop, writes m.dot1 / m.dot2

def when(c: Bool, xs: List<&2, Ev>) -> List<&2, Ev>:
  match c:
    case True{}:
      xs
    case False{}:
      Nil{}

def prog(+ks: Nat, +own: Bool) -> List<&2, Ev>:
  List.concat(&2, Ev,
    when(Bool.not(Nat.is_eq(ks, 2n)), State{} <> Nil{}) <>
    when(Nat.is_eq(ks, 2n), KsLoad{} <> Nil{}) <>
    (NormOps{} <> Conv{} <> Nil{}) <>
    when(Nat.is_eq(ks, 1n), KsLoad{} <> Nil{}) <>
    when(Nat.is_eq(ks, 2n), State{} <> Nil{}) <>
    when(Nat.is_eq(ks, 0n), Gemv{} <> Nil{}) <>
    when(Bool.not(Nat.is_eq(ks, 0n)), KsFma{} <> KsTree{} <> PartW{} <> Nil{}) <>
    (Bar{} <> Nil{}) <>
    when(Bool.not(own), Arrive{} <> Nil{}) <>
    (WinV{} <> PartR{} <> L2{} <> Bar{} <> Dot2W{} <> Nil{}) <>
    Nil{})
