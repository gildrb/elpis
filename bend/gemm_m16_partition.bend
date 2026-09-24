# Work partition of the EXL3 m16 swap-AB GEMM, patch 2001 v2 (patches/exl3-ext/
# 2001-gemm-m16-swapab.patch, sha256 0da35574..., the revision committed at 03e72ca), transcribed
# from the CUDA integer expressions over Nat. K = exllamav3_ext/quant/exl3_gemm_m16_kernel.cuh,
# H = exllamav3_ext/quant/exl3_gemm_m16.cu (post-patch line numbers).
# C `int` arithmetic on the non-negative values used here is Nat arithmetic while no product
# overflows (the kernel widens b * total and (x + 1) * G to int64); `>> 4` is `/ 16`, `& 1` / `& 3`
# are `% 2` / `% 4` and `>> 1` / `>> 2` are `/ 2` / `/ 4` on non-negative ints. The partition
# functions are generic in KT, total and G (a later static/dynamic split reuses them with other
# iteration counts). The independent reference is gemm_m16_partition_spec.bend; the laws are
# gemm_m16_partition_laws.bend.
import Base
import ./gemm_m16_partition_spec.bend as Spec

# K:117 KT = size_k >> 4 (16-deep k-tiles); H:180 KT = size_k / 16
def kt(k: Nat) -> Nat:
  Nat.div(k, 16n)

# K:119 NG = size_n / GW with GW = EXL3_M16_GW = 8 * 4 * 16 = 512 (K:35-37): 512-column groups
def ng(n: Nat) -> Nat:
  Nat.div(n, 512n)

# K:120 groups = p.num_mats * NG (H:181 num_mats * (size_n / EXL3_M16_GW))
def groups(mats: Nat, n: Nat) -> Nat:
  Nat.mul(mats, ng(n))

# K:121 total = groups * KT (H:182); iteration x = group * KT + k-tile
def total(mats: Nat, n: Nat, k: Nat) -> Nat:
  Nat.mul(groups(mats, n), kt(k))

# K:124 s_b = (int64) b * total / G; K:125 e_b = start(b + 1)
def start(b: Nat, +total: Nat, G: Nat) -> Nat:
  Nat.div(Nat.mul(b, total), G)

# K:72-75 (= H:80-83) owner(x, total, G) = ((int64) x + 1) * G + total - 1) / total - 1
def owner(x: Nat, +total: Nat, +G: Nat) -> Nat:
  Nat.sub(Nat.div(Nat.sub(Nat.add(Nat.mul(1n+x, G), total), 1n), total), 1n)

# K:280 seg_end = min(e_b, (g_cur + 1) * KT) - s_b (block-relative)
def seg_end(+s: Nat, +e: Nat, +g: Nat, +KT: Nat) -> Nat:
  Nat.sub(Nat.min(e, Nat.mul(1n+g, KT)), s)

# K:282-340: for (; j < seg_end; ++j) the body consumes iteration it = s_b + j of group g_cur
# (weights from the ring, activations from K:169-175, MMA into this group's accumulators);
# `left` = seg_end - j. `rest` is what the kernel does after the inner loop.
def inner(left: Nat, +s: Nat, +g: Nat, +j: Nat, rest: List<&2, Spec.Ev>) -> List<&2, Spec.Ev>:
  match left:
    case 0n:
      rest
    case 1n+l:
      Spec.Tile{g, Nat.add(s, j)} <> inner(l, s, g, 1n+j, rest)

# K:278 for (int g_cur = s_b / KT; j < n_iter; ++g_cur), n_iter = e_b - s_b (K:126); `go` is the
# loop condition j < n_iter. Each iteration runs the K:283 inner loop, then K:343-344
# fold(); flush(g_cur); the inner loop leaves j = max(j, seg_end). `fuel` bounds the number of
# outer iterations of this model only (the kernel has none); the law mainloop_trace shows the
# chosen fuel never cuts the loop short.
def outer(fuel: Nat, go: Bool, +s: Nat, +e: Nat, +KT: Nat, +g: Nat, +j: Nat)
    -> List<&2, Spec.Ev>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match go:
        case True{}:
          +j2 = Nat.max(j, seg_end(s, e, g, KT))
          inner(Nat.sub(seg_end(s, e, g, KT), j), s, g, j,
            Spec.Flush{g} <> outer(f, Nat.is_lt(j2, Nat.sub(e, s)), s, e, KT, 1n+g, j2))
        case False{}:
          Nil{}

# The whole main loop of block range [s, e) (K:275-346), starting at j = 0 (K:277).
def mainloop(+s: Nat, +e: Nat, +KT: Nat) -> List<&2, Spec.Ev>:
  outer(1n+Nat.sub(e, s), Nat.is_lt(0n, Nat.sub(e, s)), s, e, KT, Nat.div(s, KT), 0n)

type Cursor is Data:
  Cursor{g: Nat, kt: Nat}

# K:141-142 (and K:170-171): g = it / KT; kt = it - g * KT
def decode(+it: Nat, +KT: Nat) -> Cursor:
  Cursor{Nat.div(it, KT), Nat.sub(it, Nat.mul(Nat.div(it, KT), KT))}

def advance.pick(wrap: Bool, g: Nat, kt: Nat) -> Cursor:
  match wrap:
    case True{}:
      Cursor{1n+g, 0n}
    case False{}:
      Cursor{g, kt}

# K:147-151: one weight issue: if (++iss_kt == KT) { iss_kt = 0; iss_g++; }
def advance(c: Cursor, +KT: Nat) -> Cursor:
  match c:
    case Cursor{g, kt}:
      +k1: Nat = 1n+kt
      advance.pick(Nat.is_eq(k1, KT), g, k1)

# The issue cursor after j issues from its K:141-142 start decode(s_b).
def issued(j: Nat, +s: Nat, +KT: Nat) -> Cursor:
  match j:
    case 0n:
      decode(s, KT)
    case 1n+i:
      advance(issued(i, s, KT), KT)

# K:259 + K:268: group column of warp w's partial element with n-tile t < 4 (K:261), c >> 1 = h
# (K:268 (c >> 1) * 8) and lane >> 2 = q (K:259): w * 64 + t * 16 + h * 8 + q.
def col(w: Nat, t: Nat, h: Nat, +q: Nat) -> Nat:
  Nat.add(Nat.add(Nat.add(Nat.mul(w, 64n), Nat.mul(t, 16n)), Nat.mul(h, 8n)), q)

# K:138: weight n-tile of warp w's tile t inside the group: warp * EXL3_M16_TILES_W + t
def wtile(w: Nat, t: Nat) -> Nat:
  Nat.add(Nat.mul(w, 4n), t)

# K:267: row = mt * 8 + 2 * (lane & 3) + (c & 1)
def row(mt: Nat, a: Nat, c1: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(mt, 8n), Nat.mul(2n, a)), c1)

# K:356-357: CH = GW / 128 = 4 column chunks; jobs = groups * size_m * CH
def jobs(groups: Nat, m: Nat) -> Nat:
  Nat.mul(Nat.mul(groups, m), 4n)

# K:358: for (w = warp + EXL3_M16_WARPS * b; w < jobs; w += EXL3_M16_WARPS * G): the jobs of one
# (block, warp); `go` is the loop condition w < jobs. `fuel` bounds the model's iterations only:
# jobloop passes jobs + 1, enough since each step adds 8 * G >= 1 (law finish_jobs_once).
def jobloop.go(fuel: Nat, go: Bool, +x: Nat, +step: Nat, +jobs: Nat) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match go:
        case True{}:
          x <> jobloop.go(f, Nat.is_lt(Nat.add(x, step), jobs), Nat.add(x, step), step, jobs)
        case False{}:
          Nil{}

def jobloop(+b: Nat, +w: Nat, +G: Nat, +jobs: Nat) -> List<&2, Nat>:
  jobloop.go(1n+jobs, Nat.is_lt(Nat.add(w, Nat.mul(8n, b)), jobs), Nat.add(w, Nat.mul(8n, b)),
    Nat.mul(8n, G), jobs)

def warp_hits(+count: Nat, +b: Nat, +x: Nat, +G: Nat, +jobs: Nat) -> Nat:
  match count:
    case 0n:
      0n
    case 1n+w:
      Nat.add(warp_hits(w, b, x, G, jobs), Spec.bit(Spec.member(jobloop(b, w, G, jobs), x)))

# Number of (block b < count, warp w < EXL3_M16_WARPS = 8) whose K:358 loop visits job x.
def job_hits(+count: Nat, +x: Nat, +G: Nat, +jobs: Nat) -> Nat:
  match count:
    case 0n:
      0n
    case 1n+b:
      Nat.add(job_hits(b, x, G, jobs), warp_hits(8n, b, x, G, jobs))

# K:360-363: g = w / (size_m * CH); rem = w - g * size_m * CH; r = rem / CH; ch = rem - r * CH
def job(+x: Nat, +m: Nat) -> Spec.Job:
  +g = Nat.div(x, Nat.mul(m, 4n))
  +rem = Nat.sub(x, Nat.mul(Nat.mul(g, m), 4n))
  +r = Nat.div(rem, 4n)
  Spec.Job{g, r, Nat.sub(rem, Nat.mul(r, 4n))}

# K:258 cidx base b_lo = owner(g * KT, total, G) (also K:364)
def b_lo(g: Nat, +KT: Nat, +total: Nat, +G: Nat) -> Nat:
  owner(Nat.mul(g, KT), total, G)

# K:364 b_hi = owner((g + 1) * KT - 1, total, G)
def b_hi(g: Nat, +KT: Nat, +total: Nat, +G: Nat) -> Nat:
  owner(Nat.sub(Nat.mul(1n+g, KT), 1n), total, G)

# K:364 nc = b_hi - b_lo + 1 (H:187 same expression)
def nc(+g: Nat, +KT: Nat, +total: Nat, +G: Nat) -> Nat:
  Nat.add(Nat.sub(b_hi(g, KT, total, G), b_lo(g, KT, total, G)), 1n)

# K:258-259: partial slot of block b for group g: g * max_contrib + (b - b_lo)
def address(g: Nat, +mc: Nat, b: Nat, lo: Nat) -> Nat:
  Nat.add(Nat.mul(g, mc), Nat.sub(b, lo))

def max_contrib.pick(bigger: Bool, n: Nat, mc: Nat) -> Nat:
  match bigger:
    case True{}:
      n
    case False{}:
      mc

# H:184-189: max_contrib = 1; for g in [0, groups): nc = owner((g+1)*KT-1) - owner(g*KT) + 1;
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

# K:343-344 / K:256-270: a contributor b flushes its partial into its group slot b - b_lo
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

# Before the grid.sync (K:350) the contributors' flushes land in any order; each stores
# Part{b} at b - lo.
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

# K:365-371: after the grid.sync the finishing warp reads slot 0, then adds slots 1 .. nc - 1 in
# slot order (v = slot 0; for c = 1; c < nc; ++c: v += slot c). It uses neither the order in
# which the partials were written nor which warp finishes.
def finish(+ws: List<&2, Spec.Sum>, cnt: Nat) -> Spec.Sum:
  finish.go(Nat.sub(cnt, 1n), 1n, slot_at(ws, 0n), ws)
