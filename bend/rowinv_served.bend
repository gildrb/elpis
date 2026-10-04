# Served instance of the ~rinv link (generic model: rowinv_link.bend; laws: rowinv_served_laws.bend).
# It fixes, for the served verify forward, the three things rowinv_link.bend leaves open, each
# built from the existing Bend model of the kernel family that determines it:
#   - the round shapes and their paths: Chain{} (cs12 chain rounds, row r = the r-th draft, path
#     0 .. r) and Tree{q1..q7} (the 8-row tree of ext 9008 / 3012 / 5109, parent q_r of row r,
#     path = gdn_tree_spec.path = root, ancestors by depth, the row);
#   - the per-layer gathers: chain rounds fold in-round rows 0 .. r - 1 (3006 attention causal
#     bound, the GDN verify scan); tree rounds use, in full-attention layers (l mod 4 == 3), the
#     stash rows of the admitting 3012 pass at in-round columns base .. base + depth - 1
#     (attn_tree.bend path[leaf_of[r]][j]) and, in GDN layers, the state history the 5109 program
#     emits row r from (gdn_tree.bend run), without its last (own) step;
#   - the kernel plan of every layer launch (Plan): the RoPE / causal position; the 3006 combine
#     order and tile plan (attn_stride.bend) over the host's split grid grid_S (3006 bc_attn.py
#     av_splits, source link rinv_grid_diff.py); the split-K finisher sum of every group of every
#     weighted m16 / m16g / 8201 / tail GEMM (gemm_m16_wpart.bend contributor ranges, the
#     gemm_m16_partition.bend finisher over the barrier protocol below); the 8205 tail main-loop
#     program of every block (m16_wsched.bend tevents); the 5106 b/a GEMV value of every head
#     (gdn_ba_ksplit.bend task), relabelled to the row's own operands; the head plan (lmhead.bend
#     hp_head: final norm width, the stock lm_head row schedule through the persisted autotune
#     records, the fused greedy argmax split).
# Configuration values (SMs, kv heads, shapes, weights, descriptor list) are a Cfg. The split-K
# barrier protocol of a group g (contributors = the blocks b < G whose slice touches g, i.e. its
# flushes): the hardware interleaves the contributors' flush + counter-add sequences in any order,
# modelled as the scheduler's choice arr(m, lo, nc) of insertion indices (every order of the
# contributors arises from some index list, rowinv_served_laws.perm_reach_step: insert the k-th
# contributor at its index among the k - 1 earlier ones); the finisher reads after its counter
# reaches 8 * nc (seen); the group's workspace region holds max_contrib slots of arbitrary stale
# contents wsi(m, mc) (fill).
# This is a proof model (lists), not a shipped artifact.
import Base
import ./rowinv_link.bend as Link
import ./attn_stride.bend as Stride
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./gemm_m16_wpart.bend as Wp
import ./m16_wsched.bend as Ws
import ./tail_m16_sched_spec.bend as TSpec
import ./gdn_ba_ksplit.bend as Ba
import ./gemm_m16_wpart_spec.bend as WSpec
import ./lmhead.bend as Lm
import ./attn_tree.bend as AtI
import ./attn_tree_spec.bend as AtS
import ./gdn_tree.bend as GtI
import ./gdn_tree_spec.bend as GtS
import ./spec_inv_tree.bend as SIT

# ---------------------------------------------------------------- configuration

# One split-K GEMM launch shape: k-tiles per group, grid, SMs, slot weights, group count (the
# weighted partition of gemm_m16_wpart.bend over total = groups * KT iterations, gemm_m16_partition
# K:120-121 / H:182; equal weights = 2001 v2).
type GDesc is Data:
  GDesc{KT: Nat, G: Nat, nsm: Nat, w0: Nat, w1: Nat, groups: Nat}

# sms, kvh: the device's SM count and the layer's kv heads (3006 split grid grid_S); tail (8202 /
# 8205): grid, SMs, o_proj K, hidden, intermediate, the three phase weights; b/a GEMV: k / 2, heads,
# bias present; head: hidden size, vocabulary bound; the split-K GEMM launches of a layer.
type Cfg is Data:
  Cfg{sms: Nat, kvh: Nat, tG: Nat, tnsm: Nat, tA: Nat, tH: Nat, tI: Nat, a0: Nat, b0: Nat, a1: Nat, b1: Nat, a2: Nat,
    b2: Nat, bk2: Nat, bH: Nat, bhb: Bool, hdim: Nat, vsize: Nat, gemms: List<&2, GDesc>}

# patches/exl3-ext/3006-attn-verify-stride.patch:738 (modules/attention_fn/bc_attn.py; no later patch
# of the series changes it, rinv_grid_diff.py): av_splits = max(1, _get_sm_count(dev) // kvh).
# (Python's // raises for kvh = 0, where Nat.div gives 0: that host call never returns a grid.)
def grid_S(+sms: Nat, +kvh: Nat) -> Nat:
  Nat.max(1n, Nat.div(sms, kvh))

# The host guard of every split-K descriptor (what the host guarantees before it launches): at least
# one k-tile per group (KT = size_k / 16, size_k >= 16) and the weighted partition's guard
# gemm_m16_wpart.weights_valid (2105 H:103-109: positive weights, nsm <= G <= 2 nsm, every slice
# non-empty) over total = groups * KT.
def gdesc_ok(gs: List<&2, GDesc>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case GDesc{+KT, +G, +nsm, +w0, +w1, +groups} <> rest:
      Bool.and(Bool.and(Nat.is_lt(0n, KT), Wp.weights_valid(Nat.mul(groups, KT), G, nsm, w0, w1)), gdesc_ok(rest))

def cfg_ok(c: Cfg) -> Bool:
  match c:
    case Cfg{sms, kvh, tG, tnsm, tA, tH, tI, a0, b0, a1, b1, a2, b2, bk2, bH, bhb, hdim, vsize, gemms}:
      gdesc_ok(gemms)

# ---------------------------------------------------------------- shapes, paths, gathers

type Shape is Data:
  Chain{}
  Tree{q1: Nat, q2: Nat, q3: Nat, q4: Nat, q5: Nat, q6: Nat, q7: Nat}

# s, s + 1, .., s + k - 1
def seqn(k: Nat, +s: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      s <> seqn(k1, 1n+s)

def pth(sh: Shape, r: Nat) -> List<&2, Nat>:
  match sh:
    case Chain{}:
      seqn(1n+r, 0n)
    case Tree{q1, q2, q3, q4, q5, q6, q7}:
      GtS.path([0n, q1, q2, q3, q4, q5, q6, q7], r)

# Qwen3.x hybrid layout: layers 3, 7, .., 63 are full attention (16), the others GDN (48).
def is_attn(+l: Nat) -> Bool:
  Nat.is_eq(Nat.mod(l, 4n), 3n)

def pick_l(b: Bool, +x: List<&2, Nat>, +y: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      x
    case False{}:
      y

# 3012: in-round column base + j (j < depth[r]) of the pass admitting row r (leaf_of[r]) holds
# stash row path[leaf_of[r]][j].
def agather(k: Nat, +j: Nat, +d: AtI.TreeDesc, +r: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      AtI.path(d, AtI.leaf_of(d, r), j) <> agather(k1, 1n+j, d, r)

def attn_gather(+ps: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  agather(AtI.depth(AtS.desc(ps), r), 0n, AtS.desc(ps), r)

# 5109: the state history the program emits row r from (the rows whose rule steps were applied,
# the row's own last).
def hist(+r: Nat, outs: List<&2, GtI.Out>) -> List<&2, Nat>:
  match outs:
    case Nil{}:
      Nil{}
    case GtI.Out{+x, +h} <> rest:
      GtS.sel_l(Nat.is_eq(x, r), h, hist(r, rest))

def outs_of(w: GtI.W) -> List<&2, GtI.Out>:
  match w:
    case GtI.W{h, s, o, b}:
      o

def init(+xs: List<&2, Nat>) -> List<&2, Nat>:
  List.take(&2, Nat, xs, Nat.sub(List.length(&2, Nat, xs), 1n))

def gdn_gather(+par: List<&2, Nat>, +r: Nat) -> List<&2, Nat>:
  init(hist(r, outs_of(GtI.run(par))))

def gat(l: Nat, sh: Shape, r: Nat) -> List<&2, Nat>:
  match sh:
    case Chain{}:
      seqn(r, 0n)
    case Tree{+q1, +q2, +q3, +q4, +q5, +q6, +q7}:
      +r = r
      pick_l(is_attn(l), attn_gather([q1, q2, q3, q4, q5, q6, q7], r),
        gdn_gather([0n, q1, q2, q3, q4, q5, q6, q7], r))

# Admitted rounds: a chain round has >= 1 row; a tree round is a legal 8-row shape.
def ok(sh: Shape, m: Nat) -> Bool:
  match sh:
    case Chain{}:
      Nat.is_lt(0n, m)
    case Tree{q1, q2, q3, q4, q5, q6, q7}:
      Bool.and(AtS.legal(q1, q2, q3, q4, q5, q6, q7), Nat.is_eq(m, 8n))

# ---------------------------------------------------------------- split-K barrier protocol

# Every block in an arrival order is >= lo.
def arr_only(order: List<&2, Nat>, +lo: Nat) -> Bool:
  match order:
    case Nil{}:
      True{}
    case +a <> rest:
      Bool.and(Nat.is_le(lo, a), arr_only(rest, lo))

# Blocks b .. b + k - 1 have all arrived.
def arr_all(k: Nat, +b: Nat, +order: List<&2, Nat>) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+k1:
      Bool.and(PSpec.arrived(order, b), arr_all(k1, 1n+b, order))

# The ascending fold v + Part{b} + Part{b + 1} + .. (k terms), and the fold of the contributors
# lo .. lo + nc - 1 from Part{lo}.
def asc.go(k: Nat, +b: Nat, v: PSpec.Sum) -> PSpec.Sum:
  match k:
    case 0n:
      v
    case 1n+k1:
      asc.go(k1, 1n+b, PSpec.Add{v, PSpec.Part{b}})

def asc(nc: Nat, +lo: Nat) -> PSpec.Sum:
  asc.go(Nat.sub(nc, 1n), 1n+lo, PSpec.Part{lo})

# The contributors of group g among blocks b .. b + k - 1, ascending: the blocks whose slice touches g
# (gemm_m16_wpart_spec.touches; the kernel's slice [start(b), start(b + 1)) is the spec's owned set,
# gemm_m16_wpart_laws.range_is_owned). Each flushes its partial of g once, into slot b - first_contrib(g)
# (2105 K:279-280; 8201 / 8205 the same slots).
def keep(c: Bool, +b: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case True{}:
      b <> rest
    case False{}:
      rest

def contribs(k: Nat, +b: Nat, +g: Nat, +KT: Nat, +total: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      keep(WSpec.touches(b, g, KT, total, G, nsm, w0, w1), b, contribs(k1, 1n+b, g, KT, total, G, nsm, w0, w1))

# Insert x at index i of xs (at the end when i >= |xs|).
def ins_at(xs: List<&2, Nat>, +i: Nat, +x: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      [x]
    case +y <> rest:
      match i:
        case 0n:
          x <> y <> rest
        case 1n+j:
          y <> ins_at(rest, j, x)

def ix_hd(ix: List<&2, Nat>) -> Nat:
  match ix:
    case Nil{}:
      0n
    case i <> rest:
      i

def ix_tl(ix: List<&2, Nat>) -> List<&2, Nat>:
  match ix:
    case Nil{}:
      Nil{}
    case i <> rest:
      rest

# The arrival order chosen by the scheduler's insertion indices ix: the contributors cs in turn, each
# inserted at its index into the order of the earlier ones (acc). The flushes of different blocks are
# not ordered by anything in the kernel; every order of cs is perm(cs, ix, []) for some ix (laws: perm_reach_step).
def perm(cs: List<&2, Nat>, +ix: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      acc
    case +c <> rest:
      perm(rest, ix_tl(ix), ins_at(acc, ix_hd(ix), c))

def seen.cut(go: Bool, xs: List<&2, Nat>) -> List<&2, Nat>:
  match go:
    case True{}:
      xs
    case False{}:
      Nil{}

# Counter barrier (8201 cnt1[g]): after flushing group g each of a contributor's 8 warps adds 1 to the
# group's counter (__threadfence; __syncwarp; atomicAdd: 8201 patch:745; "expected 8 * contributors",
# patch:364-365), and the finisher block's poller waits until the counter reaches that target
# (exl3_mlp_wait, patch:848-849) before its warps read the slots. The flushes the finisher observes
# (H_mem): the arrivals in order up to the one whose adds bring the counter from cnt to the target.
# (2102 / 2105 m16g finish after grid.sync(), 2102 patch:771 / 2105 patch:353: every block, in
# particular every contributor, has arrived: the same observation.)
def seen(order: List<&2, Nat>, +cnt: Nat, +target: Nat) -> List<&2, Nat>:
  match order:
    case Nil{}:
      Nil{}
    case +b <> rest:
      b <> seen.cut(Nat.is_lt(Nat.add(cnt, 8n), target), seen(rest, Nat.add(cnt, 8n), target))

# The group's workspace region: max_contrib slots (2105 K:279-280 address g * max_contrib + slot, H:144
# sized groups * max_contrib) holding arbitrary stale contents ws (slots past ws: Part{0}).
def fill(k: Nat, ws: List<&2, PSpec.Sum>) -> List<&2, PSpec.Sum>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      match ws:
        case Nil{}:
          PSpec.Part{0n} <> fill(k1, Nil{})
        case w <> rest:
          w <> fill(k1, rest)

# ---------------------------------------------------------------- the plan of a layer launch

# 3006 tile plan of query row qp: kv positions p0 .. p0 + k - 1 of tile iteration it of CTA x
def tiles_p(k: Nat, +p0: Nat, +x: Nat, +it: Nat, +L: Nat, +S: Nat, +q: Nat, +qp: Nat) -> List<&2, Nat>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      Stride.tile_hits(x, it, p0, L, S, q, qp) <> tiles_p(k1, 1n+p0, x, it, L, S, q, qp)

def tiles_it(k: Nat, +it0: Nat, +x: Nat, +L: Nat, +S: Nat, +q: Nat, +qp: Nat, +A1: Nat) -> List<&2, List<&2, Nat>>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      tiles_p(A1, 0n, x, it0, L, S, q, qp) <> tiles_it(k1, 1n+it0, x, L, S, q, qp, A1)

def tiles_x(k: Nat, +x0: Nat, +L: Nat, +S: Nat, +q: Nat, +qp: Nat, +A1: Nat) -> List<&2, List<&2, List<&2, Nat>>>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      tiles_it(A1, 0n, x0, L, S, q, qp, A1) <> tiles_x(k1, 1n+x0, L, S, q, qp, A1)

# The split-K finisher sum of group g (first contributor lo, nc = the host's contributor count, mc =
# max_contrib, cs = the contributors): the slots as the finisher reads them after the barrier, from
# the stale region, written by the observed arrivals of the scheduler's order.
def fin_g(~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, +m: Nat, +lo: Nat,
    +nc: Nat, +mc: Nat, cs: List<&2, Nat>) -> PSpec.Sum:
  Part.finish(Part.arrive(seen(perm(cs, arr(m, lo, nc), Nil{}), 0n, Nat.mul(nc, 8n)), fill(mc, wsi(m, mc)), lo), nc)

def kgroups(~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, k: Nat, +g: Nat,
    +KT: Nat, +G: Nat, +nsm: Nat, +w0: Nat, +w1: Nat, +groups: Nat, +m: Nat) -> List<&2, PSpec.Sum>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      fin_g(~arr, ~wsi, m, Wp.first_contrib(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1), Wp.nc(g, KT, Nat.mul(groups, KT), G, nsm, w0, w1),
        Wp.max_contrib(groups, KT, G, nsm, w0, w1), contribs(G, 0n, g, KT, Nat.mul(groups, KT), G, nsm, w0, w1)) <>
        kgroups(~arr, ~wsi, k1, 1n+g, KT, G, nsm, w0, w1, groups, m)

def ksum(~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, gs: List<&2, GDesc>,
    +m: Nat) -> List<&2, PSpec.Sum>:
  match gs:
    case Nil{}:
      Nil{}
    case GDesc{+KT, +G, +nsm, +w0, +w1, +groups} <> rest:
      List.append(&2, PSpec.Sum, kgroups(~arr, ~wsi, groups, 0n, KT, G, nsm, w0, w1, groups, m), ksum(~arr, ~wsi, rest, m))

# 8205 tail: the phase-0 split-K main loop of blocks b .. b + k - 1
def tail_works(k: Nat, +b: Nat, +G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +I: Nat, +m: Nat, +a0: Nat, +b0: Nat,
    +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat) -> List<&2, List<&2, PSpec.Ev>>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      TSpec.works(Ws.tevents(G, nsm, A, H, I, m, a0, b0, a1, b1, a2, b2, b)) <>
        tail_works(k1, 1n+b, G, nsm, A, H, I, m, a0, b0, a1, b1, a2, b2)

# 5106: an fp32 expression with its x operand indices shifted down by off (the row's own x row
# becomes row 0: which row of the launch the operands come from is not part of the plan).
def unshift(e: Ba.Ex, +off: Nat) -> Ba.Ex:
  match e:
    case Ba.ZeroF{}:
      Ba.ZeroF{}
    case Ba.Fma{x2, w2, c, acc}:
      Ba.Fma{Nat.sub(x2, off), w2, c, unshift(acc, off)}
    case Ba.Add{a, b}:
      Ba.Add{unshift(a, off), unshift(b, off)}
    case Ba.Bias{v, o}:
      Ba.Bias{unshift(v, off), o}
    case Ba.Stale{q}:
      Ba.Stale{q}

def ba_tab(k: Nat, +h: Nat, +m: Nat, +r: Nat, +k2: Nat, +H: Nat, +hb: Bool) -> List<&2, Ba.Ex>:
  match k:
    case 0n:
      Nil{}
    case 1n+k1:
      unshift(Ba.task(m, r, 0n, k2, h, H, hb), Nat.mul(r, k2)) <> unshift(Ba.task(m, r, 1n, k2, h, H, hb), Nat.mul(r, k2)) <>
        ba_tab(k1, 1n+h, m, r, k2, H, hb)

type Plan is Data:
  Plan{pos: Nat, merged: List<&2, Nat>, tiles: List<&2, List<&2, List<&2, Nat>>>, ksum: List<&2, PSpec.Sum>,
    tail: List<&2, List<&2, PSpec.Ev>>, ba: List<&2, Ba.Ex>, head: Lm.HeadPlan}

# The plan of row r (logical depth d) of an m-row launch whose row 0 sits at base, in every layer and
# in the head (the lm_head call has K = 6, lmhead.served_tab the persisted records).
def plan_of(~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, c: Cfg, +base: Nat,
    +m: Nat, +r: Nat, +d: Nat) -> Plan:
  match c:
    case Cfg{+sms, +kvh, +tG, +tnsm, +tA, +tH, +tI, +a0, +b0, +a1, +b1, +a2, +b2, +bk2, +bH, +bhb, +hdim, +vsize, +gemms}:
      Plan{Nat.add(base, d), Stride.merged(Nat.add(base, m), grid_S(sms, kvh), m, d),
        tiles_x(grid_S(sms, kvh), 0n, Nat.add(base, m), grid_S(sms, kvh), m, d, 1n+Nat.add(base, d)),
        ksum(~arr, ~wsi, gemms, m),
        tail_works(tG, 0n, tG, tnsm, tA, tH, tI, m, a0, b0, a1, b1, a2, b2),
        ba_tab(bH, 0n, m, r, bk2, bH, bhb),
        Lm.hp_head(Lm.served_tab(), 6n, hdim, vsize, base, m, r, d)}

def plan(~cfg: Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>, l: Nat,
    base: Nat, m: Nat, r: Nat, d: Nat) -> Plan:
  plan_of(~arr, ~wsi, cfg, base, m, r, d)

# The head launch's plan of a row: the row's plan (its head field is the head's; the head kernels see
# no other field).
def hplan(~cfg: Cfg, ~arr: Nat -> Nat -> Nat -> List<&2, Nat>, ~wsi: Nat -> Nat -> List<&2, PSpec.Sum>,
    base: Nat, m: Nat, r: Nat, d: Nat) -> Plan:
  plan_of(~arr, ~wsi, cfg, base, m, r, d)

# ---------------------------------------------------------------- tree rounds of spec_inv_tree

# The row tokens of a tree round (row 0 = the anchor, rows 1..7 the drafted nodes) and its shape.
def tree_toks(+anchor: U32, t: SIT.Draft) -> List<&2, U32>:
  match t:
    case SIT.Draft{q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7}:
      [anchor, x1, x2, x3, x4, x5, x6, x7]

def tree_shape(t: SIT.Draft) -> Shape:
  match t:
    case SIT.Draft{q1, q2, q3, q4, q5, q6, q7, x1, x2, x3, x4, x5, x6, x7}:
      Tree{q1, q2, q3, q4, q5, q6, q7}
