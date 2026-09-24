# Schedule table of ext 8201 (persistent fused MLP, one cooperative launch): gate+up m16 GEMM
# (phase 1), silu(gate) * up finish jobs, down m16 GEMM (phase 2), no grid-wide barrier between
# the GEMMs. Nat model, generic in the grid G, the hidden size H (gate/up K1 = H, down N2 = H) and
# the intermediate size I (gate/up N1 = I, down K2 = I); the served instance G = 164, H = 5120,
# I = 17408, PF = 8 is fixed below and printed by bend/MLP_M16_SCHED_TABLE.bend. Both phases
# reuse the patch 2001 v2 partition (gemm_m16_partition.bend: start, nc, max_contrib, mainloop,
# warp_hits) unchanged. Laws: mlp_m16_sched_laws.bend.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./mlp_m16_sched_spec.bend as Spec

# Served instance: G = 164 blocks (82 SMs x 2), H = 5120, I = 17408, PF = 8 cp.async ring stages.
def grid() -> Nat:
  164n

def hidden() -> Nat:
  5120n

def inter() -> Nat:
  17408n

def pf() -> Nat:
  8n

# Phase 1: 2 matrices (gate, up) of K1 = H x N1 = I; phase 2: 1 matrix (down) of K2 = I x N2 = H.
def kt1(+H: Nat) -> Nat:
  Part.kt(H)

def kt2(+I: Nat) -> Nat:
  Part.kt(I)

def total1(+H: Nat, +I: Nat) -> Nat:
  Part.total(2n, I, H)

def total2(+H: Nat, +I: Nat) -> Nat:
  Part.total(1n, H, I)

# Pairs: gate group p + up group NP + p = down k-tiles [32 p, 32 p + 32), NP = I / 512.
def pairs(+I: Nat) -> Nat:
  Part.ng(I)

# Down k-tiles per pair: GW / 16 = 32.
def pkt() -> Nat:
  32n

# ---- per block ----

def s1(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  Part.start(b, total1(H, I), G)

def e1(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  Part.start(1n+b, total1(H, I), G)

def n1(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  Nat.sub(e1(G, H, I, b), s1(G, H, I, b))

# Phase-2 virtual slice of block b (identity permutation).
def slice(+b: Nat) -> Nat:
  b

def s2(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  Part.start(slice(b), total2(H, I), G)

def e2(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  Part.start(1n+slice(b), total2(H, I), G)

def n2(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  Nat.sub(e2(G, H, I, b), s2(G, H, I, b))

# Warp-private cp.async ring of pf stages; one stream of n1 + n2 tiles per block: tile i lives in
# slot i mod pf; the prologue issues tiles 0 .. pf - 2 before step 0, step j issues tile
# j + pf - 1 and then consumes tile j, so tile i is issued at step max(0, i - (pf - 1)).
def slot(+i: Nat, +pf: Nat) -> Nat:
  Nat.mod(i, pf)

def issue_step(+i: Nat, +pf: Nat) -> Nat:
  Nat.sub(i, Nat.sub(pf, 1n))

# Ring slot of the first phase-2 tile (stream tile n1).
def ring2(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  slot(n1(G, H, I, b), pf())

# Down pair of iteration it: (it mod KT2) / 32.
def pair_of(+I: Nat, +it: Nat) -> Nat:
  Nat.div(Nat.mod(it, kt2(I)), pkt())

# The finish pair of block b: the pair of the first iteration of its phase-2 slice.
def fin_pair(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  pair_of(I, s2(G, H, I, b))

# Number of blocks b < n with finish pair p.
def fin_count(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +p: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(fin_count(G, H, I, b, p), Spec.bit(Nat.is_eq(fin_pair(G, H, I, b), p)))

def fin_rank(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  fin_count(G, H, I, b, fin_pair(G, H, I, b))

# k_P of the block's finish pair.
def fin_cnt(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  fin_count(G, H, I, G, fin_pair(G, H, I, b))

def waits.pick(seen_it: Bool, +p: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match seen_it:
    case True{}:
      rest
    case False{}:
      p <> rest

# Distinct pairs of iterations it .. it + left - 1 not in `seen`, in first-touch order.
def waits.go(+I: Nat, left: Nat, +it: Nat, +seen: List<&2, Nat>) -> List<&2, Nat>:
  match left:
    case 0n:
      Nil{}
    case 1n+rest:
      +p = pair_of(I, it)
      waits.pick(Spec.member(seen, p), p, waits.go(I, rest, 1n+it, p <> seen))

# Wait list of block b: the distinct pairs of its phase-2 slice in first-touch order.
def waits(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> List<&2, Nat>:
  waits.go(I, n2(G, H, I, b), s2(G, H, I, b), Nil{})

def wait_cnt(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  List.length(&2, Nat, waits(G, H, I, b))

# Offset of block b's wait list in the concatenated wait array.
def wait_off(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> Nat:
  match b:
    case 0n:
      0n
    case 1n+c:
      Nat.add(wait_off(G, H, I, c), wait_cnt(G, H, I, c))

# ---- per pair ----

# Each of the 8 warps of each contributor block of group g release-adds 1 to cnt1[g].
def exp_gate(+G: Nat, +H: Nat, +I: Nat, +p: Nat) -> Nat:
  Nat.mul(8n, Part.nc(p, kt1(H), total1(H, I), G))

def exp_up(+G: Nat, +H: Nat, +I: Nat, +p: Nat) -> Nat:
  Nat.mul(8n, Part.nc(Nat.add(pairs(I), p), kt1(H), total1(H, I), G))

# 8 finisher warps per block with finish pair p: waiters on cnt1[p] and cnt1[NP + p], and
# signallers of cnt2[p].
def fin_warps(+G: Nat, +H: Nat, +I: Nat, +p: Nat) -> Nat:
  Nat.mul(8n, fin_count(G, H, I, G, p))

def wait1(+G: Nat, +H: Nat, +I: Nat, +p: Nat) -> Nat:
  fin_warps(G, H, I, p)

def exp2(+G: Nat, +H: Nat, +I: Nat, +p: Nat) -> Nat:
  fin_warps(G, H, I, p)

# Blocks b < n whose wait list contains p (thread 0 of each waits once on cnt2[p]).
def wait_blocks(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +p: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(wait_blocks(G, H, I, b, p), Spec.bit(Spec.member(waits(G, H, I, b), p)))

def wait2(+G: Nat, +H: Nat, +I: Nat, +p: Nat) -> Nat:
  wait_blocks(G, H, I, G, p)

def mc1(+G: Nat, +H: Nat, +I: Nat) -> Nat:
  Part.max_contrib(Part.groups(2n, I), kt1(H), total1(H, I), G)

def mc2(+G: Nat, +H: Nat, +I: Nat) -> Nat:
  Part.max_contrib(Part.groups(1n, H), kt2(I), total2(H, I), G)

# ---- synchronisation events of block b, in program order ----

# L0: phase-1 main loop; after flushing group g each of the 8 warps adds 1 to cnt1[g].
def sigs1(evs: List<&2, PSpec.Ev>, rest: List<&2, Spec.Ev>) -> List<&2, Spec.Ev>:
  match evs:
    case Nil{}:
      rest
    case ev <> more:
      match ev:
        case PSpec.Tile{g, it}:
          sigs1(more, rest)
        case PSpec.Flush{g}:
          Spec.Sig{Spec.C1{g}, 8n, 0n} <> sigs1(more, rest)

# L2: thread 0 waits once on cnt2[p] for each pair of the wait list, then the phase-2 loop.
def waits2(ws: List<&2, Nat>) -> List<&2, Spec.Ev>:
  match ws:
    case Nil{}:
      Nil{}
    case p <> rest:
      Spec.Wait{Spec.C2{p}, 1n, 2n} <> waits2(rest)

# L1: the finisher block waits on cnt1[p] and cnt1[NP + p] (thread 0 waits once per counter and
# counts 8 passes, one per warp, on its pass counter: "a wait" of mult 8), the 8 warps run the
# finish jobs, then each warp adds 1 to cnt2[p].
def finish(+np: Nat, +p: Nat, rest: List<&2, Spec.Ev>) -> List<&2, Spec.Ev>:
  Spec.Wait{Spec.C1{p}, 8n, 1n} <> Spec.Wait{Spec.C1{Nat.add(np, p)}, 8n, 1n} <>
    Spec.Sig{Spec.C2{p}, 8n, 1n} <> rest

def events(+G: Nat, +H: Nat, +I: Nat, +b: Nat) -> List<&2, Spec.Ev>:
  sigs1(Part.mainloop(s1(G, H, I, b), e1(G, H, I, b), kt1(H)),
    finish(pairs(I), fin_pair(G, H, I, b), waits2(waits(G, H, I, b))))

# Finish jobs of pair p for m token rows: finisher warp w of the block with finish rank r visits
# jobs f, f + 8 k, ... < 4 m with f = 8 r + w (k = k_p): the v2 finish loop with G := k and
# b := r (gemm_m16_partition jobloop / warp_hits). Visits of job x over blocks b < n.
def finisher_hits(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +p: Nat, +x: Nat, +m: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(finisher_hits(G, H, I, b, p, x, m),
        Nat.mul(Spec.bit(Nat.is_eq(fin_pair(G, H, I, b), p)),
          Part.warp_hits(8n, fin_rank(G, H, I, b), x, fin_cnt(G, H, I, b), Nat.mul(4n, m))))
