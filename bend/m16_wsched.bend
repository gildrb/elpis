# Ext 8205: the ext 8201 fused-MLP and ext 8202 layer-tail schedule under the shared slot-weighted
# split-K partition (bend/gemm_m16_wpart.bend, ext 2105's formula), per phase: phase 0 (the tail's
# o_proj, weights a0 / b0), phase 1 (gate + up, a1 / b1), phase 2 (down, a2 / b2); block b < nsm has
# weight w0 (a*), b >= nsm weight w1 (b*). Append-only extension of bend/mlp_m16_sched.bend and
# bend/tail_m16_sched.bend: every quantity is the same expression with gemm_m16_partition's uniform
# start / nc replaced by gemm_m16_wpart's weighted start / nc (and the per-group first contributor /
# count the kernel now reads from the table instead of computing owner itself); the ext 8201 helpers
# that do not depend on the partition (ring slot, down pair, wait-list scan, event builders) are
# reused. At w0 == w1 every quantity is the uniform one (laws: m16_wsched_laws.bend and
# m16_wsched_tables_laws.bend). The host builder exllamav3_ext/quant/exl3_m16_wsched.h and the
# reference generator gen_sched.py emit the flat table printed by bend/M16_WSCHED_TABLE.bend;
# bend/m16_wsched_diff.py compares the three.
# Program order: ext 8204's deferred phase-1 publish (bend/mlp_m16_defer.bend), vperm = 0.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./gemm_m16_wpart.bend as Wp
import ./mlp_m16_sched.bend as Mlp
import ./mlp_m16_sched_spec.bend as MSpec
import ./tail_m16_sched.bend as Tail
import ./mlp_m16_defer.bend as Defer
import ./mlp_m16_defer_spec.bend as DSpec
import ./tail_m16_sched_spec.bend as TSpec

# ---- phase slices (one weighted partition per phase) ----

def s1(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +b: Nat) -> Nat:
  Wp.start(b, Mlp.total1(H, I), G, nsm, a1, b1)

def e1(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +b: Nat) -> Nat:
  Wp.start(1n+b, Mlp.total1(H, I), G, nsm, a1, b1)

def n1(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +b: Nat) -> Nat:
  Nat.sub(e1(G, nsm, H, I, a1, b1, b), s1(G, nsm, H, I, a1, b1, b))

def s2(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat) -> Nat:
  Wp.start(Mlp.slice(b), Mlp.total2(H, I), G, nsm, a2, b2)

def e2(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat) -> Nat:
  Wp.start(1n+Mlp.slice(b), Mlp.total2(H, I), G, nsm, a2, b2)

def n2(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat) -> Nat:
  Nat.sub(e2(G, nsm, H, I, a2, b2, b), s2(G, nsm, H, I, a2, b2, b))

def s0(+G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +a0: Nat, +b0: Nat, +b: Nat) -> Nat:
  Wp.start(b, Tail.total0(A, H), G, nsm, a0, b0)

def e0(+G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +a0: Nat, +b0: Nat, +b: Nat) -> Nat:
  Wp.start(1n+b, Tail.total0(A, H), G, nsm, a0, b0)

def n0(+G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +a0: Nat, +b0: Nat, +b: Nat) -> Nat:
  Nat.sub(e0(G, nsm, A, H, a0, b0, b), s0(G, nsm, A, H, a0, b0, b))

# ---- 8201 per block (mlp_m16_sched's definitions over the weighted slices) ----

def ring2(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +b: Nat) -> Nat:
  Mlp.slot(n1(G, nsm, H, I, a1, b1, b), Mlp.pf())

def fin_pair(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat) -> Nat:
  Mlp.pair_of(I, s2(G, nsm, H, I, a2, b2, b))

def fin_count(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +n: Nat, +p: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(fin_count(G, nsm, H, I, a2, b2, b, p),
        MSpec.bit(Nat.is_eq(fin_pair(G, nsm, H, I, a2, b2, b), p)))

def fin_rank(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat) -> Nat:
  fin_count(G, nsm, H, I, a2, b2, b, fin_pair(G, nsm, H, I, a2, b2, b))

def fin_cnt(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat) -> Nat:
  fin_count(G, nsm, H, I, a2, b2, G, fin_pair(G, nsm, H, I, a2, b2, b))

def waits(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat) -> List<&2, Nat>:
  Mlp.waits.go(I, n2(G, nsm, H, I, a2, b2, b), s2(G, nsm, H, I, a2, b2, b), Nil{})

def wait_cnt(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat) -> Nat:
  List.length(&2, Nat, waits(G, nsm, H, I, a2, b2, b))

def wait_off(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +b: Nat) -> Nat:
  match b:
    case 0n:
      0n
    case 1n+c:
      Nat.add(wait_off(G, nsm, H, I, a2, b2, c), wait_cnt(G, nsm, H, I, a2, b2, c))

# ---- per group (the kernel reads these from the table: slot index b - fc, contributors nc) ----

def fc1(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +g: Nat) -> Nat:
  Wp.first_contrib(g, Mlp.kt1(H), Mlp.total1(H, I), G, nsm, a1, b1)

def nc1(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +g: Nat) -> Nat:
  Wp.nc(g, Mlp.kt1(H), Mlp.total1(H, I), G, nsm, a1, b1)

def fc2(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +g: Nat) -> Nat:
  Wp.first_contrib(g, Mlp.kt2(I), Mlp.total2(H, I), G, nsm, a2, b2)

def nc2(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +g: Nat) -> Nat:
  Wp.nc(g, Mlp.kt2(I), Mlp.total2(H, I), G, nsm, a2, b2)

def fc0(+G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +a0: Nat, +b0: Nat, +g: Nat) -> Nat:
  Wp.first_contrib(g, Tail.kt0(A), Tail.total0(A, H), G, nsm, a0, b0)

def nc0(+G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +a0: Nat, +b0: Nat, +g: Nat) -> Nat:
  Wp.nc(g, Tail.kt0(A), Tail.total0(A, H), G, nsm, a0, b0)

def mc0(+G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +a0: Nat, +b0: Nat) -> Nat:
  Wp.max_contrib(Part.groups(1n, H), Tail.kt0(A), G, nsm, a0, b0)

def mc1(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat) -> Nat:
  Wp.max_contrib(Part.groups(2n, I), Mlp.kt1(H), G, nsm, a1, b1)

def mc2(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat) -> Nat:
  Wp.max_contrib(Part.groups(1n, H), Mlp.kt2(I), G, nsm, a2, b2)

# ---- per pair (counter targets; each warp of each contributor adds 1: 8 * nc) ----

def exp_gate(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +p: Nat) -> Nat:
  Nat.mul(8n, nc1(G, nsm, H, I, a1, b1, p))

def exp_up(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +p: Nat) -> Nat:
  Nat.mul(8n, nc1(G, nsm, H, I, a1, b1, Nat.add(Mlp.pairs(I), p)))

def fin_warps(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +p: Nat) -> Nat:
  Nat.mul(8n, fin_count(G, nsm, H, I, a2, b2, G, p))

def wait_blocks(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +n: Nat, +p: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(wait_blocks(G, nsm, H, I, a2, b2, b, p),
        MSpec.bit(MSpec.member(waits(G, nsm, H, I, a2, b2, b), p)))

def wait2(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +p: Nat) -> Nat:
  wait_blocks(G, nsm, H, I, a2, b2, G, p)

# ---- the tail's own per-block fields ----

def ring1(+G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +a0: Nat, +b0: Nat, +b: Nat) -> Nat:
  Mlp.slot(n0(G, nsm, A, H, a0, b0, b), Mlp.pf())

def tring2(+G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +I: Nat, +a0: Nat, +b0: Nat, +a1: Nat, +b1: Nat,
    +b: Nat) -> Nat:
  Mlp.slot(Nat.add(n0(G, nsm, A, H, a0, b0, b), n1(G, nsm, H, I, a1, b1, b)), Mlp.pf())

# ---- counter events of block b (8201's, over the weighted slices), and the 8204 program order ----

def mainloop1(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +b: Nat)
    -> List<&2, PSpec.Ev>:
  Part.mainloop(s1(G, nsm, H, I, a1, b1, b), e1(G, nsm, H, I, a1, b1, b), Mlp.kt1(H))

def events(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +b: Nat)
    -> List<&2, MSpec.Ev>:
  Mlp.sigs1(mainloop1(G, nsm, H, I, a1, b1, b),
    Mlp.finish(Mlp.pairs(I), fin_pair(G, nsm, H, I, a2, b2, b),
      Mlp.waits2(waits(G, nsm, H, I, a2, b2, b))))

# ext 8204's program: the whole phase-1 main loop, then the block's counter events.
def program(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +b: Nat)
    -> List<&2, DSpec.Ev>:
  Defer.tag_work(mainloop1(G, nsm, H, I, a1, b1, b),
    Defer.tag_sync(events(G, nsm, H, I, a1, b1, a2, b2, b), Nil{}))

# Finish jobs of pair p for m token rows over blocks b < n (mlp_m16_sched's finisher_hits over the
# weighted finish pairs / ranks / counts).
def finisher_hits(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a2: Nat, +b2: Nat, +n: Nat, +p: Nat, +x: Nat,
    +m: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(finisher_hits(G, nsm, H, I, a2, b2, b, p, x, m),
        Nat.mul(MSpec.bit(Nat.is_eq(fin_pair(G, nsm, H, I, a2, b2, b), p)),
          Part.warp_hits(8n, fin_rank(G, nsm, H, I, a2, b2, b), x, fin_cnt(G, nsm, H, I, a2, b2, b),
            Nat.mul(4n, m))))

# ---- the m16 split-K workspace, in partial slots of EXL3_M16_SLOT_FLOATS floats ----
# exl3_mlp_m16.cu:262 ws_floats = (2 NP mc1 + NG2 mc2 + NG0 mc0) * EXL3_M16_SLOT_FLOATS, checked
# against the m16 workspace (fail closed); :369 ws2 = ws + 2 NP mc1 slots; exl3_tail_m16.cu:214
# ws0 = ws + ws1 + ws2. Phase 1 (gate + up, NG1 = 2 NP groups) owns slots [0, base2), phase 2 (down)
# [base2, base0), the tail's phase 0 (o_proj) [base0, ws_slots). Block b's partial of group g goes
# to region base + g * mc + (b - fc(g)) (Wp.address).
def base2(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat) -> Nat:
  Nat.mul(Part.groups(2n, I), mc1(G, nsm, H, I, a1, b1))

def base0(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat) -> Nat:
  Nat.add(base2(G, nsm, H, I, a1, b1), Nat.mul(Part.groups(1n, H), mc2(G, nsm, H, I, a2, b2)))

# The table header's mc0: 0 for kind 0 (standalone 8201 MLP), the phase-0 max_contrib for kind 1 (tail).
def mc0_of(kind: Nat, +G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +a0: Nat, +b0: Nat) -> Nat:
  match kind:
    case 0n:
      0n
    case 1n+k:
      mc0(G, nsm, A, H, a0, b0)

def ws_slots(kind: Nat, +G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +I: Nat, +a0: Nat, +b0: Nat, +a1: Nat,
    +b1: Nat, +a2: Nat, +b2: Nat) -> Nat:
  Nat.add(base0(G, nsm, H, I, a1, b1, a2, b2),
    Nat.mul(Part.groups(1n, H), mc0_of(kind, G, nsm, A, H, a0, b0)))

# ws_floats * sizeof(float), the left side of the host's workspace check.
def ws_bytes(kind: Nat, +G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +I: Nat, +a0: Nat, +b0: Nat, +a1: Nat,
    +b1: Nat, +a2: Nat, +b2: Nat) -> Nat:
  Nat.mul(Nat.mul(ws_slots(kind, G, nsm, A, H, I, a0, b0, a1, b1, a2, b2), Wp.slot_floats()), 4n)

def slot1(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +g: Nat, +b: Nat) -> Nat:
  Wp.address(g, mc1(G, nsm, H, I, a1, b1), b, fc1(G, nsm, H, I, a1, b1, g))

def slot2(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +g: Nat,
    +b: Nat) -> Nat:
  Nat.add(base2(G, nsm, H, I, a1, b1),
    Wp.address(g, mc2(G, nsm, H, I, a2, b2), b, fc2(G, nsm, H, I, a2, b2, g)))

def slot0(+G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +I: Nat, +a0: Nat, +b0: Nat, +a1: Nat, +b1: Nat,
    +a2: Nat, +b2: Nat, +g: Nat, +b: Nat) -> Nat:
  Nat.add(base0(G, nsm, H, I, a1, b1, a2, b2),
    Wp.address(g, mc0(G, nsm, A, H, a0, b0), b, fc0(G, nsm, A, H, a0, b0, g)))

# ---- the tail (kind 1) program of block b for m token rows ----
# tail_m16_sched's event list over the weighted phase-0 slice and the weighted 8201 counter events:
# barrier S, the phase-0 main loop, A, the F0 jobs, B, the N jobs, C, the counter events, D.
def tevents(+G: Nat, +nsm: Nat, +A: Nat, +H: Nat, +I: Nat, +m: Nat, +a0: Nat, +b0: Nat, +a1: Nat,
    +b1: Nat, +a2: Nat, +b2: Nat, +b: Nat) -> List<&2, TSpec.Ev>:
  TSpec.Bar{0n} <> Tail.tag_work(Part.mainloop(s0(G, nsm, A, H, a0, b0, b), e0(G, nsm, A, H, a0, b0, b),
    Tail.kt0(A)),
    TSpec.Bar{1n} <> Tail.tag_fin(Tail.warp_jobs(G, Tail.jobs0(H, m), b),
      TSpec.Bar{2n} <> Tail.tag_norm(Tail.warp_jobs(G, Tail.jobsn(H, m), b),
        TSpec.Bar{3n} <> Tail.tag_sync(events(G, nsm, H, I, a1, b1, a2, b2, b), [TSpec.Bar{4n}]))))
