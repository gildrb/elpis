# Semantic obligations for ext 8205's slot-weighted 8201 / 8202 schedule model bend/m16_wsched.bend (the
# Nat model the host builder exl3_m16_wsched.h, gen_sched.py and bend/M16_WSCHED_TABLE.bend all emit;
# differential: bend/m16_wsched_diff.py). Append-only: they restate mlp_m16_sched's and tail_m16_sched's
# partition, slot, counter, level, wait-list and finish laws over the weighted slices of the shared
# partition bend/gemm_m16_wpart.bend, with ext 8204's deferred-publish program order, and state that
# equal weights are the existing (uniform) model. Generic in G, nsm, the shapes (A = o_proj K0, H, I)
# and the per-phase weights, under the host guard Wp.weights_valid of each phase used (the extension
# refuses other weights) and the shape hypotheses of the 8201 laws. No law evaluates the served
# default weights: the checker's Nat is unary and those products reach ~1e9; that the defaults pass
# the host guard is established by the host builder (fail closed) and bend/m16_wsched_diff.py. Every
# law is about the Bend model; the kernel's conformance to the table it reads is outside this contract.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./gemm_m16_wpart.bend as Wp
import ./gemm_m16_wpart_spec.bend as WSpec
import ./mlp_m16_sched.bend as Mlp
import ./mlp_m16_sched_spec.bend as MSpec
import ./mlp_m16_sched_laws.bend as MLaws
import ./tail_m16_sched.bend as Tail
import ./mlp_m16_defer_spec.bend as DSpec
import ./m16_wsched.bend as Impl

# Grid-wide totals over blocks 0 .. n - 1 of each block's counter events.
def sig_total(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +n: Nat,
    +c: MSpec.Ctr) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(sig_total(G, nsm, H, I, a1, b1, a2, b2, b, c),
        MSpec.sig_amount(Impl.events(G, nsm, H, I, a1, b1, a2, b2, b), c))

def wait_total(+G: Nat, +nsm: Nat, +H: Nat, +I: Nat, +a1: Nat, +b1: Nat, +a2: Nat, +b2: Nat, +n: Nat,
    +c: MSpec.Ctr) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(wait_total(G, nsm, H, I, a1, b1, a2, b2, b, c),
        MSpec.wait_amount(Impl.events(G, nsm, H, I, a1, b1, a2, b2, b), c))

# ---- (1) exactly-once coverage of the three phases under the weighted partition ----

law wphase1_slice_owned:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a1: Nat
  for +b1: Nat
  for +b: Nat
  for +x: Nat
  for valid: {Wp.weights_valid(Mlp.total1(H, I), G, nsm, a1, b1) == True{} : Bool}
  {Bool.and(Nat.is_le(Impl.s1(G, nsm, H, I, a1, b1, b), x),
      Nat.is_lt(x, Nat.add(Impl.s1(G, nsm, H, I, a1, b1, b), Impl.n1(G, nsm, H, I, a1, b1, b)))) ==
    WSpec.owns(b, x, Mlp.total1(H, I), G, nsm, a1, b1) : Bool}

law wphase1_exactly_once:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a1: Nat
  for +b1: Nat
  for +x: Nat
  for valid: {Wp.weights_valid(Mlp.total1(H, I), G, nsm, a1, b1) == True{} : Bool}
  for inside: {Nat.is_lt(x, Mlp.total1(H, I)) == True{} : Bool}
  {WSpec.owners(G, x, Mlp.total1(H, I), G, nsm, a1, b1) == 1n : Nat}

law wphase2_slice_owned:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a2: Nat
  for +b2: Nat
  for +b: Nat
  for +x: Nat
  for valid: {Wp.weights_valid(Mlp.total2(H, I), G, nsm, a2, b2) == True{} : Bool}
  {Bool.and(Nat.is_le(Impl.s2(G, nsm, H, I, a2, b2, b), x),
      Nat.is_lt(x, Nat.add(Impl.s2(G, nsm, H, I, a2, b2, b), Impl.n2(G, nsm, H, I, a2, b2, b)))) ==
    WSpec.owns(Mlp.slice(b), x, Mlp.total2(H, I), G, nsm, a2, b2) : Bool}

law wphase2_exactly_once:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a2: Nat
  for +b2: Nat
  for +x: Nat
  for valid: {Wp.weights_valid(Mlp.total2(H, I), G, nsm, a2, b2) == True{} : Bool}
  for inside: {Nat.is_lt(x, Mlp.total2(H, I)) == True{} : Bool}
  {WSpec.owners(G, x, Mlp.total2(H, I), G, nsm, a2, b2) == 1n : Nat}

law wphase0_slice_owned:
  for +G: Nat
  for +nsm: Nat
  for +A: Nat
  for +H: Nat
  for +a0: Nat
  for +b0: Nat
  for +b: Nat
  for +x: Nat
  for valid: {Wp.weights_valid(Tail.total0(A, H), G, nsm, a0, b0) == True{} : Bool}
  {Bool.and(Nat.is_le(Impl.s0(G, nsm, A, H, a0, b0, b), x),
      Nat.is_lt(x, Nat.add(Impl.s0(G, nsm, A, H, a0, b0, b), Impl.n0(G, nsm, A, H, a0, b0, b)))) ==
    WSpec.owns(b, x, Tail.total0(A, H), G, nsm, a0, b0) : Bool}

law wphase0_exactly_once:
  for +G: Nat
  for +nsm: Nat
  for +A: Nat
  for +H: Nat
  for +a0: Nat
  for +b0: Nat
  for +x: Nat
  for valid: {Wp.weights_valid(Tail.total0(A, H), G, nsm, a0, b0) == True{} : Bool}
  for inside: {Nat.is_lt(x, Tail.total0(A, H)) == True{} : Bool}
  {WSpec.owners(G, x, Tail.total0(A, H), G, nsm, a0, b0) == 1n : Nat}

# ---- (2) split-K slots: a contributor b of group g flushes into slot b - fc(g) < nc(g) <= mc ----

law wphase1_slots:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a1: Nat
  for +b1: Nat
  for +g: Nat
  for +b: Nat
  for valid: {Wp.weights_valid(Mlp.total1(H, I), G, nsm, a1, b1) == True{} : Bool}
  for shaped: {Nat.is_le(128n, H) == True{} : Bool}
  for group: {Nat.is_lt(g, Part.groups(2n, I)) == True{} : Bool}
  for contributor: {WSpec.touches(b, g, Mlp.kt1(H), Mlp.total1(H, I), G, nsm, a1, b1) == True{} : Bool}
  {Nat.is_le(Impl.fc1(G, nsm, H, I, a1, b1, g), b) == True{} : Bool} &
  {Nat.is_lt(Nat.sub(b, Impl.fc1(G, nsm, H, I, a1, b1, g)), Impl.nc1(G, nsm, H, I, a1, b1, g)) == True{} : Bool} &
  {Nat.is_le(Impl.nc1(G, nsm, H, I, a1, b1, g), Impl.mc1(G, nsm, H, I, a1, b1)) == True{} : Bool}

law wphase2_slots:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a2: Nat
  for +b2: Nat
  for +g: Nat
  for +b: Nat
  for valid: {Wp.weights_valid(Mlp.total2(H, I), G, nsm, a2, b2) == True{} : Bool}
  for shaped: {Nat.is_le(128n, I) == True{} : Bool}
  for group: {Nat.is_lt(g, Part.groups(1n, H)) == True{} : Bool}
  for contributor: {WSpec.touches(b, g, Mlp.kt2(I), Mlp.total2(H, I), G, nsm, a2, b2) == True{} : Bool}
  {Nat.is_le(Impl.fc2(G, nsm, H, I, a2, b2, g), b) == True{} : Bool} &
  {Nat.is_lt(Nat.sub(b, Impl.fc2(G, nsm, H, I, a2, b2, g)), Impl.nc2(G, nsm, H, I, a2, b2, g)) == True{} : Bool} &
  {Nat.is_le(Impl.nc2(G, nsm, H, I, a2, b2, g), Impl.mc2(G, nsm, H, I, a2, b2)) == True{} : Bool}

law wphase0_slots:
  for +G: Nat
  for +nsm: Nat
  for +A: Nat
  for +H: Nat
  for +a0: Nat
  for +b0: Nat
  for +g: Nat
  for +b: Nat
  for valid: {Wp.weights_valid(Tail.total0(A, H), G, nsm, a0, b0) == True{} : Bool}
  for shaped: {Nat.is_le(128n, A) == True{} : Bool}
  for group: {Nat.is_lt(g, Part.groups(1n, H)) == True{} : Bool}
  for contributor: {WSpec.touches(b, g, Tail.kt0(A), Tail.total0(A, H), G, nsm, a0, b0) == True{} : Bool}
  {Nat.is_le(Impl.fc0(G, nsm, A, H, a0, b0, g), b) == True{} : Bool} &
  {Nat.is_lt(Nat.sub(b, Impl.fc0(G, nsm, A, H, a0, b0, g)), Impl.nc0(G, nsm, A, H, a0, b0, g)) == True{} : Bool} &
  {Nat.is_le(Impl.nc0(G, nsm, A, H, a0, b0, g), Impl.mc0(G, nsm, A, H, a0, b0)) == True{} : Bool}

# ---- (3) counters: signalled totals equal the table targets, waiter passes equal the reset counts ----

law wgate_signals:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for +p: Nat
  for valid: {Wp.weights_valid(Mlp.total1(H, I), G, nsm, a1, b1) == True{} : Bool}
  for shaped: {Nat.is_le(128n, H) == True{} : Bool}
  for pair: {Nat.is_lt(p, Mlp.pairs(I)) == True{} : Bool}
  {sig_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C1{p}) == Impl.exp_gate(G, nsm, H, I, a1, b1, p) : Nat}

law wup_signals:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for +p: Nat
  for valid: {Wp.weights_valid(Mlp.total1(H, I), G, nsm, a1, b1) == True{} : Bool}
  for shaped: {Nat.is_le(128n, H) == True{} : Bool}
  for pair: {Nat.is_lt(p, Mlp.pairs(I)) == True{} : Bool}
  {sig_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C1{Nat.add(Mlp.pairs(I), p)}) ==
    Impl.exp_up(G, nsm, H, I, a1, b1, p) : Nat}

law wfinish_signals:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for +p: Nat
  {sig_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C2{p}) == Impl.fin_warps(G, nsm, H, I, a2, b2, p) : Nat}

law wgate_waiters:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for +p: Nat
  for pair: {Nat.is_lt(p, Mlp.pairs(I)) == True{} : Bool}
  {wait_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C1{p}) == Impl.fin_warps(G, nsm, H, I, a2, b2, p) : Nat}

law wup_waiters:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for +p: Nat
  for shaped: {Nat.is_le(128n, I) == True{} : Bool}
  for groups: {Nat.mod(I, 512n) == 0n : Nat}
  {wait_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C1{Nat.add(Mlp.pairs(I), p)}) ==
    Impl.fin_warps(G, nsm, H, I, a2, b2, p) : Nat}

law wpair_waiters:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for +p: Nat
  {wait_total(G, nsm, H, I, a1, b1, a2, b2, G, MSpec.C2{p}) == Impl.wait2(G, nsm, H, I, a2, b2, p) : Nat}

# ---- (4) deadlock freedom: 8201's stratification over the weighted events ----

law wlevels:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for +b: Nat
  for +d: Nat
  for +c: MSpec.Ctr
  {MSpec.ordered(Impl.events(G, nsm, H, I, a1, b1, a2, b2, b), 0n) == True{} : Bool} &
  {MSpec.sigs_below(Impl.events(G, nsm, H, I, a1, b1, a2, b2, d), c, MLaws.gate_level(c)) == True{} : Bool} &
  {MSpec.waits_from(Impl.events(G, nsm, H, I, a1, b1, a2, b2, b), c, MLaws.gate_level(c)) == True{} : Bool}

# ---- (5) ext 8204's program order: the counter events and main loop, every cnt1 after its flush ----

law wprogram:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for +b: Nat
  {DSpec.syncs(Impl.program(G, nsm, H, I, a1, b1, a2, b2, b)) == Impl.events(G, nsm, H, I, a1, b1, a2, b2, b)
    : List<&2, MSpec.Ev>} &
  {DSpec.works(Impl.program(G, nsm, H, I, a1, b1, a2, b2, b)) == Impl.mainloop1(G, nsm, H, I, a1, b1, b)
    : List<&2, PSpec.Ev>} &
  {DSpec.pub_after_flush(Impl.program(G, nsm, H, I, a1, b1, a2, b2, b), Nil{}) == True{} : Bool}

# ---- (6) wait lists and finishers ----

law wwaits_cover:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a2: Nat
  for +b2: Nat
  for +b: Nat
  for +x: Nat
  for lo: {Nat.is_le(Impl.s2(G, nsm, H, I, a2, b2, b), x) == True{} : Bool}
  for hi: {Nat.is_lt(x, Nat.add(Impl.s2(G, nsm, H, I, a2, b2, b), Impl.n2(G, nsm, H, I, a2, b2, b))) == True{}
    : Bool}
  {MSpec.member(Impl.waits(G, nsm, H, I, a2, b2, b), Mlp.pair_of(I, x)) == True{} : Bool}

law wwaits_nodup:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a2: Nat
  for +b2: Nat
  for +b: Nat
  {MSpec.nodup(Impl.waits(G, nsm, H, I, a2, b2, b)) == True{} : Bool}

law wfin_rank_bound:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a2: Nat
  for +b2: Nat
  for +b: Nat
  for inside: {Nat.is_lt(b, G) == True{} : Bool}
  {Nat.is_lt(Impl.fin_rank(G, nsm, H, I, a2, b2, b), Impl.fin_cnt(G, nsm, H, I, a2, b2, b)) == True{} : Bool}

law wfin_rank_unique:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a2: Nat
  for +b2: Nat
  for +b: Nat
  for +c: Nat
  for pair: {Impl.fin_pair(G, nsm, H, I, a2, b2, b) == Impl.fin_pair(G, nsm, H, I, a2, b2, c) : Nat}
  for rank: {Impl.fin_rank(G, nsm, H, I, a2, b2, b) == Impl.fin_rank(G, nsm, H, I, a2, b2, c) : Nat}
  {b == c : Nat}

law wfinish_jobs_once:
  for +G: Nat
  for +nsm: Nat
  for +H: Nat
  for +I: Nat
  for +a2: Nat
  for +b2: Nat
  for +p: Nat
  for +m: Nat
  for +x: Nat
  for finished: {Nat.is_lt(0n, Impl.fin_count(G, nsm, H, I, a2, b2, G, p)) == True{} : Bool}
  {Impl.finisher_hits(G, nsm, H, I, a2, b2, G, p, x, m) == PSpec.bit(Nat.is_lt(x, Nat.mul(4n, m))) : Nat}

# ---- (7) equal weights are the uniform (ext 8201 / 8202 / 8204) model ----

law wuniform:
  for +G: Nat
  for +nsm: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +u: Nat
  for +w: Nat
  for +v: Nat
  for +b: Nat
  for +g: Nat
  for upos: {Nat.is_lt(0n, u) == True{} : Bool}
  for wpos: {Nat.is_lt(0n, w) == True{} : Bool}
  for vpos: {Nat.is_lt(0n, v) == True{} : Bool}
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped_a: {Nat.is_le(128n, A) == True{} : Bool}
  for shaped_h: {Nat.is_le(128n, H) == True{} : Bool}
  for shaped_i: {Nat.is_le(512n, I) == True{} : Bool}
  {Impl.s0(G, nsm, A, H, u, u, b) == Tail.s0(G, A, H, b) : Nat} &
  {Impl.s1(G, nsm, H, I, w, w, b) == Mlp.s1(G, H, I, b) : Nat} &
  {Impl.s2(G, nsm, H, I, v, v, b) == Mlp.s2(G, H, I, b) : Nat} &
  {Impl.events(G, nsm, H, I, w, w, v, v, b) == Mlp.events(G, H, I, b) : List<&2, MSpec.Ev>} &
  {Impl.fc1(G, nsm, H, I, w, w, g) == Part.b_lo(g, Mlp.kt1(H), Mlp.total1(H, I), G) : Nat} &
  {Impl.nc1(G, nsm, H, I, w, w, g) == Part.nc(g, Mlp.kt1(H), Mlp.total1(H, I), G) : Nat} &
  {Impl.nc2(G, nsm, H, I, v, v, g) == Part.nc(g, Mlp.kt2(I), Mlp.total2(H, I), G) : Nat} &
  {Impl.nc0(G, nsm, A, H, u, u, g) == Part.nc(g, Tail.kt0(A), Tail.total0(A, H), G) : Nat}
