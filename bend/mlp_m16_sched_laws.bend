# Semantic obligations for the ext 8201 fused-MLP schedule model bend/mlp_m16_sched.bend (the
# Nat model that computes the table bend/MLP_M16_SCHED_TABLE.bend prints). Every law is about
# that Bend model; the CUDA kernel's conformance to it (reading the table, the memory model of
# its release/acquire counters, cp.async timing, fp32 values, overflow) is outside this contract.
# All laws except pairs_finished are generic: any grid G >= 1, hidden size H and intermediate
# size I (each >= 128, G at most either phase's iteration count; I a multiple of 512 where
# pairs matter), every block, iteration, counter, pair, token-row count m and job; the ring laws
# are generic in PF as well. pairs_finished is the one fact about the served instance G = 164,
# H = 5120, I = 17408 (a witness block per pair); it discharges finish_jobs_once's k_p >= 1 there.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./mlp_m16_sched.bend as Impl
import ./mlp_m16_sched_spec.bend as Spec

# Grid-wide totals over blocks 0 .. n - 1 of each block's event list.
def sig_total(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +c: Spec.Ctr) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(sig_total(G, H, I, b, c), Spec.sig_amount(Impl.events(G, H, I, b), c))

def wait_total(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +c: Spec.Ctr) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(wait_total(G, H, I, b, c), Spec.wait_amount(Impl.events(G, H, I, b), c))

# Blocks b < n whose phase-2 virtual slice is u.
def slice_hits(+n: Nat, +u: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(slice_hits(b, u), Spec.bit(Nat.is_eq(Impl.slice(b), u)))

# Level separating the signals (strictly below) from the waits (at or above) of a counter.
def gate_level(c: Spec.Ctr) -> Nat:
  match c:
    case Spec.C1{g}:
      1n
    case Spec.C2{p}:
      2n

# ---- (1) exactly-once coverage of both GEMMs ----

# Block b's phase-1 table slice [s1, s1 + n1) is the set of gate/up iterations it owns in the
# v2 partition of total1; with phase1_exactly_once every iteration x < total1 lies in exactly
# one block's slice.
law phase1_slice_owned:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  for +x: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total1(H, I)) == True{} : Bool}
  {Bool.and(Nat.is_le(Impl.s1(G, H, I, b), x),
      Nat.is_lt(x, Nat.add(Impl.s1(G, H, I, b), Impl.n1(G, H, I, b)))) ==
    PSpec.owns(b, x, Impl.total1(H, I), G) : Bool}

law phase1_exactly_once:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +x: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for inside: {Nat.is_lt(x, Impl.total1(H, I)) == True{} : Bool}
  {PSpec.owners(G, x, Impl.total1(H, I), G) == 1n : Nat}

# Block b's phase-2 slice [s2, s2 + n2) is the set of down iterations owned by its virtual slice
# v(b) in the v2 partition of total2 ...
law phase2_slice_owned:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  for +x: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total2(H, I)) == True{} : Bool}
  {Bool.and(Nat.is_le(Impl.s2(G, H, I, b), x),
      Nat.is_lt(x, Nat.add(Impl.s2(G, H, I, b), Impl.n2(G, H, I, b)))) ==
    PSpec.owns(Impl.slice(b), x, Impl.total2(H, I), G) : Bool}

law phase2_exactly_once:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +x: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for inside: {Nat.is_lt(x, Impl.total2(H, I)) == True{} : Bool}
  {PSpec.owners(G, x, Impl.total2(H, I), G) == 1n : Nat}

# ... and v is a permutation of the grid: every virtual slice u < G is taken by exactly one
# block b < G.
law slice_permutation:
  for +G: Nat
  for +u: Nat
  for inside: {Nat.is_lt(u, G) == True{} : Bool}
  {slice_hits(G, u) == 1n : Nat}

# ---- (2) counters: signalled totals equal the expected counts, waiters equal the wait counts ----
# A wait counts mult passes on the counter's pass counter (thread 0 of a finisher block adds 8 for
# cnt1, one per warp; thread 0 adds 1 for cnt2): wait1 / wait2 are the pass totals with which the
# last passer self-resets the counter.

law gate_signals:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, H) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total1(H, I)) == True{} : Bool}
  for pair: {Nat.is_lt(p, Impl.pairs(I)) == True{} : Bool}
  {sig_total(G, H, I, G, Spec.C1{p}) == Impl.exp_gate(G, H, I, p) : Nat}

law up_signals:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, H) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total1(H, I)) == True{} : Bool}
  for pair: {Nat.is_lt(p, Impl.pairs(I)) == True{} : Bool}
  {sig_total(G, H, I, G, Spec.C1{Nat.add(Impl.pairs(I), p)}) == Impl.exp_up(G, H, I, p) : Nat}

law finish_signals:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  {sig_total(G, H, I, G, Spec.C2{p}) == Impl.exp2(G, H, I, p) : Nat}

law gate_waiters:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  for pair: {Nat.is_lt(p, Impl.pairs(I)) == True{} : Bool}
  {wait_total(G, H, I, G, Spec.C1{p}) == Impl.wait1(G, H, I, p) : Nat}

law up_waiters:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  for shaped: {Nat.is_le(128n, I) == True{} : Bool}
  for groups: {Nat.mod(I, 512n) == 0n : Nat}
  {wait_total(G, H, I, G, Spec.C1{Nat.add(Impl.pairs(I), p)}) == Impl.wait1(G, H, I, p) : Nat}

law pair_waiters:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  {wait_total(G, H, I, G, Spec.C2{p}) == Impl.wait2(G, H, I, p) : Nat}

# Every down iteration of block b's phase-2 slice reads a pair its wait list contains (the block
# waits on cnt2 of every pair whose activations it consumes), and the list has no duplicates.
law waits_cover:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  for +x: Nat
  for lo: {Nat.is_le(Impl.s2(G, H, I, b), x) == True{} : Bool}
  for hi: {Nat.is_lt(x, Nat.add(Impl.s2(G, H, I, b), Impl.n2(G, H, I, b))) == True{} : Bool}
  {Spec.member(Impl.waits(G, H, I, b), Impl.pair_of(I, x)) == True{} : Bool}

law waits_nodup:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  {Spec.nodup(Impl.waits(G, H, I, b)) == True{} : Bool}

# ---- (3) deadlock freedom given co-residency ----

# Each block's events have nondecreasing levels ...
law events_ordered:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  {Spec.ordered(Impl.events(G, H, I, b), 0n) == True{} : Bool}

# ... and for every counter c, every signal of every block d on c lies strictly below
# gate_level(c) while every wait of every block b on c lies at or above it: a wait at level L
# only needs signals of levels < L, so no block waits on a counter it (or anyone) signals later.
law signals_before_waits:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  for +d: Nat
  for +c: Spec.Ctr
  {Spec.sigs_below(Impl.events(G, H, I, d), c, gate_level(c)) == True{} : Bool} &
  {Spec.waits_from(Impl.events(G, H, I, b), c, gate_level(c)) == True{} : Bool}

# ---- (4) warp-private cp.async ring (generic in PF >= 1) ----

# Tile i is issued no later than the step that consumes it (step i) ...
law ring_issue_in_time:
  for +i: Nat
  for +pf: Nat
  {Nat.is_le(Impl.issue_step(i, pf), i) == True{} : Bool}

# ... and the next tile of the same slot, i + PF, is issued at step i + 1, strictly after tile i
# was consumed at step i.
law ring_reuse:
  for +i: Nat
  for +pf: Nat
  for pos: {Nat.is_lt(0n, pf) == True{} : Bool}
  {Impl.slot(Nat.add(i, pf), pf) == Impl.slot(i, pf) : Nat} &
  {Impl.issue_step(Nat.add(i, pf), pf) == 1n+i : Nat}

# ring2 is the slot of stream tile n1, the first phase-2 tile.
law ring2_slot:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  {Impl.ring2(G, H, I, b) == Impl.slot(Impl.n1(G, H, I, b), Impl.pf()) : Nat}

# ---- (5) split-K order equals v2 ----

# The table slices are the v2 block ranges [start(b), start(b + 1)) (phase 1) and
# [start(v), start(v + 1)) (phase 2), and each phase's loop over its slice (j from 0) consumes the
# slice's iterations in ascending order and flushes each group after its last one, exactly as
# v2's mainloop_trace; slots and fold order then follow gemm_m16_partition's slot_in_range /
# slot_injective / reduction_order at mats = 2 (phase 1) and mats = 1 (phase 2).
law phase1_v2:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, H) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total1(H, I)) == True{} : Bool}
  {Nat.add(Impl.s1(G, H, I, b), Impl.n1(G, H, I, b)) ==
    Part.start(1n+b, Impl.total1(H, I), G) : Nat} &
  {Part.mainloop(Impl.s1(G, H, I, b), Nat.add(Impl.s1(G, H, I, b), Impl.n1(G, H, I, b)),
      Impl.kt1(H)) ==
    PSpec.trace(Impl.n1(G, H, I, b), Impl.s1(G, H, I, b),
      Nat.add(Impl.s1(G, H, I, b), Impl.n1(G, H, I, b)), Impl.kt1(H)) : List<&2, PSpec.Ev>}

law phase2_v2:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, I) == True{} : Bool}
  for fits: {Nat.is_le(G, Impl.total2(H, I)) == True{} : Bool}
  {Nat.add(Impl.s2(G, H, I, b), Impl.n2(G, H, I, b)) ==
    Part.start(1n+Impl.slice(b), Impl.total2(H, I), G) : Nat} &
  {Part.mainloop(Impl.s2(G, H, I, b), Nat.add(Impl.s2(G, H, I, b), Impl.n2(G, H, I, b)),
      Impl.kt2(I)) ==
    PSpec.trace(Impl.n2(G, H, I, b), Impl.s2(G, H, I, b),
      Nat.add(Impl.s2(G, H, I, b), Impl.n2(G, H, I, b)), Impl.kt2(I)) : List<&2, PSpec.Ev>}

# ---- (6) finish jobs ----

# At the served instance every pair has at least one finisher block (k_p >= 1).
law pairs_finished:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  for served_g: {G == Impl.grid() : Nat}
  for served_h: {H == Impl.hidden() : Nat}
  for served_i: {I == Impl.inter() : Nat}
  for pair: {Nat.is_lt(p, Impl.pairs(I)) == True{} : Bool}
  {Nat.is_lt(0n, Impl.fin_count(G, H, I, G, p)) == True{} : Bool}

# A block's rank is below k of its finish pair, and no two blocks of one finish pair share a
# rank: the ranks of pair p's blocks are exactly 0 .. k_p - 1.
law fin_rank_bound:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  for inside: {Nat.is_lt(b, G) == True{} : Bool}
  {Nat.is_lt(Impl.fin_rank(G, H, I, b), Impl.fin_cnt(G, H, I, b)) == True{} : Bool}

law fin_rank_unique:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  for +c: Nat
  for pair: {Impl.fin_pair(G, H, I, b) == Impl.fin_pair(G, H, I, c) : Nat}
  for rank: {Impl.fin_rank(G, H, I, b) == Impl.fin_rank(G, H, I, c) : Nat}
  {b == c : Nat}

# For every pair p with k_p >= 1, every token-row count m and every job x: the finisher warps of
# p's blocks visit x exactly once if x < 4 m and never otherwise.
law finish_jobs_once:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  for +m: Nat
  for +x: Nat
  for finished: {Nat.is_lt(0n, Impl.fin_count(G, H, I, G, p)) == True{} : Bool}
  {Impl.finisher_hits(G, H, I, G, p, x, m) == PSpec.bit(Nat.is_lt(x, Nat.mul(4n, m))) : Nat}
