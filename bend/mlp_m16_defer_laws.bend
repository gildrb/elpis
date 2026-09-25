# Semantic obligations for ext 8204's deferred phase-1 publish (bend/mlp_m16_defer.bend), stated about
# that Bend model. Append-only: the ext 8201 laws (bend/mlp_m16_sched_laws.bend) and the ext 8202 laws
# (bend/tail_m16_sched_laws.bend) are unchanged and still hold for 8204; the laws below carry them
# over to the deferred program order. Generic in G, H, I and the block (the hypotheses of the counter
# laws are those of the 8201 laws they reuse). The kernel's conformance (the lane-predicated publish
# of groups s1 / KT1 + lane, fences, the memory model) is outside this contract; mlp_m16_defer_diff.py
# checks the lane rule against the model's signal groups at the served instance.
import Base
import ./gemm_m16_partition.bend as Part
import ./gemm_m16_partition_spec.bend as PSpec
import ./mlp_m16_sched.bend as Mlp
import ./mlp_m16_sched_spec.bend as MSpec
import ./mlp_m16_sched_laws.bend as MLaws
import ./tail_m16_sched.bend as Tail
import ./tail_m16_sched_spec.bend as TSpec
import ./mlp_m16_defer.bend as Impl
import ./mlp_m16_defer_spec.bend as Spec

# Grid-wide totals over blocks 0 .. n - 1 of the counter events of each block's deferred program.
def sig_total(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +c: MSpec.Ctr) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(sig_total(G, H, I, b, c), MSpec.sig_amount(Spec.syncs(Impl.events(G, H, I, b)), c))

def wait_total(+G: Nat, +H: Nat, +I: Nat, +n: Nat, +c: MSpec.Ctr) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+b:
      Nat.add(wait_total(G, H, I, b, c), MSpec.wait_amount(Spec.syncs(Impl.events(G, H, I, b)), c))

# ---- (1) the deferral is a pure reordering ----

# A block's deferred program has exactly ext 8201's counter events, in 8201's order ...
law defer_syncs:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  {Spec.syncs(Impl.events(G, H, I, b)) == Mlp.events(G, H, I, b) : List<&2, MSpec.Ev>}

# ... and exactly 8201's phase-1 main loop (same tiles, flushes and order) ...
law defer_works:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  {Spec.works(Impl.events(G, H, I, b)) == Impl.mainloop1(G, H, I, b) : List<&2, PSpec.Ev>}

# ... as does the per-flush (8201) order: both programs differ only in where the phase-1 signals
# sit relative to the main-loop work.
law eager_same_events:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  {Spec.syncs(Impl.eager(G, H, I, b)) == Mlp.events(G, H, I, b) : List<&2, MSpec.Ev>} &
  {Spec.works(Impl.eager(G, H, I, b)) == Impl.mainloop1(G, H, I, b) : List<&2, PSpec.Ev>}

# ---- (2) release after the data: every cnt1[g] signal follows the flush of group g ----

law defer_pub_after_flush:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  {Spec.pub_after_flush(Impl.events(G, H, I, b), Nil{}) == True{} : Bool}

law eager_pub_after_flush:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  {Spec.pub_after_flush(Impl.eager(G, H, I, b), Nil{}) == True{} : Bool}

# ---- (3) deadlock freedom: 8201's stratification holds for the deferred programs ----
# Levels never decrease in a block's counter events; every signal of any block d on counter c lies
# strictly below gate_level(c) and every wait of any block b on c at or above it: a wait at level L
# needs only signals of levels < L, which every block issues before any of its own waits.
law defer_levels:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +b: Nat
  for +d: Nat
  for +c: MSpec.Ctr
  {MSpec.ordered(Spec.syncs(Impl.events(G, H, I, b)), 0n) == True{} : Bool} &
  {MSpec.sigs_below(Spec.syncs(Impl.events(G, H, I, d)), c, MLaws.gate_level(c)) == True{} : Bool} &
  {MSpec.waits_from(Spec.syncs(Impl.events(G, H, I, b)), c, MLaws.gate_level(c)) == True{} : Bool}

# ---- (4) counts: each counter reaches exactly its expected count once per launch, and the waiters'
# passes reach exactly the pass count at which the last passer zeroes the counter (reset) ----
# The signalled total of cnt1[p] / cnt1[NP + p] / cnt2[p] over all blocks equals the count the waits
# expect (so a wait passes only once every signal is in, and no signal comes after the reset); the
# weighted waiter total equals the table's pass count, so the last pass happens and zeroes the counter
# and its pass counter for the next launch.
law defer_gate_signals:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, H) == True{} : Bool}
  for fits: {Nat.is_le(G, Mlp.total1(H, I)) == True{} : Bool}
  for pair: {Nat.is_lt(p, Mlp.pairs(I)) == True{} : Bool}
  {sig_total(G, H, I, G, MSpec.C1{p}) == Mlp.exp_gate(G, H, I, p) : Nat}

law defer_up_signals:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  for grid: {Nat.is_lt(0n, G) == True{} : Bool}
  for shaped: {Nat.is_le(128n, H) == True{} : Bool}
  for fits: {Nat.is_le(G, Mlp.total1(H, I)) == True{} : Bool}
  for pair: {Nat.is_lt(p, Mlp.pairs(I)) == True{} : Bool}
  {sig_total(G, H, I, G, MSpec.C1{Nat.add(Mlp.pairs(I), p)}) == Mlp.exp_up(G, H, I, p) : Nat}

law defer_finish_signals:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  {sig_total(G, H, I, G, MSpec.C2{p}) == Mlp.exp2(G, H, I, p) : Nat}

law defer_gate_waiters:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  for pair: {Nat.is_lt(p, Mlp.pairs(I)) == True{} : Bool}
  {wait_total(G, H, I, G, MSpec.C1{p}) == Mlp.wait1(G, H, I, p) : Nat}

law defer_up_waiters:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  for shaped: {Nat.is_le(128n, I) == True{} : Bool}
  for groups: {Nat.mod(I, 512n) == 0n : Nat}
  {wait_total(G, H, I, G, MSpec.C1{Nat.add(Mlp.pairs(I), p)}) == Mlp.wait1(G, H, I, p) : Nat}

law defer_pair_waiters:
  for +G: Nat
  for +H: Nat
  for +I: Nat
  for +p: Nat
  {wait_total(G, H, I, G, MSpec.C2{p}) == Mlp.wait2(G, H, I, p) : Nat}

# ---- (5) the layer tail: its counter events are the deferred 8201 block's ----
# ext 8202's model lists 8201's counter events after barrier C (tail_m16_sched's embeds_8201); with
# 8204 the tail's phase 1 publishes the same way, so its counter events are exactly the deferred
# program's, and tail_m16_sched's sync_levels / same_barriers / staged stay as stated.
law tail_defer_syncs:
  for +G: Nat
  for +A: Nat
  for +H: Nat
  for +I: Nat
  for +m: Nat
  for +b: Nat
  {TSpec.syncs(Tail.events(G, A, H, I, m, b)) == Spec.syncs(Impl.events(G, H, I, b)) : List<&2, MSpec.Ev>}
