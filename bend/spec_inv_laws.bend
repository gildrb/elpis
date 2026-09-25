# Round-level speculation invariance for the EXL3 + DFlash2 greedy speculative loop, over the
# model bend/spec_inv.bend (EXL3 acceptance reference + exl3_round advance kernel) against plain
# greedy decoding bend/spec_inv_spec.bend.
#
# The per-row obligation is the hypothesis ~rinv: a verify row's token depends only on its
# absolute prefix, not on which row of which round computes it (row(p, r) == row(p, 0n)). For the
# engine it is discharged by attn_rowinv_laws (3005: every row's attention partition and combine
# depend on its absolute position only), gdn_rounds_laws (the GDN state and conv window before
# token i are the uninterrupted scan whatever the round cuts) and the row-independent GEMM /
# norm / rope at a fixed M = 8; the floating-point equality of the kernels' identity merges and
# masked zeros is an engine argument (bit-exactness of the shipped kernels), not a Bend theorem.
#
# Domain: every target row function satisfying ~rinv, every prompt, stop list, checkpoint base
# and interval, every initial device state that is running with a positive budget (any
# position, anchor and checkpoint), and every sequence of draft lists (any lengths, any ids):
# this covers every drafter, including adversarial ones.
import Base
import ./spec_inv.bend as Impl
import ./spec_inv_spec.bend as Spec
import ./exl3_accept_spec.bend as Accept
import ./exl3_round.bend as Round

# D0: one round from any prefix with remaining budget 1 + bp commits exactly the greedy
# continuation: its committed verify ids followed by what greedy decoding still emits afterwards
# are the greedy output, and a round that does not end the job leaves budget.
law round_commits_greedy:
  for ~row: List<&2, U32> -> Nat -> U32
  for ~rinv: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == row(p, 0n) : U32}
  for +seq: List<&2, U32>
  for +ds: List<&2, U32>
  for +stops: List<&2, U32>
  for +bp: Nat
  for +checkpoint: Nat
  {Spec.greedy(~row, 1n+bp, stops, seq) ==
    List.append(&2, U32,
      List.take(&2, U32, Impl.targets(~row, ds, seq, 0n),
        Accept.count(Accept.accept(Impl.targets(~row, ds, seq, 0n), ds, stops, 1n+bp, checkpoint))),
      Spec.after(~row, Accept.eos(Accept.accept(Impl.targets(~row, ds, seq, 0n), ds, stops, 1n+bp, checkpoint)),
        Nat.sub(1n+bp, Accept.count(Accept.accept(Impl.targets(~row, ds, seq, 0n), ds, stops, 1n+bp, checkpoint))),
        stops,
        List.append(&2, U32, seq, List.take(&2, U32, Impl.targets(~row, ds, seq, 0n),
          Accept.count(Accept.accept(Impl.targets(~row, ds, seq, 0n), ds, stops, 1n+bp, checkpoint)))))) : List<&2, U32>} &
  {Bool.or(Accept.eos(Accept.accept(Impl.targets(~row, ds, seq, 0n), ds, stops, 1n+bp, checkpoint)),
    Nat.is_lt(Accept.count(Accept.accept(Impl.targets(~row, ds, seq, 0n), ds, stops, 1n+bp, checkpoint)), 1n+bp)) == True{} : Bool}

# D1: after any rounds with any drafts, the emitted tokens followed by what greedy decoding
# still emits from them (nothing once stopped) are the greedy output of the prompt; so the
# emitted tokens are a prefix of it; a running job keeps a positive budget.
law prefix_of_greedy:
  for ~row: List<&2, U32> -> Nat -> U32
  for ~rinv: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == row(p, 0n) : U32}
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +base: Nat
  for +interval: Nat
  for +drafts: List<&2, List<&2, U32>>
  for +position: Nat
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for positive: {Nat.is_lt(0n, budget) == True{} : Bool}
  {Spec.greedy(~row, budget, stops, prompt) ==
    List.append(&2, U32,
      Impl.out(Impl.job(~row, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint)),
      Spec.after(~row,
        Impl.stopped(Impl.job(~row, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint)),
        Impl.budget(Impl.job(~row, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint)),
        stops,
        List.append(&2, U32, prompt,
          Impl.out(Impl.job(~row, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint))))) : List<&2, U32>} &
  {List.take(&2, U32, Spec.greedy(~row, budget, stops, prompt),
      List.length(&2, U32, Impl.out(Impl.job(~row, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint)))) ==
    Impl.out(Impl.job(~row, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint)) : List<&2, U32>} &
  {Bool.or(Impl.stopped(Impl.job(~row, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint)),
    Nat.is_lt(0n, Impl.budget(Impl.job(~row, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint)))) == True{} : Bool}

# D2 (headline): any two drafters (two draft sequences, hence two sequences of acceptance
# decisions) given at least `budget` rounds both finish, and emit the same tokens: the greedy
# output of the prompt under the same budget and stop set.
law speculation_invariance:
  for ~row: List<&2, U32> -> Nat -> U32
  for ~rinv: @p:List<&2, U32> -> @r:Nat -> {row(p, r) == row(p, 0n) : U32}
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +base: Nat
  for +interval: Nat
  for +drafts1: List<&2, List<&2, U32>>
  for +drafts2: List<&2, List<&2, U32>>
  for +position: Nat
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for positive: {Nat.is_lt(0n, budget) == True{} : Bool}
  for enough1: {Nat.is_le(budget, List.length(&2, List<&2, U32>, drafts1)) == True{} : Bool}
  for enough2: {Nat.is_le(budget, List.length(&2, List<&2, U32>, drafts2)) == True{} : Bool}
  {Impl.stopped(Impl.job(~row, prompt, stops, base, interval, drafts1, position, budget, anchor, checkpoint)) == True{} : Bool} &
  {Impl.stopped(Impl.job(~row, prompt, stops, base, interval, drafts2, position, budget, anchor, checkpoint)) == True{} : Bool} &
  {Impl.out(Impl.job(~row, prompt, stops, base, interval, drafts1, position, budget, anchor, checkpoint)) ==
    Spec.greedy(~row, budget, stops, prompt) : List<&2, U32>} &
  {Impl.out(Impl.job(~row, prompt, stops, base, interval, drafts1, position, budget, anchor, checkpoint)) ==
    Impl.out(Impl.job(~row, prompt, stops, base, interval, drafts2, position, budget, anchor, checkpoint)) : List<&2, U32>}

# D3a: every round of a running job emits at least one token, whatever the target, drafts,
# budget and checkpoint (no ~rinv needed).
law round_progress:
  for ~row: List<&2, U32> -> Nat -> U32
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +base: Nat
  for +interval: Nat
  for +ds: List<&2, U32>
  for +position: Nat
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for +emitted: List<&2, U32>
  {Nat.is_lt(List.length(&2, U32, emitted),
    List.length(&2, U32, Impl.out(Impl.round(~row, prompt, stops, base, interval, ds,
      Impl.Run{Round.State{position, budget, anchor, checkpoint, False{}}, emitted})))) == True{} : Bool}

# D3b: a job with budget >= 1 has stopped after any `budget` rounds, whatever the target and the
# drafts (no ~rinv needed): runs terminate within budget rounds.
law terminates:
  for ~row: List<&2, U32> -> Nat -> U32
  for +prompt: List<&2, U32>
  for +stops: List<&2, U32>
  for +base: Nat
  for +interval: Nat
  for +drafts: List<&2, List<&2, U32>>
  for +position: Nat
  for +budget: Nat
  for +anchor: Nat
  for +checkpoint: Nat
  for positive: {Nat.is_lt(0n, budget) == True{} : Bool}
  for enough: {Nat.is_le(budget, List.length(&2, List<&2, U32>, drafts)) == True{} : Bool}
  {Impl.stopped(Impl.job(~row, prompt, stops, base, interval, drafts, position, budget, anchor, checkpoint)) == True{} : Bool}

# D4 (mutation witness): if a row's token may depend on its row index (Impl.leak violates
# ~rinv), speculation invariance fails: prompt [5], no stops, budget 2, no checkpoints; two
# single-token rounds emit [0, 0], one round drafting [0] emits [0, 1]; both runs finish.
law row_index_leak_differs:
  {U32.is_eq(Impl.leak([5, 0], 1n), Impl.leak([5, 0], 0n)) == False{} : Bool} &
  {Impl.out(Impl.job(~Impl.leak, [5], Nil{}, 0n, 0n, [Nil{}, Nil{}], 0n, 2n, 0n, 0n)) == [0, 0] : List<&2, U32>} &
  {Impl.out(Impl.job(~Impl.leak, [5], Nil{}, 0n, 0n, [[0]], 0n, 2n, 0n, 0n)) == [0, 1] : List<&2, U32>} &
  {Impl.stopped(Impl.job(~Impl.leak, [5], Nil{}, 0n, 0n, [Nil{}, Nil{}], 0n, 2n, 0n, 0n)) == True{} : Bool} &
  {Impl.stopped(Impl.job(~Impl.leak, [5], Nil{}, 0n, 0n, [[0]], 0n, 2n, 0n, 0n)) == True{} : Bool}
