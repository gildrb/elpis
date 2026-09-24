# Semantic obligations for the EXL3 greedy acceptance leaf that the patched
# ExLlamaV3 generator executes once per verify round (via the unchanged
# emitted C of bend/EXL3_ACCEPT.bend), and for its independent list reference.
import Base
import ./exl3_accept.bend as Impl
import ./exl3_accept_spec.bend as Spec

# The executed scalar leaf equals the list reference for every k <= 7, every
# budget, checkpoint, stop count and id: registers past the k + 1 targets, the
# k proposals and the first ns stop slots never influence the verdict.
law leaf_refinement:
  for +k: Nat
  for valid: {Nat.is_le(k, 7n) == True{} : Bool}
  for +budget: Nat
  for +checkpoint: Nat
  for +ns: Nat
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +t4: U32
  for +t5: U32
  for +t6: U32
  for +t7: U32
  for +p0: U32
  for +p1: U32
  for +p2: U32
  for +p3: U32
  for +p4: U32
  for +p5: U32
  for +p6: U32
  {Impl.accept(k, budget, checkpoint, ns, s0, s1, s2, s3, t0, t1, t2, t3, t4,
      t5, t6, t7, p0, p1, p2, p3, p4, p5, p6) ==
    Spec.accept(List.take(&2, U32, [t0, t1, t2, t3, t4, t5, t6, t7], 1n+k),
      List.take(&2, U32, [p0, p1, p2, p3, p4, p5, p6], k),
      List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint)
    : Spec.Verdict}

# Characterization of the reference on every well-shaped round (k + 1 targets
# for k proposals, any ids, stop list, budget and checkpoint). Explained: the
# first count - 1 positions each pass every continue rule (not a stop token,
# count below the budget, proposal equal to the target, count not the
# checkpoint) and position count - 1 halts, reporting eos exactly for a stop
# token or an exhausted budget; otherwise it is the bonus (final) position, a
# mismatch or the checkpoint boundary.
law accept_explained:
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +checkpoint: Nat
  for shaped: {List.length(&2, U32, targets) ==
    1n+List.length(&2, U32, proposals) : Nat}
  {Spec.explains(Spec.count(Spec.accept(targets, proposals, stops, budget, checkpoint)),
    Spec.eos(Spec.accept(targets, proposals, stops, budget, checkpoint)),
    targets, proposals, stops, budget, checkpoint) == True{} : Bool}

# Maximality: any prefix whose positions all pass lies strictly inside the
# committed count, so no longer valid prefix is ever left uncommitted.
law accept_maximal:
  for +passed: Nat
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +checkpoint: Nat
  for shaped: {List.length(&2, U32, targets) ==
    1n+List.length(&2, U32, proposals) : Nat}
  for passing: {Spec.passes(passed, targets, proposals, stops, 0n, budget,
    checkpoint) == True{} : Bool}
  {Nat.is_lt(passed, Spec.count(Spec.accept(targets, proposals, stops, budget,
    checkpoint))) == True{} : Bool}

# Progress: every well-shaped round commits at least one token.
law accept_progress:
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +checkpoint: Nat
  for shaped: {List.length(&2, U32, targets) ==
    1n+List.length(&2, U32, proposals) : Nat}
  {Nat.is_lt(0n, Spec.count(Spec.accept(targets, proposals, stops, budget,
    checkpoint))) == True{} : Bool}

# Committed ids are a genuine prefix of the verify ids, and at most k + 1.
law accept_bounds:
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +checkpoint: Nat
  for shaped: {List.length(&2, U32, targets) ==
    1n+List.length(&2, U32, proposals) : Nat}
  {Nat.is_le(Spec.count(Spec.accept(targets, proposals, stops, budget,
    checkpoint)), List.length(&2, U32, targets)) == True{} : Bool} &
  {Nat.is_le(Spec.count(Spec.accept(targets, proposals, stops, budget,
    checkpoint)), 1n+List.length(&2, U32, proposals)) == True{} : Bool}

# Truncation: a positive budget and a positive checkpoint bound the count.
law accept_budget:
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +checkpoint: Nat
  for shaped: {List.length(&2, U32, targets) ==
    1n+List.length(&2, U32, proposals) : Nat}
  for positive: {Nat.is_lt(0n, budget) == True{} : Bool}
  {Nat.is_le(Spec.count(Spec.accept(targets, proposals, stops, budget,
    checkpoint)), budget) == True{} : Bool}

law accept_checkpoint:
  for +targets: List<&2, U32>
  for +proposals: List<&2, U32>
  for +stops: List<&2, U32>
  for +budget: Nat
  for +checkpoint: Nat
  for shaped: {List.length(&2, U32, targets) ==
    1n+List.length(&2, U32, proposals) : Nat}
  for positive: {Nat.is_lt(0n, checkpoint) == True{} : Bool}
  {Nat.is_le(Spec.count(Spec.accept(targets, proposals, stops, budget,
    checkpoint)), checkpoint) == True{} : Bool}

# The same characterization stated directly on the executed leaf.
law leaf_explained:
  for +k: Nat
  for valid: {Nat.is_le(k, 7n) == True{} : Bool}
  for +budget: Nat
  for +checkpoint: Nat
  for +ns: Nat
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +t4: U32
  for +t5: U32
  for +t6: U32
  for +t7: U32
  for +p0: U32
  for +p1: U32
  for +p2: U32
  for +p3: U32
  for +p4: U32
  for +p5: U32
  for +p6: U32
  {Spec.explains(
    Spec.count(Impl.accept(k, budget, checkpoint, ns, s0, s1, s2, s3, t0, t1,
      t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5, p6)),
    Spec.eos(Impl.accept(k, budget, checkpoint, ns, s0, s1, s2, s3, t0, t1,
      t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5, p6)),
    List.take(&2, U32, [t0, t1, t2, t3, t4, t5, t6, t7], 1n+k),
    List.take(&2, U32, [p0, p1, p2, p3, p4, p5, p6], k),
    List.take(&2, U32, [s0, s1, s2, s3], ns), budget, checkpoint) == True{}
    : Bool}

law leaf_maximal:
  for +passed: Nat
  for +k: Nat
  for valid: {Nat.is_le(k, 7n) == True{} : Bool}
  for +budget: Nat
  for +checkpoint: Nat
  for +ns: Nat
  for +s0: U32
  for +s1: U32
  for +s2: U32
  for +s3: U32
  for +t0: U32
  for +t1: U32
  for +t2: U32
  for +t3: U32
  for +t4: U32
  for +t5: U32
  for +t6: U32
  for +t7: U32
  for +p0: U32
  for +p1: U32
  for +p2: U32
  for +p3: U32
  for +p4: U32
  for +p5: U32
  for +p6: U32
  for passing: {Spec.passes(passed,
    List.take(&2, U32, [t0, t1, t2, t3, t4, t5, t6, t7], 1n+k),
    List.take(&2, U32, [p0, p1, p2, p3, p4, p5, p6], k),
    List.take(&2, U32, [s0, s1, s2, s3], ns), 0n, budget, checkpoint) ==
    True{} : Bool}
  {Nat.is_lt(passed, Spec.count(Impl.accept(k, budget, checkpoint, ns, s0, s1,
    s2, s3, t0, t1, t2, t3, t4, t5, t6, t7, p0, p1, p2, p3, p4, p5, p6))) ==
    True{} : Bool}
