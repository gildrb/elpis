# How we formalized GPU-related inference execution

## The short answer

We did **not** formally model the entire RTX 3090 or prove NVIDIA's GPU implementation correct. We formalized selected decisions that determine whether inference can use that GPU correctly: allocation geometry, packed-memory layout, accepted speculative prefixes, and the rules for comparing optimization results. We then connected executable Bend programs to the serving implementation and checked selected native boundaries experimentally.

The idea beyond algorithmic complexity was **resource-aware semantic refinement**: an optimized implementation must preserve a separately stated meaning while respecting concrete storage, ownership, ordering, and hardware constraints. A second part was **constrained multi-objective optimization**: define what a legitimate improvement means before measuring candidates.

Those names describe the approach. They do not mean we already have a complete machine-checked refinement proof of the inference server. Some obligations are proved in Bend, others are enforced by native checks, others have measured evidence, and some remain open.

This document describes the state at the first autoresearch baseline and the unfinished direct-GPU Bend candidate on 2026-09-20. The main sources are [the root laws](LAWS.bend), [their proofs](PROOF.bend), and [the optimization contract](docs/qualification.md#optimization-contract).

## 1. Why Big-O was not enough

Algorithmic complexity describes how work grows with input size. It does not answer whether a particular implementation fits in 24 GiB, publishes a cache update too early, reads a rejected speculative token, or spends more time moving bytes than computing.

Two kernels with the same asymptotic complexity can differ substantially because of packed representation, memory access patterns, tensor-core utilization, launch overhead, synchronization, and graph replay. Conversely, a faster kernel can be unusable because its scratch buffers overlap another live allocation or because it changes model outputs.

We therefore separated four questions:

1. **Meaning:** What outputs and state transitions must the implementation preserve?
2. **Feasibility:** Can the actual hardware support its peak live resources and required context?
3. **Execution:** Does the running program really use the checked implementation, with the correct ABI and ordering?
4. **Improvement:** Do comparable measurements show better throughput, quality, or latency without concealing losses?

Formal laws answer selected parts of the first two questions and the comparison algebra in the fourth. They do not predict RTX 3090 speed. Profiling and actual runs answer the performance question.

## 2. We specified meaning separately from implementation

A proof that a function equals itself would not protect us from implementing the wrong thing. The specifications therefore use a different construction from the optimized implementation.

For example, [bend/spec.bend](bend/spec.bend) defines `seq(n, start)` as a simple ascending sequential list. [bend/range.bend](bend/range.bend) builds ranges through balanced parallel decomposition. The theorem `tree_is_seq` establishes that the parallel tree produces exactly the independent sequential reference.

The stronger `tree_exact` law uses `Spec.Ordered`: the result must have the exact length and the expected value at every position. An omitted, duplicated, reordered, or extra page fails this contract. Merely proving that every returned page belongs to a valid set would be weaker.

We made the same distinction for packed layouts. The implementation calculates named offsets; the reference scans a separate list of segment sizes. Equality connects those different constructions.

At the whole-model level, the [qualification contract](docs/qualification.md#reference-semantics-and-candidate-space) describes a reference numerical recipe, written `Rπ`. Its identity includes weights, tokenization, sampling, cache quantization, and arithmetic rules. This is a required reference boundary, **not an already completed formal Qwen model**.

That distinction matters: faithfully executing packed weights is not proof that quantization preserves the original BF16 model's quality. Small numerical error also does not guarantee identical argmax tokens unless the relevant logit margin is sufficient.

## 3. We turned GPU resource assumptions into exact contracts

### Native context and physical page geometry

The startup planner in [bend/control.bend](bend/control.bend) computes a fixed admitted geometry:

| Quantity | Value | Meaning |
|---|---:|---|
| Native context | 262144 tokens | Required served context, not a tunable benchmark shortcut |
| Additional pool headroom | 1024 tokens | Pool accounting reserve |
| Pool | 263168 tokens | Context plus headroom |
| Page size | 128 tokens | Native packed-cache page granularity |
| Physical pages | 2057 | `1 + pool / page_size`, including reserved page zero |
| Allocatable page IDs | 1 through 2056 | Page zero is excluded |

There is an important off-by-one boundary here. Physical backing covers `2057 × 128 = 263296` token positions; the last physical ID is **263295**, not `pool - 1`.

Reserving a dummy page from the 2056 allocatable pages leaves `263040` token positions, which is the native context plus **896** tokens. The `native_resources` law records these exact relationships, including the two-page write span and four-slot admission requirement. It does not claim that 896 tokens alone account for every other GPU allocation.

The planner also rejects unsupported request geometry. `plan_semantics` connects successful and rejected requests to the reference, while `valid_progress` prevents a vacuous implementation that always rejects. An empty plan or an always-failing planner cannot satisfy the successful native case.

### Packed KV layout, in bytes rather than vague sizes

For one head's 128-token k4v2 tile, the independent segment lengths are:

```text
[64d, 2d, 2d, 256, 32d, 2d, 256, 256] bytes
```

These represent packed key/value storage and its metadata. Their sum is `102d + 768` bytes. The supported head dimensions produce:

| Shape | Head dimension | Bytes per head-local tile |
|---|---:|---:|
| Target | 256 | 26880 |
| Draft | 128 | 13824 |

`layout_contiguous` proves that the implementation's boundaries equal the independent prefix scan for every natural-number dimension. `layout_shapes` exhaustively checks both supported shape constructors, including that the final boundary equals the entire tile and every boundary stays within it.

This is more specific than a space-complexity claim. It states where each region begins and ends, in the units the native consumer must use. It proves the planner's arithmetic layout, not that every CUDA load/store uses it correctly.

### Peak liveness, not just a sum of advertised model sizes

The broader resource contract is:

```text
M_peak = max over time t of
         (bytes of live physical allocations at t
          + allocator slack at t
          + driver overhead at t)

M_peak <= admitted memory budget
```

Aliases and views must not be counted as separate physical allocations. But weights, KV, recurrent state, graph-private memory, scratch, speculative staging, and capture-time peaks must all be considered.

This is a **specified feasibility obligation**, not a completed Bend theorem about all actual CUDA allocations. The planner establishes exact geometry; native allocation checks and real capacity runs supply additional evidence.

One useful example is the draft cache. Its backing is `2057 × 8 × 13824 × 5 = 1,137,438,720` bytes, even though its immediate visible window is much smaller. That observation suggests an optimization; it does not authorize replacing backing with a small ring. Radix reuse, address translation, rollback, quantization history, and asynchronous readers would first need a correct lifetime/refinement argument.

## 4. We treated speculative execution as state, not just extra tokens

For a block of eight candidates, index zero is the pending **anchor** and the other seven are draft proposals. Define:

```text
m[j] = (candidate[j + 1] == target_top1[j]), for j = 0..6
```

The accepted count `a` is the length of the uninterrupted true prefix. Once a comparison fails, a later match cannot resurrect a proposal.

The decision is:

```text
accepted proposals = a
committed inputs   = a + 1
bonus target slot  = a
sequence advance  = a + 1
```

For example, `true, true, false, true, ...` accepts two proposals and commits three inputs: the anchor plus those two proposals. The bonus comes from target slot two. **The emitted bonus is not another already-materialized KV input.**

[The speculation specification](bend/speculation_spec.bend), [implementation](bend/speculation.bend), [laws](bend/speculation_laws.bend), and [proofs](bend/speculation_proof.bend) formalize this decision independently. The generic acceptance law covers finite Boolean sequences; the fixed seven-comparison domain has exactly `2^7 = 128` masks.

EOS and output limits introduce another distinction. They can shorten visible or reusable output without changing the physical acceptance commit that has already taken place. Physical commits, client-visible output, reusable prefix, and the pending bonus cannot be treated as one length.

### Ordering and ownership are separate obligations

A valid count is not enough. KV and recurrent state must describe the same committed inputs, rejected rows must not become reusable, and a page must not be released while an asynchronous reader still uses it.

The native transaction contract requires the appropriate ordering between status reset, producers, final snapshot, fence, and publication. Failure must poison the step rather than pretend that partially changed layers were atomically rolled back. CUDA graph capture/replay and fallback paths must preserve those obligations too.

These requirements motivated native publication and host-mirror fixes. **The pure Bend acceptance proof does not prove the whole scheduler, CUDA memory model, Mamba recurrence, or transaction protocol.** Those remain separate implementation and validation boundaries, described in [qualification](docs/qualification.md#feasibility-and-inference-invariants).

## 5. We connected proofs to programs that actually execute

There are two execution stages. They must not be conflated.

### Established baseline: compiled startup planner and policy

The established integration runs original Bend-generated CPU programs for the startup plan, objective policy, and speculative policy. The planner's values and free-page sequence are consumed by native serving code. The speculative program computes all 128 decisions, whose policy is then consumed by the native GPU helper.

That is genuine execution of Bend-derived decisions, but it is **not** the same as running a Bend acceptance function on the GPU for every step. The baseline GPU path consumes the generated policy table.

The laws also cover serialized output: all 38 plan fields, page ordering, and the protocol string. Proving a correct internal value would be insufficient if the wire encoder changed it before consumption. `rows_semantics` and `native_wire` bridge that gap up to the explicit trusted IO boundary.

[bend/adapter.py](bend/adapter.py) binds retained source, compiler, Base library, proof logs, emitted C, compiled programs, and execution evidence. The selected authority is original **Bend 2.0.20**, not merely any executable named `bend`. The [Docker build](Dockerfile) packages the checked artifacts with the native patch series.

Hashes prevent accidental substitution and stale evidence from being accepted as the same build. They do not mathematically prove the compiler correct or independently defeat an operator fabricating an entire evidence set.

### Unfinished candidate: direct compiled Bend on the GPU

The candidate replaces the table lookup with `decide7`, taking seven scalar comparison flags and returning four decision fields. The fixed hot-path input is not a linked list. The independent specification can still use a clear mathematical list representation; the execution representation does not have to match it.

[bend/native_build.py](bend/native_build.py) identifies and checks the emitted scalar leaf and Boolean ABI against finite-domain reference outputs, then builds an SM86 CUDA artifact using NVRTC. [bend/native.cu](bend/native.cu) supplies the surrounding tensor loads/stores and calls the compiler-emitted function. The acceptance decision is not replaced with a handwritten CUDA formula.

[bend/native.py](bend/native.py) owns the native launch boundary. This design avoids putting the stock Bend task VM into the token loop, where its arena and synchronization behavior would impose inappropriate costs. It also avoids per-token subprocess execution or transferring the decision to the CPU.

The wrapper still has real obligations: tensor widths, prefix strides, bounds, disjoint output storage, context/stream ownership, graph lifetime, and matching integer promotion behavior. Natural-number proofs do not automatically prove C/CUDA machine-word behavior.

At this document's snapshot, the updated root proof and candidate Docker build have passed in the recorded work. **The new direct-GPU candidate's actual GPU smoke, full serving measurement, and performance gain remain unverified.** The earlier 128-mask GPU evidence belongs to the baseline policy-consuming helper, not automatically to this new launch path.

## 6. We made the proofs compositional instead of enormous computations

The proof work was not simply “evaluate a giant native configuration twice and compare it.”

`PROOF.bend` first proves reusable facts such as `seq_split`: splitting a sequential range at an arbitrary point and appending the parts gives the original range. It then proves the parallel tree equivalent by induction and specializes that result to the native page sequence.

The 2056-page sequence is composed from trees of widths 2048 and 8. `trees_split` connects those trees to the independent reference without requiring the equality checker to compare two fully expanded 2056-element lists. Serialization is likewise proved for abstract lists before specializing to native values, avoiding unnecessary evaluation of thousands of decimal encodings.

This is the distinction between **proof complexity** and **inference complexity**. Better proof structure makes checking practical without weakening the property. A universal layout theorem is stronger than checking two examples, even when its proof is cheaper to check.

The recorded original Bend 2.0.20 proof completed with a 1 GiB process stack limit and `BUN_JSC_maxPerThreadStackUsage=536870912`. That addressed checker resource requirements without patching the admitted checker or weakening the laws. The earlier checker-repair investigation is not the trusted basis of this baseline.

## 7. We formalized what “better” means, not a promised tok/s number

The full objective is not “make a token counter larger.” The [objective specification](bend/objectives.bend) distinguishes quality, throughput, time to first token, and reported energy. [selection laws](bend/selection_laws.bend) and [proofs](bend/selection_proof.bend) connect the executable classifier to that independent specification.

For the full comparison, the primary observed vector is:

```text
(quality in each frozen environment,
 committed throughput at each frozen depth,
 negative time-to-first-token at each frozen depth)
```

A candidate dominates another only if every primary coordinate is at least as good and at least one is strictly better. A quality-only improvement counts. Mixed gains and losses are a tradeoff. Missing primary evidence is incomplete, not zero or a tie. Energy is required reporting, not an undisclosed extra dominance veto.

The mathematical classifier operates on authenticated comparison categories such as `Better`, `Same`, `Worse`, and `Missing`. It does not generate quality scores, predict timings, or prove that the measured inputs are truthful.

The autoresearch loop uses frozen tiny Prime math plus C1 as a practical iteration measurement, with `model_call_output_tok_s` as its primary metric. **That narrower decision rule does not replace full qualification or certify long-context quality.** The original tasks, graders, generation budget, failed answers, and truncations stay intact.

Similarly, the hardware-indexed feasible set `F(H,D)` describes implementations valid for the declared hardware and request domain. A working 65536-token recovery service is not a feasible substitute for the required 262144-token candidate.

This approach justifies “best measured so far,” not “globally optimal.” A global maximum would require a defined candidate space and complete search or sound pruning bounds. A roofline for one kernel cannot establish an upper bound for every equivalent inference algorithm.

## 8. What the actual evidence establishes

The project combines different kinds of evidence rather than calling them all proofs:

| Evidence | Established scope | Important limit |
|---|---|---|
| Root Bend proof | Stated planner, layout, serialization, objective and speculation laws | Not the compiler, CUDA, floating point, or whole model |
| Baseline GPU helper probe | 128 masks, 5500 rows, 80 invocations across eager and graph paths | Not the new direct-leaf candidate or full recurrent state |
| Component numerical replay | 576 retained events across the declared component suites | Not loaded-model Mamba/projection/scheduler correctness or broad quality |
| Near-native capacity run | 262014 submitted input tokens plus 128 output tokens completed | Not sustained long-session quality or a global peak-memory proof |
| Tool-managed baseline run | About 92.70 math model-call tok/s, 54.92 C1 committed tok/s at 32K, reward 2/3 | Tiny repeatable measurement, not full native-context qualification |

The two throughput values measure different intervals and workloads; they must not be treated as interchangeable. The failed math task exhausted its 32768-token generation budget without a final answer and remains a zero. We did not award credit based on internal reasoning.

The [qualification ledger](docs/qualification.md#latest-bendnative-evidence-and-completed-capacity) and [sanitized baseline record](bench/results/bend20-native-baseline-20260920.json) retain the numerical and capacity boundaries. The tool-managed baseline is recorded separately by the autoresearch session.

The safe experiment machinery adds operational evidence: exclusive ownership, an independently armed finite recovery window, exact image identity, fresh private outputs, and cleanup of descendant processes. This keeps failed experiments from silently becoming permanent service failures. It is not a theorem that hardware or drivers cannot fail.

## The distinction to remember

We formalized **the legal decisions and resource relationships around GPU execution**, implemented selected decisions in executable Bend, and bound their artifacts to the native consumer. We specified broader ownership, temporal, numerical, and optimization obligations, but did not pretend those specifications were already complete proofs.

The resulting chain is:

```text
independent specification
  -> proved selected Bend implementation
  -> retained compiler/build/ABI identity
  -> actual native consumption
  -> numerical, capacity, and workload evidence
  -> constrained measured optimization
```

Each arrow needs evidence of its own. The achievement beyond Big-O is making those boundaries explicit enough to reject a fast but incorrect, infeasible, disconnected, or misleading optimization.
