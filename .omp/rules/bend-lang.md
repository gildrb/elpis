---
name: bend-lang
description: "Bend 2: law-driven correctness, affine ownership, and measured CPU/GPU performance."
alwaysApply: true
condition: "[Bb]end"
scope: ["tool:write(*.bend)", "tool:edit(*.bend)", "tool:bash"]
---

# Bend 2: prove the contract, measure the implementation

Apply this rule when writing, reviewing, optimizing, or proving Bend code, or formalizing another implementation in Bend. Do not require unrelated projects to adopt Bend.

Run `bend guide` to learn. Use `LAWS.bend` to keep important rules. Run `bend PROOF.bend` before committing. Parallelize substantial independent work wherever correctness, ownership, and measured costs permit. Never trade away the specification to obtain a proof or a speedup.

## 1. Establish the active toolchain

Use the latest stable upstream Bend release as the source of truth. Resolve the executable with `command -v bend`, inspect its help with `bend --help`, and check the selected version against the official upstream release. When a newer stable version is available, update the project toolchain pins, source and binary hashes, packaging, artifact identities, and active version gates accordingly; an older project pin is not a reason to remain on the older version. When using a tool-manager shim, identify its selected installation in the project's working directory. Record the observed path, version, and relevant capabilities, then use that version consistently for documentation, checking, and compilation. Query the version using the command advertised by its help; current releases use `bend version`, not necessarily `--version`.

Run `bend guide` and `bend LAWS.bend` with the current release before implementation. Inspect all diagnostics: a laws-only file may report open obligations discharged by `PROOF.bend`; that is not a successful proof. Read relevant library definitions through advertised commands such as `bend base Array`. Read the shader guide for parallel or graphical work and the effects guide for foreign effects when available. Inspect version-matched implementation source, tests, and release notes where behavior is unclear.

Never infer the installed or latest version from this rule, an earlier transcript, or another checkout. Upgrading to the latest stable release is the default required action, not an unauthorized toolchain change. Make the migration explicit, rediscover capabilities, and rerun the complete proof and production-artifact validation gates. Fix compatibility issues without weakening accepted laws or suppressing checks. Never downgrade or fall back to an older checker to make a failing program pass. Missing prerequisites or an upstream failure block the affected verification claim; report the exact failure rather than inventing success.

## 2. Rank evidence and resolve contradictions

Give Victor Taelin's directly attributable guidance priority over third-party interpretations. Then consult version-matched official source, tests, documentation, and changelogs; use reproducible community reports as leads, not authority. Distinguish Victor's statements from AI-written upstream tutorials and other contributors' opinions.

For executable behavior, the active toolchain and a reproducible check decide what actually works. Resolve apparent conflicts by version and experiment, not by treating an old statement as timeless. Do not promote roadmap features into current capabilities. Do not freeze tutorial-specific lane counts, record limits, array implementations, or compiler workarounds into universal rules.

## 3. Specify meaningful laws before implementation

Treat accepted `LAWS.bend` content as the human-controlled contract. Read it before editing production code. Implement the requested behavior, not merely something that satisfies an incomplete formula. When the task authorizes new specifications, state input domains, preconditions, outputs, errors, and the important invariants explicitly.

Cover both what must never happen and what must actually happen. Depending on the algorithm, include bounds, conservation, permutation or length preservation, ordering, deterministic tie-breaking, round trips, and state-transition invariants. For a state machine, prove initial validity and preservation by every allowed transition. Keep specifications understandable and independent of incidental implementation structure.

Never weaken an accepted law, narrow its domain, add unjustified assumptions, redefine its predicates, disconnect its imports, or remove required behavior to make verification succeed. Specification changes require explicit authorization and an identifiable diff. Check for vacuous preconditions and trivial implementations. Use representative examples and deliberate negative cases or temporary mutations to check that the laws reject the bugs they are intended to exclude; restore mutations before final validation.

## 4. Prove the code that actually ships

`LAWS.bend` must reference the actual production definitions under verification. `PROOF.bend` must import those laws and discharge every required claim using the installed language's law/definition pairing. A separate clean reference implementation is not a proof of an optimized implementation unless their required relation is also established.

Use small reusable lemmas, explicit annotations, structural induction, and the installed equality/rewrite facilities. Check proofs incrementally. Resolve every required open law and proof hole. Do not present `?TODO`, assumed conclusions, unchecked foreign bodies, `@unsafe` dependencies, or a checker exploit as proof evidence. Inspect dependency diagnostics; a safe-looking entry point can depend on unsafe code transitively.

Keep the verified computational core pure and isolate effects. When unsafe or foreign code is explicitly required, minimize and document that boundary; do not call the dependent behavior fully verified. Do not modify the checker, suppress failures, or downgrade to evade a proof obligation. An apparent soundness bug needs a minimal reproducer and a blocked verification claim, not exploitation.

Keep proof-only models and their dependencies outside production entry points' runtime import graphs. Production must not depend on `PROOF.bend` or acquire a list-based implementation merely because the proof uses lists. Proof modules may import production, not the reverse. Verify actual erasure and generated output rather than assuming all proof-shaped code is free.

## 5. Respect affine ownership precisely

Affine means **at most one use**, not exactly one. Unused values may be dropped. A reusable `+` binding requires the appropriate `Data` kind in checked code; `-` bindings are erased and cannot supply runtime evidence. Each affine resource must have one unambiguous ownership flow through every executed path.

Arrays and closures are affine under the safe rules. A closure, including a partial application, is not reusable merely because its captures are `Data`. Thread owned arrays and handles through their documented return values. Do not duplicate them, manufacture aliases, or add `@unsafe` to bypass ownership.

`List.take(xs, ...)` and `List.drop(xs, ...)` cannot both consume the same affine `xs`. For genuinely list-shaped algorithms, use a suitable single-pass split or explicitly permitted reusable representation. For array-shaped work, fix the representation instead. Never add `+` everywhere or clone a large buffer just to silence the checker.

`+` permits reuse; it does not promise free copying or borrowing. Account for sharing, reference counts, atomics, allocation, and destruction in hot paths. Inspect what the compiler actually borrows, shares, copies, and drops.

## 6. Match representation to the workload

No linked lists for array-shaped production work. Bytes, words, buffers, indexed state, vectors, lookup tables, and serialized data need packed native arrays, genuinely supported slices or partitions, or suitable fixed records. Verify both the API and its compiled representation. Do not invent slice support or assume a tree-shaped library definition necessarily lowers to a pointer tree.

Use linked structures only when their operations or semantics fit the algorithm, such as genuine streams, persistent structure, or short sequentially consumed candidate lists. Avoid repeated indexing, `take`/`drop`, append, whole-structure traversal, and conversions in hot loops. Isolate unavoidable list-based library boundaries and convert deliberately.

For fixed-size score selectors or folds, prefer suitable native arrays or fixed records; when a recursive parallel representation is appropriate, build a balanced `Data` tree directly from indices using `Leaf`/`Node` constructors and independent parallel calls such as `l r = build(left) build(right)`. Do not build a linked-list intermediate merely to split it into a tree. Preserve ownership, logical size, element coverage, and deterministic ties, including odd sizes and empty inputs.

Read the active array semantics: allocation sizes, index wrapping or bounds behavior, element kinds, read/write return values, and cloning costs. Prove logical bounds rather than treating wrapping as validation. Do not confuse list literals with array literals or assume every element type supports the same indexing sugar.

## 7. Expose useful parallelism aggressively

Look for independent subproblems in every substantial computation. Prefer balanced divide-and-conquer, maps, reductions, and independent pipelines over avoidable sequential chains. Express independent calls with the installed parallel-call syntax; ordinary recursive syntax alone is not evidence that useful parallelism exists.

Balance estimated work, not just item counts. Use coarse fork-join structure with efficient sequential or tail-recursive leaf loops. Tune grain size and cutoffs on the target hardware. Do not fork for every scalar operation, retain a long serial spine, or create so many tiny tasks that scheduling dominates. Serial execution is appropriate for real dependencies or demonstrated overhead, not as an unexamined default.

Partition ownership with the data. Pass independent subtrees, supported owned partitions, or small required fields to branches. Do not pass one affine array to two consumers. Do not introduce unsafe shared-array or atomic APIs merely to obtain parallel speed inside a supposedly verified core. Avoid copying whole inputs or sharing a large boxed object across all workers without measuring the cost.

Prove the parallel result satisfies the same contract as the required sequential behavior. Reassociation needs a valid algebraic law; permutation needs order independence. Preserve stable ordering and tie-breaking where required. Floating-point addition is not associative: do not silently reassociate it or change precision and call the result equivalent.

## 8. Choose and verify the execution backend

Distinguish CPU parallelism, GPU execution, and effect concurrency. Use GPU-marked calls only as supported by the installed toolchain. Confirm the actual backend: a GPU request or `!` in source is not proof that a GPU ran it. Detect disabled or unavailable GPUs and label CPU fallback honestly. Do not assume the JavaScript target executes forks in parallel.

Benchmark uniform numeric work on the GPU and compare divergent, irregular, small, or latency-sensitive work against the CPU. Amortize launches and keep data resident when possible. Do not treat discrete-GPU managed memory as equivalent to Apple's physically unified memory; measure transfers, page migration, synchronization, and ownership costs.

Distribute or preprocess shared scene/state data once per useful region instead of repeatedly traversing it in every lane. Keep leaf work flat and local. Use the supported IO concurrency primitives for independent effects while preserving required ordering and handle ownership; pure fork-join parallelism is not an effect scheduler.

## 9. Write explicit, proof-friendly, efficient code

Use small functions with clear contracts and minimal state. Follow the active structural-termination and matching rules: put decreasing structural inputs where the checker expects them, use suitable helpers for computed scrutinees, and supply justified fuel for externally bounded loops. Never insert `@unsafe` merely because the proof or termination argument is inconvenient.

Use explicit numeric types and supported typed operators. Distinguish mathematical naturals, bounded machine words, and floating-point operations. Establish overflow, conversion, shift, division, and index behavior where relevant. A theorem about `Nat` does not automatically prove a `U32` or `F32` implementation; prove the required correspondence and disclose axiomatic assumptions.

Prefer existing checked library definitions and reusable lemmas over parallel ad-hoc implementations. Use top-level functions or supported closed `~` template arguments when repeated application is needed. Specialize hot paths deliberately; do not turn every value into a template or explode code size. Minimize wide state passed through calls, continuations, and joins. Construct or compute data near its use when that reduces traffic without duplicating substantial work.

## 10. Inspect generated code and measure honestly

For performance-sensitive changes, inspect emitted C and optimized assembly for the actual hot path, plus device output or profiling when available. Use the active CLI's emission commands and equivalent production build settings. Trace unexpected code back through the corresponding Bend definitions and compiler/library source.

Look for avoidable traversal, boxing, allocation, copying, reference-count or atomic traffic, helper/continuation transitions, generic arithmetic, failed inlining, wide state transfers, register spills, and excessive code size. Distinguish unavoidable costs from actual regressions. Treat generated helper names and old optimization recipes as version-specific evidence, not permanent contracts.

Benchmark optimized runnable artifacts, not proof checking or normalization of a pure `main`. Compare identical workloads and validated outputs against a relevant baseline. Consume results so dead-code elimination cannot remove the work. Use warmups, repeated interleaved comparisons, representative sizes, and enough reporting to distinguish a gain from noise. Do not run competing benchmarks simultaneously on the same device.

Record source revision, executable/version, compiler flags, hardware, backend, thread count, workload, latency/throughput, and relevant memory costs. Separate compilation, startup, transfers, steady-state compute, and cleanup; include end-to-end costs when claiming an application speedup. Retain an optimization only when it meets the stated objective without violating correctness or other constraints. Rerun proofs and tests after changing it.

Hardware throughput is measured, not established by writing a desired number into `LAWS.bend`. A formal complexity or cost-model theorem is conditional on that model; it is not proof of wall-clock speed, GPU occupancy, or tokens per second.

## 11. State cross-language proof boundaries

Bend does not automatically import an external implementation's semantics and does not directly prove arbitrary Python, TypeScript, Rust, or C source. For a port, identify the behavior to formalize, express it in Bend, state its laws in `LAWS.bend`, and prove them in `PROOF.bend`. Explicitly label the result as a proof of that Bend implementation or model.

Claim equivalence with the original only when an additional refinement or equivalence argument establishes the required relation. Include representations, numeric semantics, errors, serialization, effects, and concurrency where they matter. Differential tests provide evidence, not a universal equivalence proof. Likewise, a checked foreign function signature does not verify its C/JS body, and a checked source theorem does not certify the compiler, runtime, or hardware.

## 12. Apply a final commit gate

Work in this order: discover the toolchain; read the contract; identify proof and performance obligations; implement and prove incrementally; test and measure; review the exact final diff; rerun the complete gates.

Before committing, run `bend PROOF.bend` through the same resolved executable against the final sources and inspect its exit status and complete diagnostics. Ensure every required law is included and discharged, with no unresolved holes or undisclosed unsafe/foreign dependencies affecting the claimed guarantees. Check the relevant production entry points and run the project's regression and backend tests as well. No cached success, truncated output, success-shaped text, disabled check, or proof of an earlier revision substitutes for this gate.

Any subsequent relevant source, law, proof, dependency, toolchain, or build change invalidates the corresponding validation. Rerun it. Preserve or integrate the gate into existing CI when the task includes build/CI changes; an agent rule alone is not an enforced repository control.

Report what changed, the exact laws and scope verified, commands actually run, measured performance and conditions, and remaining assumptions or blockers. Never claim a proof, a GPU run, a speedup, full equivalence, or completion without the corresponding evidence.
