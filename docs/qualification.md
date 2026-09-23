# Qualification status and promotion gates

**The native-context recipe is not qualified.** The objective is 262144 total
tokens with DFlash2 on one RTX 3090. The first sampled tiny-math/C1 measurement
and one full-size **262014-input + 128-output** native request have completed;
the [sanitized baseline ledger](../bench/results/bend20-native-baseline-20260920.json)
records their limited scope. The earlier interrupted capacity attempt remains
inconclusive. FP8 65536-token service is recovery capacity, not native-context
qualification; no permanent native deployment or full-profile promotion is claimed.

## Canonical tiny math baseline: not promotion

`bash autoresearch.sh` is the finite measurement entrypoint, not a deployment or
capacity command. It uses the existing native `tiny` AIME25 profile: three
seed-0 shuffled tasks, one rollout each, greedy sampling, the unchanged 32768
output budget and original upstream graders. It then runs C1 at
1024/8192/32768 content-token depths, five repetitions per depth and a 1024-token
output budget. There is no retry, task reduction, substituted scorer or new
capacity ladder in this baseline.

The operator must already own the maintenance window and recovery. Before **each**
run, Main explicitly rebuilds/deploys the intended candidate, prepares its armed
window and a fresh output path, then atomically installs a **new** descriptor at
`/run/user/1000/litos-autoresearch-operator.json`. This is the only operator input;
there is no legacy environment fallback. Its exact JSON schema is:

```json
{
  "schema_version": 1,
  "container_id": "<full 64-hex candidate container ID>",
  "api_key_file": "/private/api-key",
  "maintenance_directory": "/private/existing-armed-maintenance",
  "output_directory": "/private/parent/new-autoresearch"
}
```

Replace the placeholders with explicitly selected private values, never committed
credentials or transient IDs. Create a private temporary regular file beside the
descriptor, write and close the complete JSON with mode 0600 and owner uid1000,
then atomically rename it to the fixed path before invoking:

```console
bash autoresearch.sh
```

Missing/extra/duplicate keys, non-integer schema versions, foreign ownership,
non-0600 mode, symlinks and malformed paths are rejected. The container ID must
be full lowercase 64-hex. Paths must be canonical and absolute; the key is a
private regular file (0400/0600), the maintenance directory is an existing armed
schema-1 window, and output must not exist. The harness never changes the
descriptor or overwrites prior results. Keep it unchanged until the run exits:
the supervisor binds its private file identity and exact bytes, passes the
identity/SHA256 binding to the worker over its private stdin pipe, and records
the identity and digest in `benchmark.json`. Both processes recheck it through
the existing ownership guard. A replacement, mutation or stale window/output
fails closed; the harness never selects or recovers another candidate.

Prepared offline `eval/.venv`, pinned Prime/Verifiers and AIME25 data, sandbox
images/caches, Docker access and `nvidia-smi` are prerequisites. The shell uses
the prepared Python for its stdlib supervisor, explicitly selects rootless Docker
at `unix:///run/user/1000/docker.sock`, and clears Docker context/TLS overrides.
The supervised worker launches with
`nix develop --offline --no-write-lock-file -c <prepared-python> -m bench.autoresearch --worker`.
GPU/runtime variables are not changed. The healthy owned service must be native
262144 at `http://127.0.0.1:18020`, RTX 3090/280 W, using Bend 2.0.26. The command
does not install dependencies, start a service, change power policy or recover it.

The whole-command deadline is the earlier of 2400 seconds from start and the
guardian deadline minus 120 seconds; a 20-second termination reserve is inside
that bound. Offline Nix entry, capture, math, C1, raw-evidence admission and
PID-owned process cleanup all share this deadline.
Ownership loss, incomplete evidence, producer failure or deadline expiry rejects
the measurement rather than selecting successful rows or printing partial metrics.

The primary `model_call_output_tok_s` pools completion usage over **all** native
math model calls divided by the sum of their full model-call wall intervals.
Those native Unix wall intervals run from request send through the fully received
response and include prefill, decode and HTTP; they are neither decode-only nor
monotonic/GPU timing. Completion usage already includes reasoning tokens, which
are not added again. Legitimately graded incorrect or length-truncated answers
remain included; operationally failed calls cannot be filtered out.

Only a complete admitted run prints `METRIC name=value`: that primary metric,
`tiny_math_reward`, `committed_tps_1024`, `committed_tps_8192`,
`committed_tps_32768`, corresponding `ttft_seconds_1024`,
`ttft_seconds_8192`, `ttft_seconds_32768`, and `elapsed_seconds`.
C1 committed-counter rates and TTFT are separate secondary measurements; elapsed
time covers the entire command through admission. Retained artifacts include
`tiny-math/`, `decode/`, private `logs/`, `sources/`, before/after identity,
`benchmark.json`, `admitted.json` and `measurement.json`; failures retain
`failure.json` and/or `worker-failure.json`. Review the upstream text/reasoning
and grades privately. The first completed sampled result is recorded below.

This sampled baseline is not the full qualification vector described below.
`serve.qualification check-eval` validates one native `tiny`, `quick` or `full`
profile entry only. The separate `qualify --manifest ... --output ...` interface
requires schema-1 `profile`, `baseline` and `candidate`; each arm supplies
`identity_before`, `identity_after`, `bend_directory`, `decode_report`,
`capacity_directory`, `numerical_reports` and `evaluations`. Even a `tiny`
qualification manifest requires those evidence gates; `autoresearch.sh` instead
admits its narrower sampled-math/C1 measurement without running that full manifest.
Tiny selects only AIME25. The unchanged core suite is AIME24, AIME25, AIME26,
i3-logic and LiveCodeBench. Promotion requires profile `full`, every arm's
evidence complete and a verified observed dominance comparison; otherwise the
decision is `retain_control`. A valid tiny measurement never promotes.

### First completed sampled measurement (2026-09-20)

The [native baseline ledger](../bench/results/bend20-native-baseline-20260920.json)
binds the first admitted measurement to the native 29-patch image
`sha256:54eed6bfc1726ba03753c19fdbbf4b28792e533b030c32716877b4599cd4b499`.
It used the **predecessor operator environment**, before the private-descriptor
cutover. The workload is unchanged, but this result does not verify the updated
plain `bash autoresearch.sh` invocation, which remains pending at this record.

| Sampled measurement | Result |
|---|---:|
| Math pooled full-model-call output rate | 92.820548 tok/s |
| Native tiny AIME25 reward | 0.666667 (2/3) |
| C1 committed rate, 1024 / 8192 / 32768 content tokens | 84.716496 / 74.174910 / 54.942068 tok/s |
| C1 TTFT, 1024 / 8192 / 32768 content tokens | 1.421334 / 9.232604 / 40.817490 s |
| Whole measurement through admission | 1023.131889 s |
| Native math CLI wall time / selected-board energy | 427.215123 s / 111244.744489 J |
| Math wall time / energy per successful task rollout | 213.607562 s / 55622.372245 J |

All three math calls completed operationally, with one legitimate length
truncation and no operational failures. Private trace review reported: the first
answer correctly boxed **117** after **1832** completion tokens; the middle task
exhausted **32768** tokens without final output and retained native grade **0**,
despite eventually deriving **259** internally; the last correctly boxed **106**
after **3074** tokens, with scratch mistakes corrected. The entire middle trace
was reviewed, not retroactively graded. Its failure remains in both the reward
denominator and pooled model-call timing. The network-blocked notice is pinned
Verifiers dialect text, not a task mutation.

Energy coverage was complete over the native math CLI window (856 valid board
samples, p90 270.17 W, maximum 277.91 W); it is not whole-system energy or a
decode-only measure. No workload, scorer, task count or token budget was reduced.
These three sampled tasks and the fixed C1 matrix do not replace full-profile
quality, numerical or promotion evidence.

## Optimization contract

The task is constrained, multi-objective optimization—not proving a chosen
throughput threshold. There is no fixed 200 tok/s floor. A candidate can be
correct but infeasible, feasible but slower, faster but lower-quality, or
non-dominated without being globally optimal. Those are different results.

### Reference semantics and candidate space

Let `Rπ` be an independently specified Qwen3.8-27B reference under numerical
recipe `π`. Its identity includes checkpoint and derived-weight bytes, tokenizer,
chat template and special tokens, draft weights and ordered vocabulary, cache
quantization/sealing policy, rounding/accumulation rules, and sampling transforms.
Temperature-zero evaluation does not establish correctness of non-greedy API
paths. Randomized paths need a distributional contract and explicit RNG state,
not an accidental equality of one seeded trace.

Separate two claims:

- **Representation/execution refinement:** optimized execution implements the
  selected `Rπ`, with its declared arithmetic semantics.
- **Approximation quality:** changing `π` changes the numerical reference.
  Lossless packing relative to prepared dequantized weights is not equivalence
  to the original BF16 checkpoint. Kernel error bounds do not imply unchanged
  argmax tokens without a sufficient logit-margin bound.

The search space comprises admitted implementations and numerical recipes, not
just the currently implemented KVarN/DFLASH/A16/A8 choices. Tiling, fusion,
parallel scheduling, storage representation, buffer reuse and speculative
execution must preserve their declared reference relation. Approximation changes
need an explicit new numerical contract and unchanged native quality evaluation.
Prompt-specific answers, benchmark lookup, altered tasks/scorers/budgets and
crediting draft proposals as committed tokens are not legal optimizations.

For an implementation state `s` and reference state `r`, a simulation relation
must connect initialization, every committed transition, observable output and
termination. Internal work may take several steps; stuttering cannot excuse
nontermination. A reference-valid request must either make defined progress or
return an explicit operational error, never fabricated successful output.
Completed output, EOS/stop truncation, requested/effective budgets, physical
commits, reusable cache prefix and an unmaterialized bonus token are distinct.
Device-fault recovery is an operational assumption and measured safeguard, not
a theorem that the GPU cannot fail.

### Feasibility and inference invariants

Define `F(H,D)` from the declared hardware envelope `H` and request/workload
domain `D`. It requires the reference contract, genuine 262144-token capacity,
safe resource ownership, complete required evidence and the frozen evaluation
protocol. The presently measured hardware point is one RTX 3090 at 280 W.
Alternative operating points must be declared before comparison. A successful
65536-token fallback is outside the native-context feasible set.

Resource feasibility is a peak-liveness statement:

$$
M_{\rm peak}
= \max_t\left(\sum_{a\in {\rm live\ physical\ allocations}(t)}
 {\rm bytes}(a) + M_{\rm allocator\ slack}(t) + M_{\rm driver}(t)\right)
\le M_{\rm admitted}.
$$

Count underlying allocations once, not each alias/view. Include weights, KV,
recurrence, graph-private allocations, scratch, speculative staging, capture
peaks and external-use reserve. A nominal workspace charge, startup profiler
estimate or correct page-ID list alone is not this proof. Host/pinned memory,
integer bounds, alignment, and asynchronous lifetimes need their own bounds.

The inference obligations are grouped by observable boundary:

| Boundary | Required invariant |
|---|---|
| Input/reference | Authentic model and vocabulary bytes; exact tokenization, positions, masks and sampling; no silent prompt loss or benchmark-budget reduction. |
| Storage | Per-request logical-to-physical refinement; disjoint mutable ownership; explicit shared immutable references, dummy/sink pages and reuse generations; no stale or out-of-bounds access. |
| Speculation | Accepted prefix and bonus follow target semantics; all rejection positions are covered; target/draft KV and Mamba/GDN/conv recurrence describe the same committed inputs; rejected rows are neither reusable nor visible. |
| Transaction/publication | Failure poisons the step rather than claiming cross-layer rollback; status reset, every producer, final snapshot, fence and publication have the correct epoch and happens-before order, including graph fallback and prefill. |
| Completion/reuse | EOS, limits, cancellation, errors, radix retention/hits, extension/divergence, eviction and reuse preserve the reference relation; release follows the last asynchronous reader. |

For block size eight, candidate index zero is the pending anchor. If `a` draft
proposals are accepted, `a+1` inputs are committed: the anchor and those accepted
proposals. The emitted bonus is not yet materialized in KV/recurrence. An EOS or
output cap can further shorten visible/reusable output. Conflating these lengths
is not a harmless accounting choice.

Static source accounting identifies a useful resource hypothesis: draft packed
backing is `2057 × 8 × 13824 × 5 = 1,137,438,720` bytes, about 1.059 GiB.
Its aligned active prefix is at most 2175 tokens; eight proposal rows give 2183,
inside the 2184 metadata bound and 2304-token gather workspace. This does **not**
prove a 2304-token persistent ring is sufficient. Existing radix hits can refer
to earlier windows, and draft KV depends on target hidden states not generally
retained for reconstruction. Address translation, rollback, quantization history,
cache restoration and replay lifetimes must be proved before reducing storage.
No memory saving or performance gain from that hypothesis has been measured.

### Objectives, admissibility and deployment choice

For each frozen native environment `e`, use its unmodified weighted reward mean
`Qe` over the entire planned example/rollout multiset. Legitimately graded
incorrect answers remain in the denominator. Missing episodes, duplicate
substitution and unscored infrastructure failures cannot be silently discarded.
Greedy repetitions are not independent new questions. A legitimate budget-
exhausted native result must retain the upstream grade and truncation status;
it must not be rewritten as a different task or conflated with missing evidence.

For every frozen C1 depth `d`, aggregate the complete repetitions using pooled
committed-counter increments and elapsed intervals:

$$
T_d=10^9\,\frac{\sum_r(C_{{\rm last},r}-C_{{\rm first},r})}
                    {\sum_r(t_{{\rm last},r}-t_{{\rm first},r})},
\qquad
F_d=\frac{\sum_r(t_{{\rm first\ content/reasoning},r}-t_{{\rm start},r})}
           {10^9\,N_d}.
$$

The full comparison's observed vector is `(Qe for every e, Td for every d, -Fd for every d)`.
All coordinates must be present, comparable and legitimate. Every native
environment and each frozen depth remains separate; no scalar weighting hides
a loss. Repetition rows remain available for variability and paired analysis.
The pooled rate is not an arithmetic mean of per-row rates or a speculative
acceptance estimate.

Candidate `B` dominates `A` exactly when every primary coordinate is at least
as good and at least one is strictly better. A quality-only improvement counts.
Equal vectors are equivalent, mixed gains/losses are a tradeoff, and missing
primary evidence is incomplete—not zero or a tie. Retain non-dominated tradeoffs
for an explicit deployment decision rather than inventing utility weights.
Board energy and elapsed time per successful task are required reported
measurements; energy is not implicitly an additional dominance coordinate.

These are exact comparisons of the recorded estimates, not claims about
noise-free expected performance. Do not invent an epsilon after seeing results,
call greedy repeats independent trials, or infer statistical confidence from
a favorable point estimate. Freeze any confidence/non-inferiority policy before
the experiment it governs.

Keep admission, observed-frontier membership and deployment promotion separate.
The existing packed-only launcher constraints describe one recipe, not all of
`F(H,D)`. A non-native fallback cannot be relabeled a feasible incumbent.
If no feasible incumbent exists, that absence is explicit; comparison cannot
manufacture one. Quick evaluation may guide search but does not replace the
requested final full-suite evidence.

### Measurement and evidence legitimacy

The fixed C1 matrix is `decode.DEPTHS = (1024,8192,32768)` with 1024 output tokens,
the frozen corpus/nonce construction and greedy sampling. Every declared positive
repetition is mandatory. Validate nominal content depth using the actual
tokenizer and bind actual chat prompt counts separately; raw-content token
counts are not chat-template counts. A report cannot redefine the required
depths. Preserve raw requests, tokenizer receipts, SSE bytes and observation
timestamps, output counters, source/corpus hashes and before/after runtime
identity. Hash consistency does not establish workload legitimacy.

Committed rate excludes the already-arrived first positive burst from both the
numerator and timing interval. Require nondecreasing counters and timestamps,
positive measured counter/time differences, bounded final output, successful
terminal usage and complete framing. TTFT uses first nonempty content or
reasoning, not the first metadata event. Failed or zero-interval observations
have no substituted throughput estimate.

Energy is the clipped trapezoidal integral of adjacent valid board-power
samples over the declared native-command window. Missing coverage makes total
energy unavailable; sampled energy is an estimator, not an exact physical
integral or wall-socket measurement. With `S` native successful tasks, report
`E/S` and `elapsed/S` only for `S > 0` and complete required coverage/denominator.
For `S = 0`, retain totals and an explicit undefined ratio, never zero cost.
Preserve failures and unsuccessful attempts in task-window totals.

Raw artifacts and source/recipe bindings protect against stale, changed,
mispaired and incomplete records. They are not independent attestation against
an operator coherently fabricating all producer bytes. Bind closure identities
through proof, build, actual serving instance and promotion; never trust a
self-declared PASS field or mount-path spelling as the corresponding fact.

### What optimality would require

The immediate deliverable is a verified feasible set and its measured Pareto
frontier. “Best measured so far” is the only optimization claim justified by
finite candidate measurements without a coverage certificate.

A global claim needs a precisely defined candidate space plus complete search
or sound dominance-preserving pruning over every excluded region. An analytic
cost bound must name required work/transfers, lifetimes, overlap and hardware
assumptions; calibrated timing estimates can prioritize experiments but cannot
certify pruning. A roofline for one chosen dense kernel is not a universal lower
bound for every equivalent algorithm. Quality bounds must use the actual native
rubric range, not an assumed score ceiling.

The proof chain is therefore: independent reference and input domain; legal
transformations with semantic/resource certificates; compiled implementation and
ABI refinement; legitimate runtime measurements; goal-indexed comparison; and,
only where available, search-coverage/upper-bound certificates. The Bend startup
proof establishes its stated allocation/layout/serialization laws; objective
laws establish decision algebra. The subsequently checked transaction,
ownership, ABI and numerical domains below establish their pure contracts,
not the remaining native GPU, recurrence, publication, measurement or
search-coverage obligations.

## Evidence currently available

| Evidence | What it proves | What it does not prove |
|---|---|---|
| [Native timing](../bench/results/native.json) | Historical short C1 decode 135.90–137.69 tok/s; 130.99–132.78 end-to-end | New recipe speed or near-native context |
| Same report, 65000-input request | Historical cold TTFT 74.668 s, client decode 114.944 tok/s | 128K–262K performance |
| [Cache 45K](../bench/results/cache-45k.json) | Salt-isolated emitted-token consistency, approximate KL 0.0002171873 | Full-vocabulary or broad quality parity |
| [KVarN repair](../bench/results/240k-packing-repair-01.json) | 90 attention + 2 status cases, zero compute-sanitizer errors | Full-model startup, capacity, cache or quality |
| [First candidate failure](../bench/results/240k-native-attempt-01.json) | Packed embedding arithmetic passed; KVarN startup failed | Any candidate throughput result |

Historical measurements used a 65536-context runtime. Keep their original
producer identities; do not rebind them to current source. Detailed reports
remain in [the result index](../bench/results/README.md), not as launch defaults.
The [video preprocessing OOM](../bench/results/multimodal-baseline.json) also
remains a real limitation. Enabling vision code does not prove memory capacity.

## Latest Bend/native evidence and completed capacity

The current compiler authority is the latest stable upstream release, pinned to
original **Bend 2.0.26** with its exact retained compiler/toolchain identity.
The unchanged root proof passed on the 2.0.26 release runtime in **65.65 s** with
a 1073741824-byte process stack and
`BUN_JSC_maxPerThreadStackUsage=536870912`. Its bundled Bun 1.4.0 needs this
prefix: the former `JSC_maxPerThreadStackUsage` invocation overflowed, including
with a 2 GiB process stack and a requested 1 GiB JSC stack. Only the resource
environment changed; the release checker and proof sources stayed unmodified.
The earlier unchanged root proof passed on 2.0.25 with a 1073741824-byte process
stack and `JSC_maxPerThreadStackUsage=536870912`; the default stack overflowed.
No comparator patch is required. Rebuild and re-admit production artifacts
after a compiler update; historical GPU evidence does not qualify a new build.
The earlier 2.0.20 root `PROOF.bend` check passed (`All terms check`, exit 0,
99.59 s) under the recorded resource settings: a 1073741824-byte stack limit,
disabled core dumps and `BUN_JSC_maxPerThreadStackUsage=536870912`, with telemetry
disabled. This used the original release, not a patched checker.

The earlier real CUDA acceptance-helper run passed **128 masks, 5500 rows and 80
invocations**, exercising eager and graph paths. This is compiled-policy plus
GPU acceptance-helper evidence, not full worker/KV-write/Mamba integration,
recurrence, publication or numerical-quality proof. The separate component
numerical suite has now passed with the narrower scope recorded below.

The native **262144 context / 263168 pool** service subsequently completed one
**262014 submitted-input + 128-output** request, with matching before/after
identity, zero cached tokens/retractions and finite aligned output logprobs.
The generation HTTP interval was **638.808 s**, not a throughput qualification.
The operator independently replayed the retained raw capacity evidence through
the capacity gate (48 hashed files), rather than relying only on its producer
summary. Seed **20260920** and the exact input/body hashes match the earlier
interrupted trial. Private review found a coherent initial geometric answer
and recorded forced continuation after EOS. See the
[capacity chronology](capacity.md#completed-native-request-and-earlier-interruption)
and [sanitized ledger](../bench/results/bend20-native-baseline-20260920.json).

The earlier request remains **inconclusive**: the **900-second guardian**
interrupted it with `RemoteDisconnected` and failed identity-after capture.
That failed attempt is not an OOM diagnosis or completed-output result. Its
historical FP8 recovery was authenticated. The later math window's guardian also
reported `baseline_restored_authenticated` with exit 0, as directly observed by
the operator. Neither recovery qualifies native context or confirms recovery
for any subsequent validation window.

Upstream already reserves **262528 RoPE rows**; the redundant constructor patch
was removed. That source correction is not itself capacity evidence. The earlier
startup reports below retain their original identities and chronology; one later
completed request and sampled math measurement do not establish full qualification.

### Guarded eight-stage Marlin candidate: sampled exactness, benchmark pending

The candidate image is
`sha256:94d6dd975e406413ff8cdaa2bbccbaa181c3760379dbaeb50072e774e54e90e8`.
It selects eight copy stages instead of the retained four only for original
M1–8, full-K, SM86 BF16/U4B8/group128 inputs without act-order or zero-points,
after the existing selector chooses 128 threads and an M8/N128/K64 tile.
The remaining guards require K divisible by128, group_blocks8, one block per SM,
non-atomic reduction and the existing shared reservation at least **51200 bytes**.
That conservative padded-M16 guard exceeds the selected M8 layout's **43008
addressed bytes**; neither number replaces the unchanged launch reservation.
The compiled Bend policy is the sole stage-selection authority; unmet guards
retain four stages. Grid, K stripes, reduction grouping and scratch are unchanged.
Artifact admission uses source schema9, verified schema6 and runtime wireV2
(`MARLIN_EIGHT_STAGE`); an always-fallback wire is rejected, not accepted as proof
that the new path ran.

The original Bend2.0.26 root proof passed in **67.69 s**, including **24**
[pipeline model laws](../bend/marlin_pipeline_laws.bend). Generation, compilation,
verification and four CPU consumers passed. The checked statements cover policy
and exact wire ordering, period-two ring phase through arbitrary wraps, complete
ordered tile/MMA traces including short tails, symbolic previous-accumulator
recurrence, and shared-layout/schedule arithmetic. They do **not** prove native
CUDA execution or F32 equivalence: integer/address refinement, operands and
scale addressing, async commit/wait and barriers, ring reuse/predication/drain,
compiler/foreign-IO fidelity, actual instruction rounding and intra/inter-CTA
reduction order remain external obligations. Seven primed groups and
`wait_group<6>` are checked arithmetic parameters, not a CUDA ordering theorem.

The real candidate JIT passed in **231.13 s**. Fresh guarded baseline/candidate
captures and their CPU comparison passed **624/624 bit-exact output fixtures**
and **624/624 eager/graph dispatch pairs**, with graph/scratch checks passing.
The observed selected kernel used117 registers versus108 for four stages;
both reported stack0/local0. Dynamic shared reservation101376 bytes and grid82
were unchanged. These are sampled compiled/GPU observations, not universal
numerical or model equivalence, occupancy evidence, or a throughput result.
Private evidence is retained under `/tmp/litos-recovery-ops-id8q0yvb/`:
`marlin-eight-stage-baseline-evidence-1`,
`marlin-eight-stage-candidate-evidence-1` and
`marlin-eight-stage-comparison-evidence-1`.

**The frozen benchmark is pending; no promotion is claimed.** The retained best
remains95.380797 tok/s. The full-K-grid and two-stage-pipeline candidates remain
rejected for their frozen-suite quality failures; synthetic kernel exactness
does not supersede those decisions (see [patch notes](../patches/NOTES.md)).

### Checked domains and direct GPU/runtime-control smoke

The subsequent root proof passed with **original, unmodified Bend 2.0.20**
(`All terms check`, exit 0, **127.01 s**) under the same 1073741824-byte stack,
disabled-core-dump and `BUN_JSC_maxPerThreadStackUsage=536870912` settings.
The four isolated proof domains passed in **0.21–0.26 s** each. The additions
are 17 Bend source files: transaction specification/implementation/laws/proofs
plus `RUNTIME.bend`, and four files each for ownership, ABI and numerics.
The root [proof entry point](../PROOF.bend) imports their proof modules.

| Checked domain | Representative statements | Native boundary still required |
|---|---|---|
| [Transaction](../bend/transaction_laws.bend) | `trace_refinement`, stale/unchecked publication rejection, `nonreset_poison`, all-pool publication, cancellation drain, graph/eager producer contracts, mirror rearm/reset and exact policy wire | Truthful complete producer observations, stream ordering, status generations and all-writer/reference quiescence |
| [Ownership](../bend/ownership_laws.bend) | Lease-generation ABA rejection, no release with references/readers/writers, reserved dummy protection, raw/preview/sealed transitions and committed-page sealing | Actual generations/refcounts, exact frontier completeness, global free-list and slot-map refinement; free-slot epochs are not page generations |
| [ABI](../bend/abi_laws.bend) | Four-word/block-eight transport, bonus provenance, strides, signed widening, low-bit narrowing and wrapping addition | Pointer/extent/alias/lifetime observations, C/CUDA lowering; logical lengths additionally require `SafeAdvance` and nonnegative representability |
| [Numerical](../bend/numerical_laws.bend) | Finite classification, ties-even/ties-away, packed-code round trip, bounded error, conditional strict argmax, identity-bound complete evidence | Native floating arithmetic, NumPy replay equivalence, loaded-model recurrence and full-vocabulary per-step margins; no task-quality theorem |

The exact **31-patch** image is
`sha256:e40fc9cbb0323826646d72bb497887e9328cc0781a5aaca0a66b3c063c97e4d5`.
That historical image used the original `bend-2.0.20-linux-x64` release,
`/usr/bin/clang-19` for retained CPU artifacts and
`/usr/local/cuda/lib64/libnvrtc.so` for the SM86 CUDA artifact, on the pinned
SGLang v0.5.19 base
`sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9`.
The GPU reports identify RTX 3090 / SM86, CUDA **13.0**, Torch **2.13.0+cu130**
and, for direct acceptance, Triton **3.7.1**. Retained source/build/native
identity hashes bind the smoke reports to their artifacts.

Private evidence is at
`/tmp/litos-recovery-ops-id8q0yvb/bend20-runtime-evidence-3`:

- `bend-flat-gpu.json`: **passed**, direct original Bend-compiled GPU leaf,
  **128 masks / 5500 rows / 80 invocations**, batches 1/17/128/129, eager and
  graph replay, unused output cells checked, **zero policy uploads**. This is
  new direct-leaf evidence, not a relabeling of the historical table helper.
  It is not evidence for KV writes, worker integration, accuracy or throughput.
- `runtime-control-gpu.json`: **passed, 18 cases**, elapsed **19.041 s**;
  `pool.clear + cuda.synchronize` cleanup passed. The fourth CPU artifact,
  [RUNTIME.bend](../bend/RUNTIME.bend), supplies compiled policies consumed
  through [the runtime-control patch](../patches/kvarn-bend-runtime-control.patch)
  by actual `mirrored_tail_slots()` and `finish_status_mirror()` methods.
  Coverage includes status **0/1/2/4/6**, unarmed rejection, rearm while a real
  writer is pending, current mirrors, write/release epoch invalidation,
  exact recount, busy refresh, draining both writers at reset and safe pinned
  storage reuse. Named pending cases required actual CUDA event queries to
  observe incompletion, rather than mocked completion.

The host-control smoke used **two small BF16 layers, four usable physical
pages and eight raw slots per layer** with real portable ownership methods.
Native-profile admission/attention, model execution, worker publication
callbacks and full worker graph replay were not exercised by that smoke.
The eventless status branch and synthetic missing-event corruption were not
tested. Existing asynchronous D2H mirrors remain the native boundary; the
integration adds neither per-token subprocess execution nor production D2H
transfers. These finite observations do not authenticate uninstrumented native
generations/refcounts/frontiers or establish compiler/CUDA semantics.

Two earlier retained preflight attempts failed before runtime cases: a stale
private schema gate, then a missing private package path. Both were corrected
only in fresh private diagnostics; both authenticated FP8 recoveries completed.
They are not source-kernel failure evidence. Numerical thresholds, graders and
benchmark protocol were unchanged. The adapter `ty` check passed; Ruff
diagnostics remain unsuppressed.

The image subsequently reached **authenticated native API readiness** after a
**78.07 s** readiness wait, candidate
`e3409f368646b05a28b4652b580849aa9019ae6a3f5c5b12ce8ef5755afec9a1`.
The existing unchanged `bench.decode` subsequently **completed, exit 0 in
126.98 s**, with one repetition at all **1024/8192/32768** depths under native
**262144**. Actual prompt counts were **1076/8244/32821**; every request emitted
**1024 completion tokens**, with `finish_reason=length`. The report is below
the same private evidence directory at
`native-c1-smoke/decode-depth-matrix.json`. This is real native serving smoke,
**not a comparable canonical primary-rate result, capacity qualification or
quality qualification**. Best measured run 2 remains
**93.0255 model-call tok/s versus 92.7021**, tiny reward **2/3**; it does not
qualify this image or full quality. Optimization resumes from that measured
baseline, not from a claimed speedup inferred from proofs.

### Component numerical run and harness controls

The actual `bench.numerical` run passed **exit 0 in 105.19 s** under protocol
`qwen-component-numerics-v2`; the operator independently replayed **576 events**.
Coverage includes `kvarn_attention`, `kvarn_native_context`, `kvarn_storage`,
`packed_embedding`, `dflash_commit` and `dflash_sampler`. The report hash and
private evidence pointer are retained in the
[ledger](../bench/results/bend20-native-baseline-20260920.json).

This exercises real native pools and the production commit runner with
deterministic toy draft projections, full-history traversal over repeated real
packed tiles plus a raw tail, and all **248320 embedding rows / 1271398400
values** hashed to the immutable oracle. The fixed component limitations remain:
KVarN error is relative to the dequantized packed-KV reference, not unquantized
KV; the traversal is not loaded-model capacity or quality proof; the commit
fixture does not exercise loaded-model projections, Mamba recurrence or scheduler
cancellation. Sampler coverage is greedy temperature 0, top-p 1, without
penalties or grammar—not non-greedy or finite-RNG-law coverage. There is no W4A8
claim, full served-path validation or model-quality qualification.

The first cold numerical attempt is preserved: two suites failed only with
`ModuleNotFoundError: bend`. Explicit `docker-exec` `PYTHONPATH=/opt/qwen`,
matching the immutable image's working directory/package, repaired the import
environment; no gate, tolerance or workload changed. Its guardian reported
`restored_authenticated` and exit 0. The second numerical candidate remains
live and unqualified at this record; its eventual recovery is not yet confirmed.

The lifecycle fix also passed five real CPU cases: clean completion, abrupt
double-fork, rejection of zero-exit live orphans, acceptance of zombie-only
descendants, and TERM-time fork/KILL cleanup. An unrelated sentinel survived.
Seventeen descriptor rejection controls and a live positive control passed.
These controls do **not** complete the still-pending plain canonical
`bash autoresearch.sh` math/C1 invocation.

## Refactored FP8 hardware trial

[The bounded startup trial](../bench/results/refactor-fp8-startup.json) requested
context 262144 and pool 263168 on the RTX 3090. The actual GPU profiler capped
both target and draft pools at **68004 tokens**. This does not meet the objective.
The target/draft weights were 15.90/1.20 GB; logged target/draft KV was 2.08/0.64 GB,
with about 1.79 GB of Mamba state/intermediates. These are rounded engine figures.

Sampled startup VRAM peaked at 22978 MiB. The API was not ready before the bounded
stop while target-verify graph capture was still running. **No deep request was
submitted**, so there is no HTTP capacity rejection, completed prefill, output,
quality result or useful inference speed. Incomplete capture is not proof of a
graph defect. Concurrent CPU preparation also prevents performance claims.

The candidate had zero restarts and was stopped deliberately. The original
service was restored with authenticated health, model inventory and a short
completion check. No power/fan policy or permanent deployment was changed.

## Full-qualification capacity matrix

For full qualification, run each row independently for baseline KV, FP8 KV,
applicable upstream compression and the explicit KVarN experiment. Record
unsupported hardware paths as unsupported, not tested failures. Reserve
meaningful output inside the total context plus engine accounting overhead.
These requirements do not add a capacity ladder to `autoresearch.sh`.
The implemented automated capacity gate admits one exact near-native request per
arm; passing that gate does not establish the broader study or the other
promotion requirements below.

| Total context | Startup | Deep prefill + output | Peak VRAM / finite numerics | Direct-context quality | Status |
|---:|---|---|---|---|---|
| 131072 | — | — | — | — | Not run |
| 163840 | — | — | — | — | Not run |
| 196608 | — | — | — | — | Not run |
| 229376 | — | — | — | — | Not run |
| 245760 | — | — | — | — | Not qualified; earlier startup failure |
| 262144 | Native API authenticated, pool263168 | One 262014-input + 128-output request completed; earlier interrupted attempt remains inconclusive | Finite aligned output logprobs; standalone component numerical suite passed, not peak-memory or full served-path proof | Not established by synthetic capacity probe | Not qualified. First sampled tiny-math/C1 result is separate; full promotion gates remain pending. Earlier FP8 pool68004, packed 0.94 profile rejection and 0.98 wiring failure remain historical. |

A row passes only after startup, near-depth request acceptance, completed
prefill, meaningful subsequent output, measured VRAM safety, finite numerics
and acceptable quality all pass. Synthetic random/repeated tokens can establish
allocation behavior, not retrieval or useful output. Use upstream direct-context
environments for capability; file-search tasks measure a different workload.

## Promotion sequence

1. **Build and source:** clean pinned upstream plus selected Git series applies;
   compile/import under the pinned image. Identify actual built image digest,
   patch hashes, model inventories, launch configuration and host driver.
2. **Correctness:** test quantized loading, packed arithmetic, DFlash2 rejection
   positions, non-greedy transforms, penalties, grammar/EOS, graph/non-graph
   execution, recurrence and cache restoration. Kernel repair evidence must
   not stand in for an end-to-end sampler check.
3. **Capacity and cache:** complete all capacity rungs that fit, then cold/warm
   identical prefix, extension and divergent continuation at meaningful depths.
   Record startup, TTFT, cache hits, retractions, peak VRAM and restoration.
   This promotion study is separate from the tiny measurement; startup alone
   cannot pass it.
4. **Capability:** run frozen Prime Envs smoke/quick/full for target-only and
   each proposed patch/quantization change. Declare per-environment tolerances
   before runs; retain errors, truncations, seeds and traces. No accepted
   non-inferiority threshold or passing result exists yet.
5. **Performance:** interleave repeat A/B runs using official SGLang utilities;
   fill the optimization ladder, context-depth C1 table, C2/C4 crossover and
   host power sweep. Promote only reproducible improvements with acceptable
   quality and operating margin. A fast shallow run is insufficient.

## KVarN maintenance window: no candidate launched

[The second window](../bench/results/refactor-kvarn-startup.json) expired before
candidate launch because the agent resumed after the independent recovery
deadline. The original service was restored and passed authenticated health,
model and short-completion checks. **No KVarN GPU measurement was made in that window.** This is
not an allocation failure, startup failure or capacity result for KVarN. No
further GPU trial was made during that historical run.

## Experimental native KVarN sizing

At that historical stage, `kvarn-native-rungs.patch` was a separate experimental
change after the byte-preserving ten-stage migration. It admitted the six
native/eager DFlash2 context rungs with exact `context + 1024` pools and derived
page counts, rejecting an actual pool smaller than requested rather than
advertising lower allocation as success. CPU checks covered 132 admission/budget
cases; all eleven patches applied to the pinned commit. That was not GPU capacity
evidence.

Tile geometry, workspace, null-page and error-status checks stayed intact. At
that stage graph mode remained at its prior 245760 envelope. The KVarN target-only
guard blocked the ordinary worker because it did not check native sticky error
status before publication. That history is not a claim about the latest graph
envelope or a reason to remove the guard for a comparison. FP8/BF16 target-only
controls use a different KV policy and must be labeled as confounded comparisons.

## Packed trial exposed a launcher defect

[The first packed-path GPU trial](../bench/results/packed-kvarn-262144.json)
used image `8a1eeb69…` but omitted the packed embedding activation flag. The
loader skipped the packed embedding parameters and allocated a dense-sized
embedding. It then rejected requested pool263168 against profiled139520.
**This is not a valid packed-model capacity result.** No request or capability
score was produced. The scheduler's explicit process-tree termination must not
be mislabeled as a CUDA OOM; Docker reported `OOMKilled=false`.

The subsequent correction bound the explicit representation to its loader flag,
`safetensors` load format, BF16 dtype and DFlash2 requirement. File hashing alone
does not prove that the intended model-loading branch was selected. Corrected
images needed separate runtime qualification; the old image remains evidence.

The next separate experimental patch, `packed-embedding-lora-defaults.patch`,
corrected upstream's disabled LoRA defaults (`None`) without enabling LoRA. Only
identity `None` or `False` was accepted for the two LoRA flags; supplied paths,
true values or invalid types were rejected. All other guards remained unchanged.
Forty-two CPU constructor checks passed; the complete twelve-stage series applied
to the pinned source. That was compatibility evidence, not a GPU loader pass.

## Corrected packed image: first GPU admission result

The corrected twelve-patch image `880b09a2…` binds the packed representation to
its loader flag, `safetensors`, BF16 dtype and DFlash2, accepts only genuinely
disabled LoRA defaults, and adds a bounded 0.94–0.98 memory-fraction control.
Its CPU boundary and constructor checks passed. A first corrected-window attempt
was cancelled by the wall-clock guard before anything was stopped; the baseline
never went down.

[The 0.94 admission window](../bench/results/packed-kvarn-094-admission.json)
then loaded the packed target for real: the gate was bound, no loader skip
warning appeared, and the target/draft weights took 14.75/1.22 GB. The KVarN
profiler backed only **211328 tokens** against the requested 263168 pool cap,
and the scheduler refused to advertise an unbacked context length. This is a
valid packed-load startup rejection, not a capacity result: no readiness,
VRAM-at-ready, deep request or quality result came from that attempt. The
conditional 0.98 retry was not taken because under seven minutes remained; the
later separate 0.98 window is recorded below. The baseline was restored and
re-authenticated.

[The 0.98 admission window](../bench/results/packed-kvarn-098-admission.json)
then passed the strict pool-cap check for the first time: no profile rejection
occurred, the Mamba cache and both KV pools were allocated, and 1.09 GB
remained available. Startup still failed before API readiness, now at
attention-backend wiring: upstream's `HybridLinearAttnBackend` reads
`token_to_kv_pool`, `req_to_token_pool` and `kv_index_translator` from its
full-attention child, but the experimental `KVarNAttnBackend` constructor never
set them. This is a source-level integration gap in the patch chain, not a
memory-capacity result. **No API readiness or deep-request evidence came from
that attempt**; its probe was deferred pending a new patch stage/image and
separate checks. Later authenticated native readiness is recorded above.

## Known blockers

CPU probes previously found DFlash selector differences for top-k/top-p,
`min_p`, frequency/presence and repetition penalties. Local sampler repairs
remain experimental until GPU and target-only quality comparisons pass.
KVarN now has one completed full-model near-native allocation/generation request
and the first sampled tiny-math/C1 result. Standalone component numerics passed,
but loaded-model numerical/recurrence/cache, direct-context quality and
full-profile comparison evidence remain incomplete.
Full CPU artifact reproduction has passed, including exact inventories and the
all-row proof; it does not establish packed-runtime inference parity or capability
preservation. The descriptor-based plain launcher still needs its own execution.

A 280 W host cap was used historically. It is not a recommended knee for the new
recipe. No canonical 200–350 W sweep has completed. Do not change host fan or
power policy from a container.

See [benchmark protocol](benchmarks.md) for frozen workloads and measurement
semantics, and [Prime Envs](../eval/README.md) for evaluator compatibility.
