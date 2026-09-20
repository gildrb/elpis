# Qualification status and promotion gates

**The native-context recipe is not qualified.** The objective is 262144 total
tokens with DFlash2 on one RTX 3090. No completed near-native full-model run or
Prime Envs quality comparison is recorded. The authenticated Qwen FP8 fallback
serves 65536 tokens; it is recovery capacity, not a native-context qualification.

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

The primary observed vector is `(Qe for every e, Td for every d, -Fd for every d)`.
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
only where available, search-coverage/upper-bound certificates. The current Bend
startup proof establishes only its stated allocation/layout/serialization laws.
New objective laws establish decision algebra, not the missing GPU, recurrence,
publication, numerical, measurement or search-coverage obligations.

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

## Required capacity matrix

Run each row independently for baseline KV, FP8 KV, applicable upstream
compression and the explicit KVarN experiment. Unsupported hardware paths must
be recorded as unsupported, not tested failures. Reserve meaningful output
space inside the total context, plus engine-required accounting overhead.

| Total context | Startup | Deep prefill + output | Peak VRAM / finite numerics | Direct-context quality | Status |
|---:|---|---|---|---|---|
| 131072 | — | — | — | — | Not run |
| 163840 | — | — | — | — | Not run |
| 196608 | — | — | — | — | Not run |
| 229376 | — | — | — | — | Not run |
| 245760 | — | — | — | — | Not qualified; earlier startup failure |
| 262144 | — | — | — | — | FP8 pool68004; packed KVarN 0.94 profile-rejected (211328<263168); 0.98 pool cap passed but hybrid wiring failed; no deep request |

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
further GPU trial was made in this run.

## Experimental native KVarN sizing

`kvarn-native-rungs.patch` is a new, separate experimental change after the
byte-preserving ten-stage migration. It admits the six native/eager DFlash2
context rungs with exact `context + 1024` pools and derived page counts. It rejects
an actual pool smaller than the request rather than silently treating a lower
allocation as success. CPU checks cover 132 admission/budget cases; all eleven
patches apply to the exact upstream commit. This is not GPU capacity evidence.

Tile geometry, workspace, null-page and error-status checks stay intact. Graph
mode remains at its prior 245760 envelope. KVarN target-only execution remains
blocked: the ordinary worker does not yet check native sticky error status before
publishing results. Do not remove that guard merely to obtain a comparison.
Target-only FP8/BF16 controls are available, but a different KV policy is a
confounded comparison and must be labeled as such.

## Packed trial exposed a launcher defect

[The first packed-path GPU trial](../bench/results/packed-kvarn-262144.json)
used image `8a1eeb69…` but omitted the packed embedding activation flag. The
loader skipped the packed embedding parameters and allocated a dense-sized
embedding. It then rejected requested pool263168 against profiled139520.
**This is not a valid packed-model capacity result.** No request or capability
score was produced. The scheduler's explicit process-tree termination must not
be mislabeled as a CUDA OOM; Docker reported `OOMKilled=false`.

The correction must bind the explicit representation to its loader flag,
`safetensors` load format, BF16 dtype and DFlash2 requirement. File hashing alone
does not prove that the intended model-loading branch was selected. Corrected
images need separate runtime qualification; the old image is retained for evidence.

The next separate experimental patch, `packed-embedding-lora-defaults.patch`,
corrects upstream's disabled LoRA defaults (`None`) without enabling LoRA. Only
identity `None` or `False` is accepted for the two LoRA flags; any supplied paths,
true values or invalid types are rejected. All other guards remain unchanged.
Forty-two CPU constructor checks passed; the complete twelve-stage series applies
to the pinned source. This is compatibility evidence, not a GPU loader pass.

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
VRAM-at-ready, deep request or quality result exists. The conditional 0.98
retry was not taken because under seven minutes remained in the window; it runs
in a separate window with the same image and protocol. The baseline was
restored and re-authenticated.

[The 0.98 admission window](../bench/results/packed-kvarn-098-admission.json)
then passed the strict pool-cap check for the first time: no profile rejection
occurred, the Mamba cache and both KV pools were allocated, and 1.09 GB
remained available. Startup still failed before API readiness, now at
attention-backend wiring: upstream's `HybridLinearAttnBackend` reads
`token_to_kv_pool`, `req_to_token_pool` and `kv_index_translator` from its
full-attention child, but the experimental `KVarNAttnBackend` constructor never
set them. This is a source-level integration gap in the patch chain, not a
memory-capacity result. **No admission, readiness or VRAM evidence exists**;
the deep-request probe stays deferred. The fix must ship as a new patch stage
with a new image identity and its own CPU checks.

## Known blockers

CPU probes previously found DFlash selector differences for top-k/top-p,
`min_p`, frequency/presence and repetition penalties. Local sampler repairs
remain experimental until GPU and target-only quality comparisons pass.
KVarN's corrected packing passed small GPU fixtures but has no successful
full-model near-native result. Full CPU artifact reproduction has now passed,
including exact inventories and the all-row proof. That does not establish packed
runtime inference parity, native capacity or capability preservation.

A 280 W host cap was used historically. It is not a recommended knee for the new
recipe. No canonical 200–350 W sweep has completed. Do not change host fan or
power policy from a container.

See [benchmark protocol](benchmarks.md) for frozen workloads and measurement
semantics, and [Prime Envs](../eval/README.md) for evaluator compatibility.
