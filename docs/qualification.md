# Qualification status and promotion gates

**The native-context recipe is not qualified.** The objective is 262144 total
tokens with DFlash2 on one RTX 3090. No completed near-native full-model run or
Prime Envs quality comparison is recorded. The running historical service is
not proof that the refactored Docker build works.

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
