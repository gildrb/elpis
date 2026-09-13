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
| 262144 | — | — | — | — | FP8 pool68004; no deep request |

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
model and short-completion checks. **No KVarN GPU measurement exists.** This is
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
