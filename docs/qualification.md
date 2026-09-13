# Runtime measurements and qualification

The selected runtime is Qwen3.8-27B on one RTX 3090: SGLang v0.5.19,
W4A16 target and DFlash2 draft, block 8, context 65,536, output budget 8,192,
C1, token pool 66,560, K8, FP8 KV, BF16 Mamba state and `NCCL_MAX_CTAS=1`.
The exact image, source and model hashes are in the repository manifests.

## Measured performance

Two native short timing runs completed 8/8 requests each:

| Metric | Run A | Run B |
|---|---:|---:|
| Decode tokens/s (reciprocal mean TPOT) | 137.686 | 135.901 |
| Aggregate output tokens/s | 132.778 | 130.990 |
| Input / output tokens | 1,130 / 7,829 | 1,130 / 7,829 |
| Cached prompt tokens | 0 | 0 |

A cold 65,000-input / 128-output request measured 74.668 seconds to first
token and 114.944 client decode tokens/s. These short and long metrics use
different definitions; neither guarantees throughput on other workloads.
The 280 W value is the host power cap, not measured power draw or energy.

The eight public prompts in `bench/throughput-prompts.jsonl` are retained only
as a timing control for these measurements. They are not the quality benchmark.
The easy numeric and passcode gates have been removed. Use the fresh procedural
suite in [benchmarks.md](benchmarks.md) for reasoning measurements.

## Capacity and cache scope

Bounded capacity requests completed 57,342 input + 8,192 output and 65,406 input
+ 128 output tokens. Native maximum input was 65,530; input/output accounting
reserves two tokens. Over-budget output may be clamped. Advertising 65,536
context alone does not prove allocated capacity.

The measured generated-prefix probe reused 65,024 cached tokens and aligned
128 emitted token IDs against cold recomputation. Its emitted-token approximate
KL was 0.0000148516, below the predeclared 0.001 cutoff. This is not full-vocabulary
KL, broad reasoning parity, or proof for every checkpoint boundary.

[Native results](../bench/results/native.json) preserve allowlisted measurements
and exact metric/fixture provenance. Private raw outputs are not shipped.

## Salt-isolated cache measurements

A fresh 45,000-input probe reused 45,056 tokens and aligned 128 emitted tokens
against a separately salted cold recomputation. Approximate KL was
0.0002171873, below 0.001, with zero retractions. See
[the allowlisted result](../bench/results/cache-45k.json).

A separate 45,900-input probe reused only 45,888 tokens, not beyond its original
prompt. It therefore stopped as **inconclusive**, without a numerical verdict.
See [that result](../bench/results/cache-45900.json). Both ran on the shared live
service without a restart or global cache flush. Neither establishes broad
conversational quality or every generated-checkpoint boundary.

## Current qualification limits

The Docker/Nix packaging and recovery changes require separate live qualification.
CPU builds and source checks do not establish cold-boot, suspend/resume, scheduler
recovery, or long-request behavior under the new supervisor. The unchanged model
and runtime bytes do not by themselves prove lifecycle equivalence.

Reasoning, conversation-state retention, and cache consistency are separate
measurements. No broad quality threshold or universal always-on guarantee is
claimed from the old short fixture. New results must identify their frozen plan,
model/source identities, errors, truncations and cache state. Shared-load timings
must not be presented as exclusive GPU benchmarks.

## Held-out reasoning evaluation

The fixed nine-stratum hard suite scored **78/180 (43.3%)** at an **8,192-token**
output cap with thinking requested. There were **96 length truncations** and
**6 incorrect completed answers**. API, parser, scorer and generation failures
were all zero. All 180 requests remain in the accuracy denominator; no passing
threshold was declared. See [reasoning-evaluation.json](../bench/results/reasoning-evaluation.json).

| Family | Full credit | Truncated | Incorrect completed |
|---|---:|---:|---:|
| Knights/Knaves | 57/60 | 3 | 0 |
| Zebra | 17/40 | 23 | 0 |
| Conditioned shortest path | 2/40 | 37 | 1 |
| Sokoban | 2/20 | 13 | 5 |
| RE-ARC | 0/20 | 20 | 0 |

The evaluation used fresh seeds and excluded every prompt in the original pilot's
banks. The original frozen producer `cb941c7a…`, plan, transport and dependency
lock were verified; only evaluation mode, sample count and pilot binding differed
from the original 8K pilot protocol. This is not a run of the newer bank-comparison
producer `0d76cff4…`. The separate **13/18 at 32K** reused pilot questions after
observing truncation and remains a post-hoc budget diagnostic, not held-out evidence.

Read-only artifact checks verified all 360 generated entries' seed derivations
and prompt commitments, zero duplicate/pilot-overlap prompts, and all 180 raw
response/result/checkpoint records. The 80 conditioned path oracles across both
banks were independently checked by BFS. This audit did not rerun every upstream
scorer or issue model requests. Private seeds, prompts, answers and raw responses
remain unpublished.

The run emitted **1,096,845 output tokens** over **6,000.609 seconds of summed HTTP
request time**, or **182.789 output tokens/s**. This shared-service HTTP metric is
not decode speed, exclusive GPU performance, or total benchmark wall time. It
excludes initial bank generation and CPU scoring. The result establishes limited
quality under this specific task distribution and output budget. Truncation does
not establish whether a task would be solved with more budget, and public task
families may still be familiar to the model.

## Fresh discovery pilots

The harder nine-stratum reasoning pilot scored **9/18** at an 8,192-token output
budget. The other nine requests ended at the token limit; there were no incorrect
completed answers or API/parser/scorer failures. This is a small discovery pilot,
not held-out qualification. See [reasoning-pilot.json](../bench/results/reasoning-pilot.json).

The client-neutral synthetic conversation pilot scored **36/36** across twelve
matched cases with full-history, fixed-summary and direct-control arms. It recorded
no stale or unsupported values, API/parser failures or truncations. These static
fixtures do not establish native compaction correctness or explain real-session
failures. See [conversation-pilot.json](../bench/results/conversation-pilot.json).

Both pilots used the unchanged shared live service. Their request timing includes
HTTP overhead and is not an exclusive GPU decode-rate measurement. Private tasks,
answers, seeds and raw responses are not published.

A post-hoc rerun of the **same eighteen tasks** at 32,768 output tokens scored
**13/18**, with four truncations and one incorrect completed answer. It had no
API/parser/scorer failures. The verified bank import changed only `max_tokens`;
it is not a fresh held-out evaluation. More budget helped, but did not eliminate
failures. See [reasoning-budget32k.json](../bench/results/reasoning-budget32k.json).

## Bounded baseline multimodal diagnostic

A separate private four-case control on the unchanged baseline did not pass:
three image cases had exact-label OCR errors, and one video request returned
HTTP 500. Visual inspection confirmed that the image pixels matched the frozen
oracles; the errors were not caused by clipped or incorrectly drawn labels.

The bounded server traceback identified CUDA out-of-memory during video
preprocessing resize: a 12 MiB allocation failed with 3.19 MiB reported free.
The following image request completed, so this observation does not establish a
service restart or permanent failure. It also does not establish ownership of
every GPU allocation reported in the traceback.

These private controls are not a shipped multimodal benchmark, a reasoning score,
or proof of compaction or cache corruption. They expose baseline OCR and memory
limits. Candidate multimodal parity remains inconclusive. The later packed-embedding
GPU arithmetic proof passed, but candidate startup failed before inference; no
new production configuration has been activated. Keeping vision code enabled is not proof that every
image/video workload fits in memory.

## Packed-embedding comparison trial

The approved 64K comparison trial verified all 248,320 embedding rows bit-for-bit
on the GPU with unchanged inputs. Candidate startup then failed its strict draft
directory inventory check: the supplied directory also contained `.cache` and
`README.md`. No candidate generation probe ran. The guard was not relaxed and
no model files were changed.

Guarded recovery restored the original service identity, authenticated health,
and native short compatibility check in about 95 seconds after rollback began.
[Trial evidence](../bench/results/packed64-trial.json) records the failed startup
separately from successful restoration. This does not qualify packed-candidate
inference, multimodal parity, or 240K operation.

The final context target remains **245,760 total tokens with DFlash2 + KVarN**,
not a 64K production limit or compaction recommendation. The reference project's
262,144-token non-speculative profile is a different configuration. Its vLLM
measurements are not measurements of this SGLang implementation.

## Sampling correctness blocker

CPU probes against the pinned stock image reproduced differences between the
DFlash2 selector verifier and ordinary autoregressive sampling: combined
top-k/top-p filtering, ignored `min_p`, stale per-row frequency/presence penalties,
and repetition penalties ignored even on the first verify row. The helper-source
hashes were checked against the image. These are not GPU parity results and do
not establish the cause of any particular client conversation failure.

A separate repair is being prepared without changing SGLang, DFlash2, the model,
or the context/output budgets. It must preserve filter order, grammar/EOS masks,
logit bias, returned logprobs and accepted-prefix state ownership. Error status
must be checked before indexing sampled tokens or committing state. Until the
repair is qualified, greedy/no-penalty measurements cannot establish broad
sampling correctness or authorize final promotion.
