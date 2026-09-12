# Current 64K SGLang qualification

## Configuration and status

Current profile: `nccl-max-ctas-1-current`, **`NCCL_MAX_CTAS=1`**, context **65,536**, token-pool cap **66,560**, static memory fraction **0.94**, prefill chunk **1024**, one running request (**C1**), Mamba cache **K8**, DFlash block **8**, draft window **2048**, `extra_buffer`, BF16 Mamba state, FP8 KV, input-logprob chunk **256**, sleep-on-idle and **280 W power cap**. No NCCL minimum-CTA/channel overrides are selected. The pool flag is an upper bound, not a guaranteed minimum allocation; current runtime metadata reports an actual pool of **66,560**.

Runtime is `lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9`, stock kernels and the three mandatory reviewed replacements from `gildrb/sglang` revision `3958762c198b7e9e0167e6aedda1b8c3f9a8afb1`. Target is `compact-target-rholsc8k/artifact`; draft is `Qwen3.8-27B-DFlash2-W4A16`. Source/model inventories and two-phase guards remain mandatory. Current entrypoint SHA256 is `c994f0a56914b8dddba2d347cbac5ee963af04a2d11818321979e4a622a108dd`. Runtime reported ready, health HTTP 200, context 65,536, pool 66,560 and maximum input 65,530.

NixOS activation has not been performed. Before activation, the consumer must pin and validate the exact inference and dotfiles revisions, then satisfy staging, backup and transaction gates. The sanctioned staged activation/reboot unit is allowed by passwordless sudo and reboots the host. Runtime health and benchmarks do not establish consumer closure validation or system activation.

## Native short and long measurements

| Native run | Completed | Decode tok/s | Aggregate output tok/s | Mean TPOT ms | Mean TTFT ms | Benchmark wall s |
|---|---:|---:|---:|---:|---:|---:|
| A | 8/8 | 137.686001940 | 132.778447411 | 7.262902444 | 162.468612875 | 58.962882551 |
| B | 8/8 | 135.900829746 | 130.989520388 | 7.358306803 | 168.374690124 | 59.768140053 |

Both runs had **1,130 input / 7,829 output tokens**, zero cached prompt tokens and exit 0. Decode is `1000 / mean_tpot_ms`, using arithmetic mean request TPOT. Aggregate output is output tokens divided by benchmark wall time. Neither is a universal throughput guarantee. Invocation wall brackets include work outside the benchmark's reported duration; do not substitute one denominator for the other. Cache flushing does not unload weights or compiled graphs. Two short runs do not establish text identity or a broad latency distribution.

Cold **65,000 input / 128 output** passed HTTP 200 with zero cached tokens/retractions. Client TTFT was **74.668278194 s**, client decode **114.944469652 tok/s**, and client duration **75.773159537 s**. Client decode uses `(completion_tokens - 1) / (client_end - first_positive_completion_event)`, not reciprocal mean TPOT. Streaming chunks can contain multiple tokens. This full-context measurement is lower than the short-suite decode values. Input count divided by TTFT includes overhead, not just GPU prefill.

A separate full-input-logprob request returned HTTP 200 with **65,000 rows**, **128 outputs**, zero cached tokens/retractions and duration **77.594354026 s**, finish reason length 128. These are bounded capacity probes, not arbitrary-input or concurrent-long-request OOM guarantees.

## Numeric quality and generated-checkpoint reuse

The current numeric gate passed **191/200 (95.5%)** in **334.177168214 s**, with **nine failures**, mean **379.95 output tokens**, one worker and exit 0. It used the unchanged `gsm8k-bench.py` / `gsm8k-200.json`, temperature 0, thinking disabled and a 768-output-token cap; fixture SHA256 `c33dcc6090f023fef25fe87711f6bd09d4de81658edb14468162cc9a9e5679fe`. The existing 95% gate passed. The current sanitized report does not enumerate individual failures, so no cap-hit breakdown or independent full rescore is claimed. This is one capped numeric fixture, not broad quality or distribution equivalence.

The same-process checkpoint probe reused **65,024 cached tokens**, beyond the first **65,000-input** prompt. Its second request had **65,129 inputs and 128 outputs**. Cold recomputation had **65,257 input-logprob rows**, zero outputs, zero cached tokens and zero retractions. The final **128 output token IDs** aligned. The diagnostic is `mean(expm1(cold_logprob - warm_logprob) - (cold_logprob - warm_logprob))`, measured **1.485160174869604e-05**, below the predeclared **0.001** cutoff. This emitted-token estimator is **not full-vocabulary KL**.

This supports the measured `extra_buffer` generated-prefix path only. It does not qualify `extra_buffer_lazy`, every checkpoint boundary, cancellation/reclamation, arbitrary concurrency or broad speculative/non-speculative equivalence. The separate FlashInfer window finding remains draft-only; no target-greedy accepted-output divergence is established here.

## Admission, output budget and retrieval

Native maximum input is **65,530**, not 65,536. Combined input/output accounting reserves two tokens. Current probes:

| Input / requested output | Observed response |
|---|---|
| 57,342 / 8,192 | HTTP 200, 8,192 outputs; 65,534 combined; zero cache hits/retractions; finish length 8,192 |
| 65,406 / 128 | HTTP 200, 128 outputs; 65,534 combined; zero cache hits/retractions; finish length 128 |
| 65,529 / 6 | HTTP 200, clamped to five outputs; zero cache hits/retractions; finish length 5 |
| 65,536 / 1 | HTTP 400 |

These show request-specific clamping and rejection, not uniform over-budget rejection or universal no-OOM behavior. The 8,192-output probe is **capacity evidence only**: cumulative SSE client parsing caused backlog, with client wall **185.904314 s** versus server E2E **136.973994 s**. Do not report its client-derived rate as GPU decode speed or compare it with the declared native metrics.

The separate synthetic retrieval probe returned HTTP 200 with **65,000 actual inputs, 25 outputs and zero cached tokens**, in **76.175448 s**. Both planted facts passed at offsets **6,503 / 32,525**. The payload was validated for unique facts, retained question and chat framing. This is one two-fact spot check, not broad long-context comprehension or position coverage.

## Hermes compatibility

A fresh-home Hermes task passed after native discovery of context **65,536**, with **no context override**. It ran `cat /fixture/README.md`, returned the correct cited facts, and completed a final answer. Exact-session resume passed with the prior tool result in history and **zero new tool calls**. Native auxiliary title generation also passed. This is bounded agent compatibility, not a broad agent benchmark. Persisted `cache_read_tokens` was **0**: conversation-history reuse is proven, not a measured prefix-cache hit.

Task wall time was **15.538119 s**; resume wall time **3.893181 s**. These are task-level observations, not decode benchmarks. Main requests used temperature 0, max 512 outputs and thinking disabled. The successful title used native defaults. A separate current native title replay passed HTTP 200 and returned a valid JSON title completion with temperature 0.3, no explicit max-token setting and no thinking override; it returned 519 completion tokens, including 502 reasoning tokens. Do not combine auxiliary-title usage with main task totals or infer broad tool/agent reliability from this bounded task.

## Power and concurrency scope

The configured 280 W value is a cap, not measured draw or energy. Active-power performance, idle savings and queue performance were not measured here. C1 remains selected; no batching benefit or simultaneous long-request capacity is qualified. No phase-aligned energy or tokens/J result is claimed.

## Reproduction and evidence

Use [README.md](README.md) for the exact native short-fixture command, approved exclusive access, authentication, cache flushing and private output handling. Publish only allowlisted metrics, never raw `server_info`, keys, private prompts or generated text.

The long-capacity input repeats public LongBench-v2 Kalamang material; it is not a purely synthetic corpus. The UUID prefix is already present in the sample, not a proven freshly added cache-busting prefix. Preparation used the pinned image helper `sglang.test.kl_test_utils.get_input_ids`, `random.seed(0)`, `max_prompt_tokens=3000`, `num_samples=48`, `trust_remote_code=False` and the retained tokenizer. Dataset-cache metadata identifies `THUDM/LongBench-v2` train revision `2b48e494f2c7a2f0af81aae178e05c7e1dde0fe9`. The helper did not explicitly pass a dataset revision. Independent rebuilding must pin that revision and verify the hashes; a fresh network reconstruction was not run here. The frozen 48-sample fixture SHA256 is `df118399f26d3550f1d23e937734d980831661df1584099617a53de1ba5ffc13`. The first native fixture has 4,033 token IDs; its canonical compact ID-JSON SHA256 is `036a9ac23c3ade2524593e91a6fc1314469d83a708b935099ab222d870dfe735`. Construct `seed24000 = (first4033 * 6)[:24000]`, then `long_ids = (seed24000 * 3)[:N]`. Keep long-request token counts tokenizer-verified and record actual response metadata; full-input-logprob output must contain the expected row count.

The retained procedure is documented at `/tmp/inference-64k-qualification-dkzu7258/methodology-sanitized.md`; that file describes the protocol, not the current run results. Native capacity requests use authenticated `/generate` with exact `input_ids`, temperature 0, `ignore_eos=true` and the stated output budget. Full-input-logprob requests add `return_logprob=true`, `logprob_start_len=0`, `top_logprobs_num=0`. Each cold probe first requires successful POST `/flush_cache`, without restarting. For checkpoint reuse, append the first 128 output IDs and token ID 11 to the 65,000 inputs; request 128 outputs with `return_logprob=true`, `logprob_start_len=-1` and no flush. Append those outputs, flush, then recompute full input logprobs with zero new tokens. Align the final 128 token IDs before scoring. Client long-probe decode is `(completion_tokens - 1) / (client_end - first_positive_completion_event)`; it is not the short suite's reciprocal mean TPOT metric.


Current native evidence: `/tmp/inference-64k-closeout-lc6qsqyl/final-max-ctas-results-native.json`. Current Hermes evidence: `/tmp/inference-hermes-64k-retry-wizy3p6a/hermes-result.json`. [benchmark-results.json](benchmark-results.json) is the repository's sanitized current result record. Local `/tmp` paths are evidence locations, not durable artifact hosting. All performance and quality values above come from the current `NCCL_MAX_CTAS=1` report; model/source provenance and fixture recipes are not runtime measurements.
