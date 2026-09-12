# Current SGLang qualification

## Configuration and deployment status

- Runtime: SGLang v0.5.19, image `sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9`, with packed-head, quantized draft-FC and Mamba checkpoint corrections. Public source: `https://github.com/gildrb/sglang`, branch `fix/v0.5.19-packed-head-dflash-fc`, commit `3958762c198b7e9e0167e6aedda1b8c3f9a8afb1`.
- Selected profile: compact Qwen target, DFLASH block 8, stock kernels, `extra_buffer`, one active server request, context **24,576**, input-logprob chunk **256**, `--sleep-on-idle`, and **280 W power cap**. A cap is distinct from actual draw; current NVML sample measurements and cold-input timing are recorded below.
- Qualified artifact: `/mnt/ssd/storage/ai/qwen3.8-27b/models/compact-target-rholsc8k/artifact`; its parent contains `validation.json` and `convert.py`. Embedding conversion matched all 248,320 rows against the packed-value reference, with unrelated tensors preserved.
- Inference integration `0662029` and evidence `2498b8a` are pushed. Locked `run-linux-validation.sh --host computer --without-vm` passed: all 27 flake checks, native contracts and the exact host closure built. **No activation or reboot occurred; runtime handover remains pending.** The active cap is operator-reported as 280 W; declarative activation is not established by the build.

## Current native chat, cold-input, active-power and idle measurements

Canonical sanitized post-`--sleep-on-idle` evidence: `/tmp/inference-sleep-idle-1myt_akk/current-measurements.json`. Native SGLang chat completed **8/8** requests per run, each with **1,130 input tokens**, **7,829 output tokens** and **zero cached prompt tokens**. No raw prompts or generated outputs are included here.

| Native chat run | Completed | Decode tok/s | Aggregate output tok/s | Mean TPOT ms | Wall seconds |
|---|---:|---:|---:|---:|---:|
| A | 8/8 | 137.086135 | 132.171700 | 7.294684 | 59.233557 |
| B | 8/8 | 137.047285 | 132.157401 | 7.296752 | 59.239967 |

**Decode** is reciprocal arithmetic mean request TPOT, `1000 / mean_tpot_ms`. **Aggregate** is output tokens divided by benchmark wall time. Mean TTFT was **163.932 / 165.053 ms**; mean request E2E **7.400735 / 7.401488 s**. Stream chunks can contain multiple tokens; arrival intervals are not individual token-ready timestamps. These two runs support approximately **137 single-request decode tok/s on this workload**, not a fixed-speed guarantee or broad quality/distribution parity. The summary does not provide text-identity evidence; run-order, thermal and limited-repeat caveats remain.

One post-flag prefix-cold synthetic natural-language request completed **24,000 inputs**, **128 outputs** and **zero cached tokens**. Client TTFT was **22.641913 s**, giving effective input-to-first-token rate **1059.981124 tokens/s**. This includes overhead and is **not pure GPU prefill throughput**. Full invocation duration was **23.161875 s**, with **1,036.185563 input tokens/s** under that separate denominator. One cold sample is not a tail-latency or arbitrary-input capacity result.

Post-flag chat B actual draw: **294 NVML samples**, every **200 ms**, selected at rolling GPU utilization **>=90%** within the invocation bracket. Mean draw was **278.769626 W**, range **204.51–280.71 W**, at a reported **280 W cap**; temperature **54–65°C**. These are selected invocation samples, **not phase-exact energy, whole-run mean draw or tokens/J**. No corresponding post-flag A power summary is claimed.

Idle observations used **100 samples per condition at 200 ms**, both **P8**: GPU mean **24.6198 W without sleep-on-idle / 25.2126 W with it**. Thermal states differed; **no GPU power saving was demonstrated**. Container CPU snapshots changed from **102.91% to 0.51%**; these are snapshots, not time-integrated CPU utilization or energy measurements. No idle-performance causality beyond this bounded observation is claimed.

## Quality and generated-checkpoint reuse

The current profile completed the existing 200-question numeric quality gate at **193/200 (96.5%)**, in **331.871401 seconds**, with mean **379.6 output tokens** and one worker. Seven items failed; four reached the 768-token cap. Conditions were temperature 0, thinking disabled and max 768 outputs. Fixture SHA256: `c33dcc6090f023fef25fe87711f6bd09d4de81658edb14468162cc9a9e5679fe`. Result: `/tmp/inference-final-qualification-o9vcvml2/final-quality.json`.

The corrected `extra_buffer` generated-checkpoint diagnostic passed its **predeclared 0.001 approximate-KL cutoff** on two frozen prompts: mean **0.000035783726386075915**; individual values **0.000007992375402146286** and **0.00006357507737000554**. Cached boundaries were **4,352 and 4,096 tokens**, both 256-aligned and extending into generated output. Each trajectory was compared with its own cold recomputation. Both completed diagnostics used input-logprob chunk 256 without an observed OOM. Evidence: `/tmp/inference-dflash-mamba-checkpoint-qualification.md` and `/tmp/inference-checkpoint-validation-vq8o7o22/fixed-chunk256.log` with its server log.

These are narrow numeric and checkpoint-reuse gates. They do not establish broad intelligence, sampling-distribution equivalence, `extra_buffer_lazy` correctness, arbitrary concurrency, cancellation/reclamation safety or every checkpoint boundary. The separate FlashInfer window issue remains outside this qualification.

## Memory, admission and queueing

- Two authenticated cold requests each completed **24,000 input tokens**, all **24,000 input-logprob rows** and **128 output tokens**, HTTP 200, with zero cached tokens. Evidence: `/tmp/inference-final-qualification-o9vcvml2/long-logprob-authenticated-response.json` and `long-logprob-warm-response.json`. Despite the second filename, its metadata records a cold request.
- A separate 24K request without input logprobs completed HTTP 200 with **20,480 cached tokens** and **128 outputs**: `long-cache-response.json` in the same directory.
- A **24,576-token input** was rejected with HTTP 400. A near-boundary **24,569-token input with six requested outputs** completed HTTP 200 with **five outputs**, finish reason length 5. Rejection and clamping are request-specific; not every over-budget request necessarily returns HTTP 400.


Response metadata was independently audited; HTTP statuses and the near-boundary/queue observations include execution-agent evidence. These completed probes support bounded memory and admission behavior, not universal no-OOM, unrelated long-request concurrency or all-input safety. Initial authentication failures were excluded. Runtime deployment remains pending; current draw and cold-input timing are recorded above.


## Client-concurrency scope: measured before sleep-on-idle

Evidence: `/tmp/inference-current-native-leyns4zq/current-concurrency.json`. **These client-C1/C2/C4 measurements predate `--sleep-on-idle`; they have not been rerun for the current flag setting.** The server limit in these measurements was **one running request**. Higher client concurrency queues work; **actual server batching is false**. Each run completed 8/8 with 1,130 input and 7,829 output tokens.

| Client concurrency | Decode tok/s | Aggregate output tok/s | Mean TTFT seconds |
|---|---:|---:|---:|
| 1 | 137.044857 | 132.134457 | 0.164485 |
| 2 | 137.205600 | 132.314392 | 6.288577 |
| 4 | 136.474464 | 131.605880 | 15.669979 |

Aggregate throughput is approximately unchanged while queueing increases TTFT. Server logs show one running request with queued requests, including queue depths two and three. Client concurrency is not simultaneous server decode concurrency; these results do not establish a batching gain or capacity for multiple active long sequences. Each concurrency setting has one measured run, not a repeated latency distribution. The separate true server-batch-two measurement below is completed; these queueing results must not be confused with it.


## Separate true batch-two measurement and Hermes blocker

Sanitized evidence: `/tmp/inference-current-batch2-cyoy588u/sanitized-results.json`. This is a **separate capacity configuration, not the production-default C1 profile**: context **8,192**, Mamba cache **K12**, token pool **18,000**, maximum running requests **two**, graph maximum batch size **two**, and sleep-on-idle enabled. Server evidence confirms **two requests actually running**.

The native short suite completed **8/8**, with **1,130 input tokens**, **7,827 output tokens**, zero reported cached prompt tokens and duration **39.174914 s**. Aggregate output throughput was **199.796229 tok/s**; reciprocal mean TPOT decode was **114.279933 tok/s**, mean TPOT **8.750443 ms**, mean TTFT **242.299227 ms**. This is one short-workload run with a smaller context/state allocation, not the default C1's performance or a long-request concurrency qualification. The default remains the separately measured sleep-on-idle C1 profile above.

**Hermes compatibility is blocked:** both empty-profile Hermes attempts were rejected by the client's minimum-context check **before generation**. Neither is a successful agent task or agent-performance benchmark. Synthetic API, numeric-quality and cache passes do not establish Hermes usability. The operator is restoring the default C1 candidate before commit, consumer repin and deployment; successful restoration, deployment and Hermes task completion are not yet established here. No further tuning is planned in this qualification closeout.
