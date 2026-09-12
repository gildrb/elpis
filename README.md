# Local Qwen inference

Use the guarded Nix service to run Qwen3.8-27B on the RTX 3090. `gildrb/nix` imports these modules. This repository owns reproducible model/source preparation, native benchmark evidence and the consumable Nix serving module. The consumer owns GPU drivers, power and fan policy, monitoring and deployment.

## Current setup and deployment state

Enabling this service always selects the retained compact target and quantized DFlash2 draft, with stock kernels and three mandatory reviewed Python source fixes. There is no profile selector or source-guard opt-out. Locked Linux validation (`--host computer --without-vm`) has passed all 27 flake checks/contracts and exact-closure validation. The final consumer revision pin and validation must match this current-only interface before activation. **Activation and restart handover are still pending; no reboot has occurred.** CPU deployment checks are not live-service evidence.

| Item | Selected value |
|---|---|
| GPU / power policy | ZOTAC RTX 3090 Trinity, 24 GB; 280 W owned by `gildrb/nix` |
| Runtime | `lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9` |
| Reviewed source | [`gildrb/sglang`](https://github.com/gildrb/sglang) at `3958762c198b7e9e0167e6aedda1b8c3f9a8afb1`; compressed-head selection, quantized draft FC loading, Mamba checkpoint tracking |
| Target / draft | Retained `compact-target-rholsc8k/artifact` with dense embeddings / original quantized W4 `Qwen3.8-27B-DFlash2-W4A16` |
| Speculation / attention | DFlash2 block 8, draft window 2048; FlashInfer target and draft |
| Capacity / memory | One running request (C1), static fraction 0.89, Mamba cache size 8 (K8), `extra_buffer`, BF16 Mamba state, FP8 KV |
| Context / chunking | Context 24,576; prefill chunk 4096; native input-logprob chunk 256 enabled |
| Client API | Authenticated OpenAI-compatible `http://127.0.0.1:18020/v1`, served model `qwen3.8-27b` |

Local clients use the `qwen-local` endpoint.

## Idle behavior

The entrypoint enables native `--sleep-on-idle`. In local idle checks, Docker CPU snapshots fell from 102.91% to 0.51%. Each GPU check collected 100 NVML samples at 200 ms: mean idle draw was 24.6198 W before and 25.2126 W with the flag, both in P8. The thermal states differed; these measurements establish **no GPU power saving**. Idle CPU behavior is separate from the 280 W cap and active-run power draw.

The scheduler polls for at most 1000 ms while idle and wakes on a request; this is not a fixed one-second request delay. Two native chat runs and a cold 24K request completed with the flag enabled. Current decode, cold-input and active-power figures below use this enabled configuration. The separately labeled queue table has not yet been rerun with the flag.

## Qualification, not guarantees

The native SGLang chat-template benchmark at a 280 W cap completed two cold-cache C1 suites, **8/8 each**, at **137.08613 / 137.04729 decode tok/s** (reciprocal mean TPOT). Aggregate output throughput was **132.17170 / 132.15740 tok/s**. Both runs used 1,130 input and 7,829 output tokens with zero cached prompt tokens. These short-suite measurements are not a universal throughput promise. The final capped GSM8K gate scored **193/200 (96.5%)**; this does not prove broad quality or spec/no-spec distribution parity.

Two cold 24,000-input full-logprob requests passed with 24,000 logprob rows and 128 outputs each. A separate no-input-logprob request reused 20,480 cached tokens. A 24,576-token input returned HTTP 400; 24,569 input tokens plus six requested outputs returned five outputs. Do not assume every over-budget request is rejected instead of clipped, or that all possible requests are OOM-free.

The corrected generated-prefix diagnostic's mean approximate KL was **0.0000357837**. This qualifies the narrow `extra_buffer` repair, not `extra_buffer_lazy` or all cache/concurrency cases. The separate FlashInfer window finding remains draft-only and unchanged; no target-greedy accepted-output divergence is proven. See [TRIALS.md](TRIALS.md) for current qualification evidence and limits. A native cold 24,000-input-token request passed with zero cached tokens and TTFT 22.641913 s: effective input-to-first-token throughput was 1059.981124 tok/s, including overhead. This is not pure GPU prefill throughput. The 280 W value is the cap. Mean high-utilization NVML power draw for chat repeat B was **278.769626 W**, from 294 samples at 200 ms, selected at GPU utilization at least 90% within that invocation. These rolling-utilization samples are not phase-exact energy measurements.

### Queue qualification scope: measured before sleep-on-idle

These queue runs have not been repeated with `--sleep-on-idle`; they are not post-flag performance evidence. All runs completed 8/8 with 1,130 input and 7,829 output tokens. The server permits one active request; additional clients were observed queued. These are queue-handling measurements, **not actual batching or a batching gain**.

| Client concurrency | Aggregate output tok/s | Decode tok/s (`1000 / mean TPOT ms`) | Mean TTFT s |
|---|---:|---:|---:|
| 1 | 132.13 | 137.04 | 0.164 |
| 2 | 132.31 | 137.21 | 6.289 |
| 4 | 131.61 | 136.47 | 15.670 |

The current server setting remains C1. A separate capacity measurement used context 8192, two running requests, Mamba cache size 12, an 18,000-token pool and CUDA graph maximum batch size 2, with sleep-on-idle enabled. It completed 8/8 with 1,130 input and 7,827 output tokens, zero cached prompt tokens, **199.796229 aggregate output tok/s** and **114.279933 decode tok/s**. Two simultaneous running requests were observed. This is not the production C1 configuration or a qualification of two independent 24K requests.

**Client compatibility blocker:** both empty-profile Hermes attempts were rejected by the client's minimum-context check before generation. They are not successful agent tasks or agent benchmarks. Native serving results do not resolve this client admission blocker.

## Reproduce the native benchmark

Use `python3 -m sglang.benchmark.serving` in the running pinned SGLang container. Read its actual container identity from the generated service/Compose deployment; do not assume a container name. Run only when exclusive benchmark access and cache flushing are approved.

1. Use the repository's `benchmark-prompts.jsonl` as the eight-prompt custom fixture. Stage it through container-exec stdin into writable `/tmp`; the inference root filesystem is read-only. This staging method was verified with the exact repository fixture bytes in a newly created mode-0700 `/tmp` directory on the read-only-root server. Both post-flag native runs passed with 1,130 input tokens.
2. Set backend `sglang`, base URL `http://127.0.0.1:18020`, and both model and tokenizer to `/models/compact-target-rholsc8k/artifact`. Use `--ready-check-timeout-sec 0` and pass authentication as `docker exec -e OPENAI_API_KEY` with the key already in the caller's environment, never a literal command-line value. Use `-e CUDA_VISIBLE_DEVICES=` for this client process.
3. Use `--dataset-name custom --dataset-path <container-fixture> --num-prompts 8 --apply-chat-template --sharegpt-output-len 1024 --disable-ignore-eos --max-concurrency 1 --request-rate inf --temperature 0 --seed 42 --warmup-requests 0 --flush-cache --cache-report --disable-tqdm`. EOS can end a response before the 1024-token cap. Repeat the same cold-cache protocol twice.
4. Set `--output-file <private-file>` inside a private directory with mode `0700`. Native output includes `server_info`, which can contain secrets. Never print or commit the raw output. Export only reviewed, explicitly allowlisted metrics into [benchmark-results.json](benchmark-results.json); do not copy nested server configuration.
5. Calculate decode tok/s as `1000 / mean_tpot_ms`, not aggregate output throughput. Record input/output counts, failures and cache state. Sample power separately with timestamped invocation boundaries; a 280 W cap is not measured draw, and utilization-filtered NVML samples are not phase-exact energy.

## Operate and roll back

1. Preserve the retained target and draft. Compact startup verifies their exact inventories and hashes in both phases. It never downloads, converts or silently falls back. For a new artifact, follow [prepare/REPRODUCE.md](prepare/REPRODUCE.md) separately before serving.
2. Set `workstation.qwenInference.enable = true` in the consumer. Set `stateRoot` and `requiredMountPoint` for its storage layout; `port` defaults to 18020 and `model` is the fixed served name. Pin the current revision and complete locked validation before a separately approved activation.
3. Start through the generated `qwen-inference.service`. Its `prepare` phase checks the original pinned-image source without overlays, then checks models. Inference checks the three read-only replacements and models before launch. Direct `docker compose up inference` bypasses original-source verification; do not use it as the service startup path.
4. Before activation, retain an independently verified previous Nix generation, service configuration and its required artifacts for rollback. Restore that guarded generation if handover fails. Do not bypass a failed compact guard or silently substitute a model.
5. Keep power policy in `gildrb/nix`: selected source/live cap is 280 W, with boot/resume handling and no five-minute power-reset timer. This does not assert activation of the new consumer generation.

## Repository and local state

- `nix/qwen-inference.nix` and `nix/sglang-entrypoint.sh`: guarded preparation and current compact serving.
- `nix/sglang-compat/`: immutable source provenance, guards and [loader restrictions](nix/sglang-compat/NOTES.md).
- `prepare/`: retained conversion, numerical proof and model inventories; no automatic conversion on startup.
- `benchmark-prompts.jsonl` and `benchmark-results.json`: native benchmark fixture and sanitized current results. Host health probes, recovery and dashboards belong to `gildrb/nix`.

The workstation uses `/mnt/ssd/storage/ai/qwen3.8-27b` as its state root (module default: `/srv/ai/models/qwen3.8-27b`):

```text
/mnt/ssd/storage/ai/qwen3.8-27b/
├── api-key
├── cache/
└── models/
    ├── compact-target-rholsc8k/artifact/
    └── Qwen3.8-27B-DFlash2-W4A16/
```

Model weights, API keys, caches and generated corpora are not committed. Never include credentials or private prompt/output artifacts in published evidence.
