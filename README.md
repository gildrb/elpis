# Local Qwen inference

Use the guarded Nix service to run Qwen3.8-27B on the RTX 3090. `gildrb/nix` consumes this repository's model preparation, native benchmark evidence and Nix module. The consumer owns drivers, power and fan policy, monitoring and deployment.

## Current 64K setup

The service selects one retained compact target, one quantized DFlash2 draft and three mandatory reviewed Python source replacements. There is no profile selector or source-guard opt-out.

| Item | Selected value |
|---|---|
| Hardware / power cap | ZOTAC RTX 3090 Trinity, 24 GB; 280 W policy owned by `gildrb/nix` |
| Runtime | `lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9` |
| Reviewed source | [`gildrb/sglang`](https://github.com/gildrb/sglang), revision `3958762c198b7e9e0167e6aedda1b8c3f9a8afb1`; compressed-head selection, quantized draft FC loading and Mamba checkpoint tracking; stock kernels |
| Target / draft | `compact-target-rholsc8k/artifact`, dense embeddings with preserved packed W4 head / `Qwen3.8-27B-DFlash2-W4A16` |
| Speculation / attention | DFlash2 block 8, draft window 2048; FlashInfer target and draft |
| Capacity | Context 65,536; token-pool cap 66,560; one running request (C1); static fraction 0.94; Mamba cache size 8 (K8) |
| Memory / chunking | `extra_buffer`, BF16 Mamba state, FP8 KV; prefill chunk 1024; input-logprob chunk 256; sleep-on-idle enabled; `NCCL_MAX_CTAS=1` |
| API | Authenticated OpenAI-compatible `http://127.0.0.1:18020/v1`; served model `qwen3.8-27b`; local endpoint `qwen-local` |

`--max-total-tokens 66560` is an upper bound on the token pool, not a minimum allocation or a larger request context. Record actual startup capacity separately. Native admission has a maximum input length of **65,530**; combined input/output accounting reserves two tokens. Output can be clamped at the boundary. Do not interpret the context value as permission to submit 65,536 input tokens, or assume every over-budget request is rejected.

The current profile uses **`NCCL_MAX_CTAS=1`**. Pinned source and model guards remain mandatory. The qualified entrypoint SHA256 is `c994f0a56914b8dddba2d347cbac5ee963af04a2d11818321979e4a622a108dd`; runtime reported context 65,536, actual pool 66,560, maximum input 65,530 and health HTTP 200.

NixOS activation has not been performed. Before activation, the consumer must pin and validate the exact inference and dotfiles revisions, then satisfy staging, backup and transaction gates. The sanctioned staged activation/reboot unit is allowed by passwordless sudo and reboots the host. Runtime health and benchmarks do not establish consumer closure validation or system activation.

## Measured performance and limits

Two native short suites passed **8/8 each**, with **1,130 input / 7,829 output tokens** and **zero cached prompt tokens** per run. Decode was **137.686002 / 135.900830 tok/s**; aggregate output was **132.778447 / 130.989520 tok/s**. Decode is reciprocal arithmetic mean request TPOT, not end-to-end throughput.

A cold **65,000-input / 128-output** request passed with zero cached tokens/retractions, **74.668278 s client TTFT** and **114.944470 client decode tok/s**. This full-context result is slower than the short-suite result. A separate cold full-input-logprob probe returned **65,000 rows and 128 outputs** with zero cached tokens/retractions in **77.594354 s**. These are bounded probes, not universal speed or no-OOM guarantees.

The current numeric gate passed **191/200 (95.5%)** in **334.177168 s**, with nine failures and mean **379.95 output tokens**. This is a capped numeric fixture, not broad quality or speculative/non-speculative equivalence.

A generated-checkpoint probe reused **65,024 cached tokens**, beyond the first 65,000-token prompt, and passed its predeclared emitted-token approximate-KL cutoff: **1.485160174869604e-05 < 0.001** over 128 aligned output IDs. This is not full-vocabulary KL or proof for every checkpoint boundary. A **65,000-input / 25-output** retrieval spot check returned both planted facts at offsets **6,503 / 32,525**, with zero cached tokens; it is not broad long-context comprehension.

Capacity probes passed **57,342 input + 8,192 output** and **65,406 input + 128 output**, both **65,534 combined tokens**, with zero cached tokens/retractions. Input 65,529 plus six requested outputs was clamped to five; input 65,536 returned HTTP 400. The 8,192-output probe is capacity-only evidence: cumulative SSE client parsing caused backlog, so it is not a comparable GPU decode measurement.

## Hermes compatibility

A fresh-home Hermes task passed after native discovery of context **65,536**, with **no context override**. It ran `cat /fixture/README.md`, returned the correct cited facts, and completed a final answer. Exact-session resume passed with the prior tool result in history and **zero new tool calls**. Native auxiliary title generation also passed. This is bounded agent compatibility, not a broad agent benchmark. Persisted `cache_read_tokens` was **0**: conversation-history reuse is proven, not a measured prefix-cache hit.

See [TRIALS.md](TRIALS.md) for exact metric definitions and evidence. The 280 W value is the power cap. Active draw, energy, idle savings, queue performance and batching are not qualified here; C1 remains selected.

## Reproduce the native benchmark

Run `python3 -m sglang.benchmark.serving` inside the pinned running SGLang container. Read the container identity from the generated deployment. Only run with approved exclusive access and cache flushing.

1. Stage the exact repository `benchmark-prompts.jsonl` bytes through container-exec stdin into a writable, mode-0700 `/tmp` directory. The inference root filesystem is read-only.
2. Set backend `sglang`, base URL `http://127.0.0.1:18020`, and model/tokenizer `/models/compact-target-rholsc8k/artifact`. Use `--ready-check-timeout-sec 0`, `docker exec -e OPENAI_API_KEY` with the key already in the caller environment, and `-e CUDA_VISIBLE_DEVICES=` for the client. Never put the literal key in a command.
3. Use `--dataset-name custom --dataset-path <container-fixture> --num-prompts 8 --apply-chat-template --sharegpt-output-len 1024 --disable-ignore-eos --max-concurrency 1 --request-rate inf --temperature 0 --seed 42 --warmup-requests 0 --flush-cache --cache-report --disable-tqdm`. Repeat twice. EOS may end output below the cap. Cache flushing does not unload weights or compiled graphs.
4. Write `--output-file <private-file>` in the private directory. Raw output includes `server_info`, which can contain secrets. Never print or commit it. Export only reviewed, explicitly allowlisted metrics to [benchmark-results.json](benchmark-results.json), not nested server configuration or generated text.
5. Report reciprocal mean TPOT separately from aggregate output tokens divided by wall time. Record actual input/output counts, failures and cache state. Sample power with timestamped invocation boundaries; utilization-filtered NVML data is not phase-exact energy.

## Operate and roll back

1. Preserve the retained target and draft. Both startup phases verify inventories and hashes; neither downloads, converts nor falls back. Use [prepare/REPRODUCE.md](prepare/REPRODUCE.md) for separate model reproduction.
2. Set `workstation.qwenInference.enable = true` in the consumer. Configure `stateRoot` and `requiredMountPoint`; port defaults to 18020 and the served model name is fixed. Pin and validate the exact final revision before separately approved activation.
3. Start through generated `qwen-inference.service`. Preparation verifies original pinned-image source without replacements, then models. Inference verifies read-only replacements and models. Direct `docker compose up inference` bypasses original-source verification; do not use it as the service startup path.
4. Retain an independently verified previous Nix generation, service configuration and required artifacts before activation. Restore that guarded generation if handover fails. Never bypass a failed guard or silently substitute a model.
5. Keep the 280 W power policy, boot/resume handling and monitoring in `gildrb/nix`. CPU closure validation is not live-service evidence.

## Repository and local state

- `nix/qwen-inference.nix` and `nix/sglang-entrypoint.sh`: guarded serving; `nix/sglang-compat/`: immutable source provenance, guards and [loader restrictions](nix/sglang-compat/NOTES.md).
- `prepare/`: conversion, numerical proof and artifact inventories. These model proofs are not current runtime quality benchmarks.
- `benchmark-prompts.jsonl`, `benchmark-results.json` and `TRIALS.md`: fixture, sanitized current measurements and qualification limits.

The workstation state root is `/mnt/ssd/storage/ai/qwen3.8-27b` (module default `/srv/ai/models/qwen3.8-27b`). It contains `api-key`, `cache/`, `models/compact-target-rholsc8k/artifact/` and `models/Qwen3.8-27B-DFlash2-W4A16/`. Do not commit weights, credentials, caches or private prompts/outputs.
