# Mandatory reviewed runtime sources

Keep exact bytes and original license/source notices. Do not run a broad formatter over the retained reference modules.

`manifest.json` pins the stock SGLang image, immutable fork revision and NAR hash, plus original/replacement hashes for compressed-head selection, quant-aware draft FC loading and DFlash Mamba checkpoint tracking. Nix verifies the three stock-image source files in `base/`, verifies and applies the local patch diffs with zero fuzz, then verifies exact replacement hashes. It does not fetch a fork, build CUDA, or replace the runtime package. The source revision and NAR hash record historical provenance, not a build dependency.

Source is `gildrb/sglang` revision `3958762c198b7e9e0167e6aedda1b8c3f9a8afb1`, used with `lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9`. Source review does not establish runtime quality or activated deployment.

## Guard and loader requirements

The service runs `prepare` first in the exact pinned image without replacement mounts. It checks original source before model preparation. Inference mounts the three replacements read-only and verifies their hashes before launch. A replacement hides its original; replacement checks alone do not establish applicability. Preserve both phases. Direct `docker compose up inference` bypasses original-source verification.

The head and FC replacements support one full initial `DefaultModelLoader` load only. Do not use hot reload or partial weight loading. The head helper assumes successful Marlin processing; metadata alone does not prove numerical layout. The FC check requires checkpoint parameters before derived Marlin buffers exist. The Mamba correction tracks committed post-verify sequence lengths.

Do not relax hashes, apply fuzz, alias packed weights to dense `.weight`, or accept arbitrary quantization methods. Image/source changes require a reviewed rebase. Preserve the three patch diffs and manifest.

## Current 64K service

`workstation.qwenInference.enable = true` selects the retained compact target, original W4 draft and all three replacements. There is no profile selector or guard opt-out. Configure `stateRoot` and `requiredMountPoint`; port defaults to 18020 and the served model is fixed. Both phases verify complete model inventories and hashes. Missing or mismatched artifacts fail closed. Startup does not download, convert or silently fall back. See [../prepare/REPRODUCE.md](../prepare/REPRODUCE.md) for separate reproduction without overwriting originals.

The entrypoint selects context **65,536**, `--max-total-tokens 66560`, C1, static fraction **0.94**, Mamba cache **K8**, `extra_buffer`, BF16 Mamba state, FP8 KV, prefill chunk **1024**, DFlash block **8**, draft window **2048** and FlashInfer target/draft attention. Native input-logprob chunking is enabled at **256**. Prefill CUDA graphs are disabled; decode graph maximum batch size is 8, which does not change the C1 running-request limit. `NCCL_MAX_CTAS=1` bounds NCCL CTAs; no NCCL minimum-channel setting is selected. Native `--sleep-on-idle` is enabled; its polling timeout is not a fixed one-second request delay or evidence of GPU power saving.

The token-pool setting is an upper bound, not a minimum allocation or per-request context. Native actual maximum input length is **65,530**. Combined input/output accounting reserves two tokens, and near-boundary output may be clamped. These limits do not guarantee all requests are OOM-free.

## Qualification and deployment boundary

Current entrypoint SHA256: `c994f0a56914b8dddba2d347cbac5ee963af04a2d11818321979e4a622a108dd`. Runtime metadata reported context 65,536, actual token pool 66,560 and maximum input 65,530; health returned HTTP 200. Current measurements are bound to `NCCL_MAX_CTAS=1`.

Two native short suites passed **8/8 each**, with **1,130 input / 7,829 output tokens** and **zero cached prompt tokens** per run. Decode was **137.686002 / 135.900830 tok/s**; aggregate output was **132.778447 / 130.989520 tok/s**. Decode is reciprocal arithmetic mean request TPOT, not end-to-end throughput.

A cold **65,000-input / 128-output** request passed with zero cached tokens/retractions, **74.668278 s client TTFT** and **114.944470 client decode tok/s**. This full-context result is slower than the short-suite result. A separate cold full-input-logprob probe returned **65,000 rows and 128 outputs** with zero cached tokens/retractions in **77.594354 s**. These are bounded probes, not universal speed or no-OOM guarantees.

The current numeric gate passed **191/200 (95.5%)** in **334.177168 s**, with nine failures and mean **379.95 output tokens**. This is a capped numeric fixture, not broad quality or speculative/non-speculative equivalence.

A generated-checkpoint probe reused **65,024 cached tokens**, beyond the first 65,000-token prompt, and passed its predeclared emitted-token approximate-KL cutoff: **1.485160174869604e-05 < 0.001** over 128 aligned output IDs. This is not full-vocabulary KL or proof for every checkpoint boundary. A **65,000-input / 25-output** retrieval spot check returned both planted facts at offsets **6,503 / 32,525**, with zero cached tokens; it is not broad long-context comprehension.

Capacity probes passed **57,342 input + 8,192 output** and **65,406 input + 128 output**, both **65,534 combined tokens**, with zero cached tokens/retractions. Input 65,529 plus six requested outputs was clamped to five; input 65,536 returned HTTP 400. The 8,192-output probe is capacity-only evidence: cumulative SSE client parsing caused backlog, so it is not a comparable GPU decode measurement.

The separate FlashInfer window finding remains draft-only; no target-greedy accepted-output divergence is established here. The checkpoint diagnostic does not qualify `extra_buffer_lazy`, cancellation/reclamation or arbitrary concurrency.

See [../docs/qualification.md](../docs/qualification.md) for reproduction and evidence. The 280 W cap is consumer-owned policy, not measured draw or energy. Idle and queue performance were not measured here; no batching is qualified.

NixOS activation has not been performed. Before activation, the consumer must pin and validate the exact inference and host configuration revisions, then satisfy its staging, backup and transaction gates. Runtime health and benchmarks do not establish consumer closure validation or system activation.

Before activation, retain an independently verified previous Nix generation, service configuration and required artifacts. Restore the guarded generation if handover fails; never bypass failed compact verification.

## Vendored base provenance

`base/` contains only the three original Python files extracted from the exact
manifest-pinned stock SGLang image in a CPU-only, network-disabled, read-only
container. Every file matches its `original_sha256`. Original source/license
notices remain intact. The local `.patch` files are authenticated separately;
Nix verifies their output against every `replacement_sha256`. Runtime prepare
still verifies the actual image originals independently before replacement
mounts hide them. No fork download or full runtime source copy is required.
