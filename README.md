# eta: Qwen3.8-27B on one RTX 3090 at 350 W, 262K context, lossless speculative decoding

**Qwen3.8-27B · EXL3 4.00 bpw · DFlash2 + 8-row token tree · 262,144 context · one RTX 3090 at 350 W, quiet fans · output = plain greedy · acceptance proved in Bend.**

> Numbers below: 250 W (protocol v4). Since 2026-09-28: 350 W + quiet fan curve; 350 W (v5) runs queued.

## How it compares with other RTX 3090 results for this model

Other projects' figures below are quoted from their repositories, not re-run here. No
other result shares eta's prompts, power cap and metric, so read this as what each
project reports, not as a ranking.

| One RTX 3090 | Weights | Speculation | Context / KV | Power | Reported tok/s |
|---|---|---|---|---|---|
| **eta, this repo** (measured) | 4.00 bpw | DFlash2 + 8-row token tree | 262,144 / 3-bit | 250 W cap; SM 0.96-1.19 GHz under load | **122.3** reasoning + code lane, **153.3** GSM8K (whole request, prefill included); 113.6 decode only at 1K context (*computed*) |
| [trellis-serve](https://github.com/0xSero/trellis-serve/tree/1ace59c4b43ca16a50fb6b7acf8b3fd7e2351f96) README headline, by 0xSero | 3.00 bpw | MTP, 3 steps / 4 tokens | 212,992 / fp8 | not published | 96.2 prose, 141.1 code (thinking off); 141.3 prose, 129.3 code (thinking on); decode only ([sweep](https://github.com/0xSero/local-ai-registry/blob/c6e6f4c796304229a3c11442af6f09673180d4f6/data/registry/speed-sweep/qwen38-27b-exl3-3bpw-mtp-vision-rtx3090-sglang-tp1-sweep.json)) |
| trellis-serve's fastest 3090 recipe ([DFlash2](https://github.com/0xSero/local-ai-registry/blob/c6e6f4c796304229a3c11442af6f09673180d4f6/data/registry/recipe/qwen38-27b-exl3-3bpw-dflash2-rtx3090-sglang-tp1.json), registry status "candidate") | 3.00 bpw | DFlash2, 5.0 bpw draft, block 8 | 131,072 / fp8 | not published; SM 1.74 GHz in its soak | 98.2 prose, 225.1 code (thinking off); 227.0 prose, 195.4 code (thinking on); decode only |
| [r0b0tlab](https://github.com/r0b0tlab/qwen38-exl3-dflash2) | 4.00 bpw | DFlash2 | 8,192 / FP16 in this run | 350 W cap | 162.9 GSM8K (in-process, per request) |

What differs:

- **Prompts.** Only GSM8K is shared: eta 153.3 at 250 W vs r0b0tlab 162.9 at 350 W on the
  same 40 questions ([details](#gsm8k-the-same-test-as-r0b0tlabs-published-number)).
  trellis-serve's prose and code panel prompts are not published.
- **Metric.** trellis-serve reports decode only: (completion tokens − 1) / (last − first
  streamed token). eta's lane and GSM8K rates divide by the whole request wall time; its
  decode-only figure is RoundBench's 3.89 tokens per 34.2 ms round.
- **Power.** eta is capped at 250 W. trellis-serve publishes no power limit; its DFlash2
  soak held the SMs at 1.74 GHz, against eta's 1.03 GHz median. On an older eta stack,
  350 W instead of 250 W gave +38.5 % tok/s on the same calls ([What 250 W costs](#what-250-w-costs)).
- **Bits.** 3.00 bpw reads 25 % fewer weight bits per token than 4.00 bpw (*computed*),
  at a larger quantization error; quality is not compared here.
- **Cost per verify step** (*computed*: reported tok/s ÷ reported accept length, assuming
  the accept length counts the bonus token): trellis-serve 23.4-24.9 ms at short context,
  eta 34.2 ms at 1K and 35.0 ms at 8K. Tokens per step at temperature 0: trellis-serve
  2.25-3.48 (MTP) and 2.45-5.65 (DFlash2) on its panel; eta 3.93 on the lane's C1 rows,
  5.70 on GSM8K.

Longest prompt shown working: eta 262,136 tokens (537 s prefill); r0b0tlab 262,080 (needle
test); trellis-serve 208,858 (MTP, 294 s to first token) and 126,782 (DFlash2, 187 s).
eta also reports energy, 0.495 tok/J on the lane and 0.616 on GSM8K; no other row
publishes tok/J.

In short: trellis-serve's DFlash2 recipe reports the fastest decode in this table, 225-227
tok/s on its code and thinking-on prose panels, with 3.00 bpw weights, a 131K window and SM
clocks 1.7× eta's median (*computed*); its README headline (MTP) reports 96-141 tok/s. eta
serves the full 262K window with 4.00 bpw weights under a 250 W cap. No row shares both
eta's prompts and its power; r0b0tlab's GSM8K shares the prompts only.

## Speed

**Target:** most tok/s at the native 262K context, one RTX 3090, 350 W. **Status** (live `tree3s`, 2026-09-28, measured at 250 W):

| Workload | tok/s | Tokens / round | tok/J |
|---|---|---|---|
| **Lane**: 20 calls, AIME 2025 · MMLU-Pro · I3 Logic · LiveCodeBench v6, thinking on, whole request (#67) | **122.33** | — | **0.495** |
| **GSM8K**: 40 questions, 512 tokens, median of 5 runs | **153.3** | 5.70 | **0.616** |
| C1 whole request, 1K / 8K / 32K-token prompt, 1,024 tokens out | 140.8 / 54.3 / 21.9 | 5.81 / 3.40 / 3.37 | 0.578 / 0.218 / 0.088 |
| Decode only, 1K / 8K context (RoundBench, *computed*) | 113.6 / 94.5 | 3.89 / 3.31 | 0.451 / 0.380 |

<details><summary>Lane per task (#67)</summary>

| Task set | Calls | Budget / call | Output tokens | Wall s | tok/s | Mean W | tok/J | Score | At budget |
|---|---|---|---|---|---|---|---|---|---|
| AIME 2025 | 3 | 32,768 | 36,985 | 279.4 | 132.36 | 247.6 | 0.534 | 3/3 | 0 |
| MMLU-Pro | 10 | 8,192 | 11,991 | 100.7 | 119.08 | 238.5 | 0.499 | 8/10 | 1 |
| I3 Logic | 4 | 16,384 | 39,876 | 294.3 | 135.49 | 247.9 | 0.546 | 2/4 | 1 |
| LiveCodeBench v6 | 3 | 16,384 | 36,018 | 346.3 | 104.00 | 248.4 | 0.419 | 1/3 | 2 |
| **All** | **20** | | **124,870** | **1,020.8** | **122.33** | **247.1** | **0.495** | | **4** |

- tok/s = completion tokens (reasoning included) / request wall time, prefill and HTTP included.
- Power: host `nvidia-smi` sampler, 250 ms, over each call.

</details>

<details><summary>Decode rounds (RoundBench: fresh process per repetition, 90 s heat-up, 4 repetitions)</summary>

| Depth | Mode | ms / round | Tokens / round | tok/s (*computed*) | J / round | tok/J |
|---|---|---|---|---|---|---|
| 1K | tree | 34.23 | 3.89 | 113.6 | 8.63 | 0.451 |
| 8K | tree | 35.01 | 3.31 | 94.5 | 8.71 | 0.380 |
| 1K | chain (`EXL3_TREE=0`) | 34.29 | 3.39 | 98.9 | 8.65 | 0.392 |
| 8K | chain (`EXL3_TREE=0`) | 35.03 | 2.90 | 82.8 | 8.78 | 0.330 |
| 1K | every draft token rejected (`cs12`) | 33.89 | 1.00 | 29.5 | 8.49 | 0.118 |
| 8K | every draft token rejected (`cs12`) | 34.71 | 1.00 | 28.8 | 8.65 | 0.116 |

</details>

## Lossless, with proof

| Claim | Proof | Result |
|---|---|---|
| The draft never changes the text | invariance gate (`cs10`): 15 prompts × normal / capped / all-rejected draft | 45/45 identical token ids |
| Speedups never change the text | lane 20 + C1 15 answers, `cs10` → `cs11` → `cs12` → `tree3s` | byte-identical |
| | GSM8K 40 answers × 16 runs, `cs12` + `tree3s` | byte-identical |
| Forced chain = old engine | `EXL3_TREE_FORCE_CHAIN=1` vs `cs12`, 17 prompts: ids, every round, drafted ids, usage | identical |
| Accept / commit logic | `bend PROOF.bend`: 41 modules, chain + tree acceptance, speculation invariance over trees | "All terms check." |
| Kernel changes | GDN state hashes, 1-8 steps (5108); 64 layers × rows 1-8 × 30 graph replays (2113); all 5,040 tree shapes vs the chain kernel (3012) | bit-exact |
| The tree costs no time | tree − chain, ms per round, 4 fresh processes | 1K: −0.06 (95 % CI −0.31..+0.19); 8K: −0.02 (−0.21..+0.18) |
| Scores | AIME 2025 3/3 · MMLU-Pro 8/10 · I3 Logic 2/4 · LiveCodeBench 1/3 | = `cs12` |

- [`LAWS.bend`](LAWS.bend) = contract; [`PROOF.bend`](PROOF.bend) = proofs. Order for every engine change: law → proof → measurement.
- Proofs cover the Bend models. CUDA / Python conformance = the bitwise differentials above (evidence, not proof).

## 262K context

| | |
|---|---|
| Context / cache | 262,144 / 270,336 tokens, 3-bit K and V |
| Longest prompt run | 262,136 tokens, prefill 537 s (`cs10`) |
| KV size | 12 KiB / token: only 16 of 64 layers keep KV; 3.1 GiB at 270,336 tokens (*computed*) |
| GPU memory, live | 21,888 / 24,576 MiB |

## GSM8K, the same test as r0b0tlab's published number

[`bench/gsm8k_compare.py`](bench/gsm8k_compare.py) = r0b0tlab's [`acceptance_check.py`](https://github.com/r0b0tlab/qwen38-exl3-dflash2/blob/main/scripts/acceptance_check.py) workload: first 40 GSM8K test questions (pinned), raw ChatML, greedy, 512 tokens, mean of per-request tok/s.

| | r0b0tlab (published) | eta `cs12` (11 runs) | eta `tree3s` (live, 5 runs) |
|---|---|---|---|
| Power | 350 W cap; 336 W mean (their telemetry, another run) | 250 W cap; 249.4 W median | 250 W cap; 249.4 W median |
| Engine | ExLlamaV3 `355c6ee`, unpatched | + 36 patches | + 41 patches |
| Context / KV | 8,192 / FP16 | 262,144 (cache 270,336) / 3-bit | same |
| Transport | in-process `generate()` | HTTP `/v1/completions` | same |
| tok/s | 162.9 | 148.8 median (147.9-154.3) | **153.3** median (151.9-159.7) |
| Tokens / round | 5.657 | 5.552 | 5.695 |
| Answers at the 512-token cap | 5/40 | 4/40 | 4/40 |
| tok/J | not published | 0.598 median (0.593-0.623) | **0.616** median (0.610-0.646) |

- Answers: byte-identical across all 16 eta runs.
- Tree gain: +3.0 % here vs +9.4 % on the lane; the chain already commits 5.55 of 8 tokens per round.
- Spread: fresh window, quiet host fastest (`cs12` 153.9-154.3, `tree3s` 159.7); warm card (67 °C) slower; host load ≈ 10: 148.8 (`cs12`); live endpoint, idle host: 161.9 (`cs12`, 34.0 ms/round).

## What 250 W costs

`cs5`, memory offset 0, 3 AIME 2025 calls, 35,081 tokens, token-identical:

| Power cap | tok/s | Mean W | tok/J | SM clock |
|---|---|---|---|---|
| 350 W (#56) | 158.90 | 322.8 | 0.492 | 1,455-1,479 MHz |
| 250 W (#57) | 114.69 | 247.9 | 0.463 | 892-1,042 MHz |

## How

| Lever | Measured |
|---|---|
| DFlash2 draft: one pass proposes 7 tokens from the target's hidden states | 1.00 → 3.39 tokens / round, 29.5 → 98.9 tok/s (1K, ~34 ms / round either way) |
| 8-row token tree: 7 nodes best-first; commit the longest matching root path + 1 | 3.39 → 3.89 tokens / round (1K); lane 111.85 → 122.33 tok/s; round time unchanged |
| 1-8 verify rows share one weight pass (16-row tensor-core tiles) | 16 rows: +21 % per verify forward |
| 4-bit EXL3 weights | 15.4 GiB target + 1.2 GiB draft |
| 41 engine patches, each bit-exact or numerics-gated | per area below |
| Memory clock −1500 MHz: watts go to the SMs under the 250 W cap | −1000 MHz: −0.77..−0.90 ms / round; −1500: −0.25..−0.46 more; −2000: none; core offsets: none (+225 MHz: Xid 109) |

<details><summary>41 engine patches</summary>

| Area | Patches | What | Measured when kept |
|---|---|---|---|
| Verify loop | exl3 0001-0003, 0005, 0006 | batched greedy verify via the Bend acceptor, host/GPU overlap, draft CUDA graph, DFlash2 block mask, tree verify via the proved tree acceptor | |
| Token tree | 9008, 3012, 5109, 3013 | GPU tree builder, ancestor-masked verify attention, GDN along each row's ancestors, commit of the accepted path's K/V | lane 111.85 → 122.33 tok/s |
| Layer tail + MLP | 2001, 7001, 8201, 8202, 8204, 8205b, 2106, 2107, 2113 | M ≤ 16 GEMMs, fused persistent MLP, one kernel per layer tail, weighted split-K, instruction diets, L2 discard of dead split-K partials | 2106/2107: −13.3 µs / layer; 2113: −0.40..−0.50 ms / round |
| Projections | 2102, 2105, 9003b | grouped m16 qkv(+z) GEMMs, target and draft | |
| Attention | 3001-3007, 3010 | exact dequant, GQA split, row-invariant strided verify attention, CUDA prefill attention | 3010: 262,136-token prefill 722 → 537 s |
| Gated DeltaNet | 0001-0004, 5001, 5101, 5106, 5108 | history-free verify, commit replay, fused conv/recurrence/norm, b/a K-split, replay gather | 5108: replay 620 → 402 µs (8 tokens) |
| Draft | 6001, 9002, 9005c | draft graph, int4 draft head, head pruned to 896 blocks | full head: −2.7 % tok/s (1K) |
| Prefill GEMM | 3011 | fp16-accumulate wide tiles | −21.6 % per 2,048-row chunk |

</details>

<details><summary>Where one verify round goes (CUPTI trace, <code>cs12</code>: 31.77 ms / round, 6.17 tokens / round)</summary>

| Phase | ms / round | % | Note |
|---|---|---|---|
| Layer tails: out projection + residual + norm + MLP | 17.10 | 53.8 | 64 fused persistent kernels (261.5 µs each) + pre-mixer norms |
| Gated DeltaNet input projections (qkv + z) | 4.15 | 13.0 | 48 grouped m16 GEMMs |
| Draft: forward, int4 head, walk, KV refresh | 3.02 | 9.5 | |
| Output head (248,320 × 5,120, 6 bpw) | 1.69 | 5.3 | |
| Gated DeltaNet conv + recurrence + norm | 1.54 | 4.8 | 48 fused kernels |
| Attention qkv projections | 1.23 | 3.9 | 16 grouped m16 GEMMs |
| Attention (split + combine + pre) | 0.52 | 1.6 | 1.50 ms at 8K context |
| GDN commit replay + conv rewind | 0.44 | 1.4 | |
| Sampler + copies | 0.05 | 0.2 | |
| GPU idle | 1.66 | 5.2 | lead, host-late gaps, gaps < 10 µs |

- ≈ 14 GB of quantized weights read per round (shape-derived).
- At 250 W, time per round tracks energy per round (8.5-8.7 J), not DRAM bandwidth.

</details>

## History

Kept lane runs. Compare within one protocol only.

| Run | Image | Protocol | Power | tok/s | tok/J |
|---|---|---|---|---|---|
| #53 | g7kafqt | v1: AIME 2025 ×3 + C1 (math only) | 350 W | 157.49 | 0.494 |
| #56 | cs5 | v2: AIME ×3, MMLU-Pro ×20, I3 Logic ×6, LiveCodeBench ×3 + C1 | 350 W | 144.13 | 0.444 |
| #57 | c0 (cs5 stack) | v3: v2 with MMLU-Pro ×10, I3 Logic ×4 | 250 W | 101.46 | 0.411 |
| #58 | cs10 | v3 | 250 W | 106.13 | 0.432 |
| #60 | cs10 | v4: v3 + declared memory offset −1500 MHz | 250 W | 107.03 | 0.433 |
| #61, #62 | cs11 | v4 | 250 W | 109.65, 109.81 | 0.444, 0.444 |
| #63 | cs12 | v4 | 250 W | 111.85 | 0.452 |
| **#67** | **tree3s (live)** | v4 | 250 W | **122.33** | **0.495** |

Every change and every dropped attempt: [docs/benchmarks.md](docs/benchmarks.md).

## Run it

1. Weights (pinned below) into a private `QWEN_STATE_ROOT`: `models/qwen38-27b-exl3/`, `models/dflash2-exl3/`, `cache/`, `api-key`, launch lock ([docs/docker.md](docs/docker.md)). Any byte mismatch: refuses to start.
2. Docker Compose + NVIDIA Container Toolkit (CDI `nvidia.com/gpu=0`); authenticated base image present locally.
3. Build and start:

```sh
bash docker/build-exl3.sh candidate-ext qwen-inference:exl3   # or: baseline, candidate
export QWEN_STATE_ROOT=/absolute/path/to/state QWEN_IMAGE=qwen-inference:exl3
export QWEN_ALLOW_UNQUALIFIED=1
docker compose --project-name qwen-inference up --no-build --pull never --detach --wait
```

- API: `http://127.0.0.1:18020/v1`, model `qwen3.8-27b`. Never beside another inference service.
- Docker owns runtime and restarts; Nix pins tools, the `.#bend` toolchain and a Compose adapter ([nix/STANDALONE.md](nix/STANDALONE.md)).

## Measure

```sh
bash autoresearch.sh   # the lane; protocol: docs/benchmarks.md; scoring: Prime Envs + Verifiers (eval/README.md)
curl -o gsm8k-test.jsonl https://raw.githubusercontent.com/openai/grade-school-math/3101c7d5072418e28b9008a6636bde82a006892c/grade_school_math/data/test.jsonl
python3 -m bench.gsm8k_compare --api-key-file /path/to/api-key --data gsm8k-test.jsonl --out gsm8k.json
```

## Setup

| | |
|---|---|
| GPU | RTX 3090 24 GiB (GA102, SM86), VBIOS 94.02.42.80.1F, PCIe 4.0 ×16, driver 595.71.05 |
| Power, clocks | **350 W** cap since 2026-09-28 (250 W before); core +0; **memory −1500 MHz**; NixOS `nvidia-quiet-power-limit.service`; the lane checks all three via NVML |
| Fans | CoolerControl: 70 % at 70 °C, 77 % at 80 °C, 80 % at 84 °C, 100 % at 90 °C; above 83 °C the card lowers its clocks |
| Under load, 350 W | 337 W mean; SM mean 1,533 MHz; 77-81 °C; fan 77-78 %; throttle: power cap only (3 min, fine-tune data job) |
| Under load, 250 W (#67) | 247.1 W mean; SM per-call mean 957-1,194 MHz (median 1,029); ≤ 68 °C |
| Host | Ryzen 7 5800X (8 cores / 16 threads), 125.7 GiB, NixOS 26.05, Linux 6.18.50 |
| Runtime | rootless Docker 29.7.2, CDI, read-only root; Ubuntu 24.04 CUDA base; Python 3.13.10, PyTorch 2.10.0+cu130, CUDA 13.0.96, cuBLAS 13.1.0.3, Triton 3.6.0 |
| Engine | ExLlamaV3 1.5.0 `355c6ee` (r0b0tlab `community`, native DFlash2) + 5 [`patches/exl3`](patches/exl3) + 36 [`patches/exl3-ext`](patches/exl3-ext), SHA256-pinned |
| Server | [`serve/exl3_server.py`](serve/exl3_server.py): authenticated OpenAI-compatible `/v1` chat/completions + tool calls, greedy, one sequence |
| Target | [`r0b0tlab/Qwen3.8-27B-EXL3-4.00bpw`](https://huggingface.co/r0b0tlab/Qwen3.8-27B-EXL3-4.00bpw) @ `3f1771b8` (`Qwen/Qwen3.8-27B`): 48 Gated DeltaNet + 16 full-attention layers, hidden 5,120, vocab 248,320; 4.00 bpw, 6 bpw head; 16.5 GB |
| Draft | [`r0b0tlab/Qwen3.8-27B-DFlash2-EXL3-4.00bpw`](https://huggingface.co/r0b0tlab/Qwen3.8-27B-DFlash2-EXL3-4.00bpw) @ `265b5240` (`incoai/Qwen3.8-27B-DFlash2`): 5 sliding-attention layers, block 8, reads target layers 5/19/33/47/61, top-16 selector; 1.25 GB |
| Recipe | [`serve/exl3-entrypoint.sh`](serve/exl3-entrypoint.sh): context 262,144, cache 270,336, 3-bit KV; 8 verify rows / round (anchor + 7 tree nodes); every file rehashed against [`prepare/exl3-manifest.json`](prepare/exl3-manifest.json) at start |

## Limitations

```
- Unqualified: one 262,136-token prompt ran; sustained 262K capacity, quality and speed are not qualified.
- Greedy only, one sequence at a time.
- Chat stream=true is buffered SSE: first event is not TTFT.
- Exact logit ties can depend on max_tokens (cs12: token 39457 at 8192 vs 54185 at 256,
  p = 0.28775 each; normal and all-rejected draft agree). Compare at equal request params.
- Speed varies with the text (3.37-6.69 tokens / round), host CPU load and card temperature.
- Quality: lane samples only. Full Prime Envs suite and 4-bit vs BF16 loss: not measured.
- In progress: DFlash2 fine-tune on the target's own outputs (prompts disjoint from all eval sets).
```

## References

- Protocol, every change, every dropped attempt: [docs/benchmarks.md](docs/benchmarks.md)
- Architecture and the Bend proof boundary: [docs/architecture.md](docs/architecture.md)
- Deployment: [docs/docker.md](docs/docker.md)
- Evaluator: [eval/README.md](eval/README.md)
- All docs: [docs/README.md](docs/README.md)
