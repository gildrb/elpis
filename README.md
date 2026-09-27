# eta: Qwen3.8-27B on one RTX 3090 at 250 W, 262K context, lossless speculative decoding

The live endpoint serves Qwen3.8-27B (EXL3 4.00 bpw) with native DFlash2
speculative decoding at its full 262,144-token context on a single 24 GiB RTX 3090
capped at 250 W. Bend states and proves the decision logic the serving path must
get right; every speedup below left the model's greedy output unchanged.
Optimize C1 agent latency and useful code/reasoning output at native context.

## Current numbers

Live image `tree3s` (`sha256:ec9751b0…`, the patch series of commit `c10606d`: `cs12` plus
8-row token-tree verification), measured 2026-09-26/28. Every figure is a measurement unless
marked *computed*; details and definitions follow in [Results](#results). Rows marked `cs12`
were measured on the previous image and not repeated.

| What | Result | Workload |
|---|---|---|
| **Output speed, reasoning + code lane** | **122.33 tok/s** | 20 calls (AIME 2025, MMLU-Pro, I3 Logic, LiveCodeBench v6), thinking on, greedy; 124,870 output tokens in 1,020.8 s of request wall, prefill included (run #67) |
| **Energy** | **0.495 tok/J** at 247.1 W mean board power | the same 20 calls, board power sampled every 250 ms |
| Output speed, GSM8K (the test behind r0b0tlab's 162.9 tok/s) | **153.3 tok/s** median, 0.616 tok/J | first 40 GSM8K test questions, 512 new tokens, 5 isolated runs |
| Tokens committed per verify round | 3.93 (lane C1 rows) · 5.70 (GSM8K) | 8 rows verified per round |
| Decode only, 1K-token context | 113.6 tok/s (3.89 tokens per 34.2 ms round, *computed*), 0.45 tok/J | RoundBench, 4 fresh processes |
| Same rounds with every draft token rejected | 29.5 tok/s, 0.12 tok/J (`cs12`) | RoundBench `wrong0` arm |
| Output vs plain greedy decoding | identical | invariance gate 45/45 (`cs10`); `cs10` → `cs11` → `cs12` → `tree3s`: 20/20 lane and 15/15 C1 answers byte-identical |
| Context | 262,144 tokens (cache 270,336, 3-bit KV) | a 262,136-token prompt prefills in 537 s (measured on `cs10`) |
| GPU memory | 21,888 MiB of 24,576 MiB in use | live server, model + draft + cache loaded |

## Hardware and software

| Component | Value |
|---|---|
| GPU | NVIDIA GeForce RTX 3090 (GA102, Ampere, SM86), 24,576 MiB GDDR6X, VBIOS 94.02.42.80.1F, PCIe 4.0 ×16 |
| Driver | 595.71.05 (CUDA 13.2 driver API), persistence mode on |
| Power limit | **250 W** (card default and maximum 350 W) |
| Clock offsets | core 0 MHz; **memory −1500 MHz** (8,751 MHz reported under load, 9,001 MHz max) |
| Observed under load | 247-250 W; SM clock 955 MHz mean over the lane's calls (samples 210-1,815 MHz); 64-67 °C; fan 67 % (driver auto); throttle reason: software power cap only |
| Observed at idle | 38.6 W, 51 °C (one sample, model loaded, no request) |
| How it is set | NixOS `nvidia-quiet-power-limit.service` applies the limit and offsets at boot and resume; the lane reads all three through NVML and refuses to measure otherwise |
| Host | AMD Ryzen 7 5800X (8 cores / 16 threads), 125.7 GiB RAM, NixOS 26.05, Linux 6.18.50 |
| Containers | rootless Docker 29.7.2, GPU through CDI `nvidia.com/gpu=0`, read-only root filesystem |
| Image | Ubuntu 24.04 NVIDIA CUDA base; Python 3.13.10, PyTorch 2.10.0+cu130, CUDA runtime 13.0.96, cuBLAS 13.1.0.3, Triton 3.6.0 |
| Engine | ExLlamaV3 1.5.0 at `355c6ee` (r0b0tlab `community` branch, native DFlash2) + 4 engine patches ([`patches/exl3`](patches/exl3)) + 32 CUDA/extension patches ([`patches/exl3-ext`](patches/exl3-ext)), every file SHA256-pinned |
| Acceptance | Bend 2.0.29 artifact (`bend/exl3_accept*.bend`): the greedy accept/commit decision of every round runs the proved Bend leaf |
| Server | [`serve/exl3_server.py`](serve/exl3_server.py): authenticated OpenAI-compatible `/v1` chat/completions and tool calls on `127.0.0.1:18020`, model `qwen3.8-27b`, greedy only, one sequence |

| Model | Identity | Architecture |
|---|---|---|
| Target | `Qwen/Qwen3.8-27B` quantized as [`r0b0tlab/Qwen3.8-27B-EXL3-4.00bpw`](https://huggingface.co/r0b0tlab/Qwen3.8-27B-EXL3-4.00bpw) at `3f1771b8c21f83cbb8e82169559ced9f38ca04e5` | 64 layers: 48 Gated DeltaNet (linear attention, 16 key / 48 value heads × 128) + 16 full attention (24 query / 4 KV heads × 256); hidden 5,120, MLP 17,408, vocabulary 248,320, native context 262,144. EXL3 1.5.0: 4.00 bpw weights, 6 bpw output head, `mul1` codebook; 16,509,561,298 bytes |
| Draft | `incoai/Qwen3.8-27B-DFlash2` quantized as [`r0b0tlab/Qwen3.8-27B-DFlash2-EXL3-4.00bpw`](https://huggingface.co/r0b0tlab/Qwen3.8-27B-DFlash2-EXL3-4.00bpw) at `265b5240592907d2d55ff0dc4d5f66569692604d` | DFlash2 block-diffusion draft: 5 sliding-attention layers (hidden 5,120, 32 / 8 heads × 128), block of 8 (anchor + 7 masked positions), reads the target's hidden states at layers 5/19/33/47/61, top-16 candidate selector (rank 256); int4 output head pruned to 896 of 1,940 blocks; 1,254,647,206 bytes |
| Serving recipe | [`serve/exl3-entrypoint.sh`](serve/exl3-entrypoint.sh) | context 262,144, cache 270,336 tokens, 3-bit K and V (CQ3); 7 draft tokens + 1 anchor verified per round; every model file rehashed against [`prepare/exl3-manifest.json`](prepare/exl3-manifest.json) at start |

## Results

### Benchmark lane, run #67 (`bash autoresearch.sh`, protocol v4)

Prime Envs + Verifiers tasks with their native scorers, one greedy call per task,
thinking on. tok/s = completion tokens (reasoning included) / request wall time,
send to complete response, prefill and HTTP included. Power from the host's 250 ms
`nvidia-smi` sampler over each call.

| Task set | Calls | Output budget / call | Input tokens | Output tokens | Wall s | tok/s | Mean W | tok/J | Score | Stopped at budget |
|---|---|---|---|---|---|---|---|---|---|---|
| AIME 2025 | 3 | 32,768 | 762 | 36,985 | 279.4 | 132.36 | 247.6 | 0.534 | 3/3 | 0 |
| MMLU-Pro | 10 | 8,192 | 2,681 | 11,991 | 100.7 | 119.08 | 238.5 | 0.499 | 8/10 | 1 |
| I3 Logic | 4 | 16,384 | 3,825 | 39,876 | 294.3 | 135.49 | 247.9 | 0.546 | 2/4 | 1 |
| LiveCodeBench v6 | 3 | 16,384 | 1,991 | 36,018 | 346.3 | 104.00 | 248.4 | 0.419 | 1/3 | 2 |
| **All (primary)** | **20** | | **9,259** | **124,870** | **1,020.8** | **122.33** | **247.1** | **0.495** | | **4** |

Scores, budget stops and every completion text are byte-identical to `cs12`'s run #63
(111.85 tok/s, 0.452 tok/J); the tree changes only how many tokens each round commits.
The previous stack ran this lane twice, 109.65 and 109.81 tok/s.

### Long prompts: C1 whole-request matrix (same run)

Five requests per depth from the frozen corpus [`bench/throughput-prompts.jsonl`](bench/throughput-prompts.jsonl),
1,024 output tokens each, whole-request rate including prefill (TTFT is not exposed
by the non-streaming transport).

| Prompt | Prompt tokens | Wall s (5 requests) | tok/s | Tokens / round | Mean W | tok/J |
|---|---|---|---|---|---|---|
| 1K | 1,076 | 36.37 | 140.77 | 5.81 (request 1: 4.00; requests 2-5: 6.40-6.69, their reasoning copies ~80 % of its text verbatim from the prompt) | 243.5 | 0.578 |
| 8K | 8,244 | 94.29 | 54.30 | 3.40 | 249.2 | 0.218 |
| 32K | 32,821 | 233.78 | 21.90 | 3.37 | 248.2 | 0.088 |

### Decode rounds only (RoundBench)

A fresh server process per repetition, 90 s heat-up, 4 repetitions, C1 prompts at
two depths, 250 W. `off` is `tree3s` with `EXL3_TREE=0` (the `cs12` chain); `wrong0`
(measured on `cs12`) forces every draft token to be rejected, so each round commits
exactly one token with the same kernels. tok/s and tok/J are *computed* from the
measured ms, tokens and joules per round.

| Depth | Mode | ms / round | Tokens / round | tok/s | J / round | tok/J |
|---|---|---|---|---|---|---|
| 1K | tree | 34.23 | 3.89 | 113.6 | 8.63 | 0.451 |
| 8K | tree | 35.01 | 3.31 | 94.5 | 8.71 | 0.380 |
| 1K | off (chain) | 34.29 | 3.39 | 98.9 | 8.65 | 0.392 |
| 8K | off (chain) | 35.03 | 2.90 | 82.8 | 8.78 | 0.330 |
| 1K | `wrong0` (`cs12`) | 33.89 | 1.00 | 29.5 | 8.49 | 0.118 |
| 8K | `wrong0` (`cs12`) | 34.71 | 1.00 | 28.8 | 8.65 | 0.116 |

The tree costs no measurable round time: tree − off = −0.06 ms at 1K (95 % CI
−0.31 to +0.19) and −0.02 ms at 8K (−0.21 to +0.18). Base arms of screens on
2026-09-27/28 span 33.79-34.29 ms (1K) and 34.87-37.04 ms (8K).

### GSM8K, the same test as r0b0tlab's published number

[`bench/gsm8k_compare.py`](bench/gsm8k_compare.py) replays r0b0tlab's
[`acceptance_check.py`](https://github.com/r0b0tlab/qwen38-exl3-dflash2/blob/main/scripts/acceptance_check.py)
workload: the first 40 GSM8K test questions (pinned file), raw ChatML prompt,
greedy, 512 new tokens, mean of per-request tok/s. Isolated GPU windows: eleven
runs of `cs12` on 2026-09-27, five of `tree3s` in one window on 2026-09-28.

| | r0b0tlab (published) | eta `cs12` | eta `tree3s` (live) |
|---|---|---|---|
| Power | 350 W cap; their telemetry of another run: 336 W mean under load | 250 W cap; 249.4 W median | 250 W cap; 249.4 W median |
| Engine | same ExLlamaV3 `355c6ee`, unpatched | + 36 patches | + 41 patches |
| Context / KV cache | 8,192 / FP16 | 262,144 (cache 270,336) / 3-bit | same |
| Transport | in-process `generate()` | HTTP `/v1/completions` | same |
| tok/s | 162.9 | 148.8 median (147.9-154.3) | **153.3** median (151.9-159.7) |
| Tokens / round | 5.657 | 5.552 | 5.695 |
| Answers at the 512-token cap | 5/40 | 4/40 | 4/40 |
| tok/J | not published | 0.598 median (0.593-0.623) | **0.616** median (0.610-0.646) |

All 16 runs of both images return the same 40 answers, byte for byte. GSM8K gains
less from the tree (+3.0 % tok/s) than the lane (+9.4 %): its answers are short
and formulaic, so the chain already commits 5.55 of 8 possible tokens per round.
Speed moves with conditions, output does not: the first run in a fresh window on a
quiet host is the fastest (`cs12` 153.9 and 154.3, `tree3s` 159.7), later runs settle
as the card warms from 42-45 to 67 °C, and a `cs12` first run while other jobs
kept the host's load average near 10 measured 148.8. One earlier `cs12` run against
the long-running live endpoint on an idle host measured 161.9 tok/s (34.0 ms per round).

### What 250 W costs

Same kernel stack (`cs5`), memory offset 0, identical output (the three AIME 2025
calls, 35,081 tokens, match token for token):

| Power cap | tok/s | Mean W | tok/J | SM clock |
|---|---|---|---|---|
| 350 W (#56) | 158.90 | 322.8 | 0.492 | 1,455-1,479 MHz |
| 250 W (#57) | 114.69 | 247.9 | 0.463 | 892-1,042 MHz |

The protocol-v4 lane (same tasks as #57, memory offset −1500 MHz, later kernels)
measures 122.33 tok/s and 0.495 tok/J at 250 W (#67; see [history](#result-history)).

### Where one verify round goes

CUPTI kernel trace of `cs12` (kernel-trace-12; the tree adds no measurable round time), a short-context reasoning prompt:
31.77 ms per round (unprofiled median), 6.17 tokens per round on this prompt.

| Phase | ms / round | % | Note |
|---|---|---|---|
| Layer tails: output projection + residual + norm + MLP | 17.10 | 53.8 | 64 fused persistent kernels (261.5 µs each) + pre-mixer norms |
| Gated DeltaNet input projections (qkv + z) | 4.15 | 13.0 | 48 grouped m16 GEMMs |
| Draft: forward, int4 head, walk, KV refresh | 3.02 | 9.5 | |
| Output head (248,320 × 5,120, 6 bpw) | 1.69 | 5.3 | |
| Gated DeltaNet conv + recurrence + norm | 1.54 | 4.8 | 48 fused kernels |
| Attention qkv projections | 1.23 | 3.9 | 16 grouped m16 GEMMs |
| Attention (split + combine + pre) | 0.52 | 1.6 | 1.50 ms at 8K context |
| GDN commit replay + conv rewind | 0.44 | 1.4 | |
| Sampler + copies | 0.05 | 0.2 | |
| GPU idle (lead, host-late gaps, gaps < 10 µs) | 1.66 | 5.2 | |

About 14 GB of quantized weights are read per round (shape-derived). At the 250 W
cap the weight-streaming kernels are limited by instruction issue and power, not by
DRAM bandwidth: time per round follows energy per round (8.5-8.7 J measured above).

## Why it is fast

1. **Speculative decoding with DFlash2 and a token tree.** One draft pass proposes a
   block of tokens at once (block diffusion over masked positions, conditioned on the
   target's own hidden states). Instead of a 7-token chain, the 8 verify rows carry a
   token tree: 7 nodes picked best-first by the draft's calibrated cumulative
   probability. One target pass checks every row, and the round keeps the longest
   matching root path plus one token of the target's own. 3.37-5.81 tokens per round
   across the lane's C1 depths instead of 1 (29.5 → 113.6 tok/s at the same round cost, above).
2. **Verifying 8 positions costs about the same as 1.** The weight-streaming kernels
   work in 16-row tensor-core tiles, so 1-8 rows share one pass over the weights
   (16 rows measured +21 % per verify forward).
3. **4-bit EXL3 weights** (15.4 GiB target + 1.2 GiB draft).
4. **Hybrid attention.** Only 16 of 64 layers keep a KV cache; at 3 bits that is
   12 KiB per token, 3.1 GiB for 270,336 tokens (*computed*, plus scales). That is
   why the full native context fits in 24 GiB next to the weights.
5. **41 engine patches**, kept only when the output stayed identical (or passed a
   numerics gate) and the benchmark improved:

| Area | Patches | What | Measured when kept |
|---|---|---|---|
| Verify loop | exl3 0001-0003, 0005, 0006 | batched greedy verify through the Bend acceptor, host/GPU overlap, draft CUDA graph, DFlash2 block mask, token-tree verify through the proved tree acceptor | |
| Token tree | 9008, 3012, 5109, 3013 | GPU tree builder, ancestor-masked verify attention, GDN along each row's ancestors, commit of the accepted path's K/V rows | lane 111.85 → 122.33 tok/s; round time unchanged |
| Layer tail and MLP | 2001, 7001, 8201, 8202, 8204, 8205b, 2106, 2107, 2113 | M ≤ 16 GEMMs, fused persistent MLP, one kernel per layer tail, weighted split-K, instruction diets, L2 discard of dead split-K partials | 2106/2107: −13.3 µs per layer; 2113: −0.40 to −0.50 ms per round |
| Projections | 2102, 2105, 9003b | grouped m16 qkv(+z) GEMMs for target and draft | |
| Attention | 3001-3007, 3010 | exact dequant, GQA split, row-invariant strided verify attention, CUDA prefill attention | 3010: 262,136-token prefill 722 → 537 s |
| Gated DeltaNet | 0001-0004, 5001, 5101, 5106, 5108 | history-free verify, commit replay, fused conv/recurrence/norm, b/a K-split, replay gather | 5108: replay 620 → 402 µs at 8 committed tokens |
| Draft | 6001, 9002, 9005c | draft graph, int4 draft head, head pruned to 896 blocks | full head: −2.7 % tok/s at 1K |
| Prefill GEMM | 3011 | fp16-accumulate wide tiles | −21.6 % per 2,048-row chunk |

6. **Power moved to the cores.** Capped at 250 W the card is power-bound, so a lower
   memory clock hands watts to the SMs: −1000 MHz saved 0.77-0.90 ms per round and
   −1500 MHz a further 0.25-0.46 ms, bit-identical (−2000 MHz: nothing more). Core
   offsets do nothing (+225 MHz faulted with Xid 109).

## Quality and correctness

| Check | Result |
|---|---|
| Speculation is lossless by construction | the target commits only its own greedy token at each position; the draft decides speed, never text |
| Invariance gate (`cs10`) | 45/45: 15 prompts × {normal draft, capped draft, all-wrong draft} give identical token IDs |
| Last three kept speedups (`cs10` → `cs11` → `cs12` → `tree3s`) | 20/20 lane answers and 15/15 C1 answers byte-identical, identical scores; the tree also passed a forced-chain run identical to `cs12` round by round |
| Kernel changes | bit-exact before keeping: 5108 GDN state hashes at 1-8 steps; 2113 all 64 layers, rows 1-8, 30 CUDA-graph replays; tree attention on all 5,040 tree shapes, each row equal to the chain kernel on its path |
| Lane scores (small samples, greedy, thinking on) | AIME 2025 3/3 · MMLU-Pro 8/10 · I3 Logic 2/4 · LiveCodeBench 1/3. Of the 6 misses, 4 hit the output budget (MMLU-Pro 8,192; I3 Logic and 2× LiveCodeBench 16,384) and 2 are wrong answers |
| Bend | `bend PROOF.bend` (Bend 2.0.29, 41 proof modules): "All terms check." Acceptance (chain and tree), tree descriptor derivation, speculation invariance over trees, plus kernel schedule and index laws. Proofs cover the Bend models; the older kernels' transcriptions are checked against their source, and the tree kernels' conformance rests on bitwise GPU differentials (evidence, not proof) |
| Not measured | the full Prime Envs suite at a 32,768-token budget; the 4-bit quantization's loss against BF16 |

## Result history

Lane primaries of kept runs. Compare only within one protocol (the task mix
differs between them).

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

Per-change notes and every dropped attempt are in [docs/benchmarks.md](docs/benchmarks.md).

## Reproduce

1. Download the pinned target and draft revisions above into a private
   `QWEN_STATE_ROOT` with `models/qwen38-27b-exl3/`, `models/dflash2-exl3/`,
   `cache/`, an `api-key` and the shared launch lock, as described in
   [Docker setup](docs/docker.md). Serving never downloads, converts or
   substitutes weights; it rejects any byte mismatch.
2. Install Docker Compose and NVIDIA Container Toolkit (CDI `nvidia.com/gpu=0`).
   The authenticated base image must already exist locally.
3. Build and explicitly opt into the unqualified candidate:

```sh
bash docker/build-exl3.sh candidate-ext qwen-inference:exl3   # or: baseline, candidate
export QWEN_STATE_ROOT=/absolute/path/to/state QWEN_IMAGE=qwen-inference:exl3
export QWEN_ALLOW_UNQUALIFIED=1
docker compose --project-name qwen-inference up --no-build --pull never --detach --wait
```

Do not start beside an existing inference service. The API is at
`http://127.0.0.1:18020/v1`, model `qwen3.8-27b`. Keep credentials out of
commands and Git. Docker owns runtime and restarts; Nix pins development tools,
the `.#bend` toolchain and a thin Compose adapter ([Nix](nix/STANDALONE.md)).

## Measure

- `bash autoresearch.sh` runs the benchmark lane above; its protocol is in
  [docs/benchmarks.md](docs/benchmarks.md). [Prime Envs + Verifiers](eval/README.md)
  own capability tasks, scoring, rewards and traces; this repository defines no
  quality tasks, scorers or combined intelligence score.
- The GSM8K comparison, against a running endpoint:

```sh
curl -o gsm8k-test.jsonl https://raw.githubusercontent.com/openai/grade-school-math/3101c7d5072418e28b9008a6636bde82a006892c/grade_school_math/data/test.jsonl
python3 -m bench.gsm8k_compare --api-key-file /path/to/api-key --data gsm8k-test.jsonl --out gsm8k.json
```

## Bend's role

`LAWS.bend` holds the accepted contract; `PROOF.bend` proves the production Bend
definitions against it. The serving path's greedy speculative acceptance (the
accepted prefix and bonus token of each DFlash2 block, and for the token tree the
longest matching root path and its descriptor) runs as proved Bend leaves
compiled to C. Engine changes follow the same order: state the law, prove the
implementation, then measure. A Bend proof covers the Bend definition only;
kernels, the Python server and speed need their own evidence. See
[architecture](docs/architecture.md).

## Limitations

- The deployment is an explicitly acknowledged **unqualified** candidate: one
  262,136-token prompt has run, but sustained 262,144-token capacity, quality and
  throughput are not qualified by the recipe settings.
- Generation is greedy only, one sequence at a time; chat `stream=true` is
  buffered SSE, so first-event time is not TTFT.
- Speed depends on the text (tokens per round: 3.37 at 32K context to 6.69 on
  quoting), the host's CPU load and the card's temperature, as measured above.
- Quality evidence is the lane's small samples; the full Prime Envs results for
  this engine are pending.
- In progress: a DFlash2 fine-tune on the target's own greedy outputs (training
  prompts disjoint from every evaluation set).

See the [documentation map](docs/README.md).
