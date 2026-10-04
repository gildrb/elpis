# elpis

**Lossless speculative decoding for Qwen3.8-27B on one RTX 3090. Bend proves it.**

- Model: Qwen3.8-27B, EXL3 4.00 bpw weights, 3-bit KV cache.
- Context: 262,144 tokens (native).
- Speculation: DFlash2 draft, 8-row token tree, greedy.
- GPU: one RTX 3090, 350 W cap.
- Proof: `bend PROOF.bend --verdict` (Bend 2.0.34, Lean 4.34.0 kernel): ALL PROOFS CHECK.

elpis is the research build. [elpis-fast](https://github.com/gildrb/elpis-fast) is the speed build. It uses the same model and benchmarks. It uses int8 prefill attention and makes no lossless claim.

| | elpis | elpis-fast |
|---|---|---|
| Rule | Keep a speedup only if claims 1-3 stay proven | Keep the fastest build with measured quality |
| Draft can change the output | No: proven and tested | No: proven and tested |
| Prefill attention | fp32 sums; error bound ≤ stock (proven) | int8 Q·Kᵀ; error 3.6-33× stock (measured) |
| Cold prefill, geomean | 1,014.7 tok/s | 1,164.9 tok/s |

## Lossless

Lossless = claims 1, 2 and 3. Each claim has a Bend proof and a GPU test.

| # | Claim | Proof | Test |
|---|---|---|---|
| 1 | **The draft never changes the output.** elpis emits the tokens that its target emits at one token per round. This is true for every prompt and every draft, also an adversarial draft. | `rinv_laws` over `spec_inv` / `spec_inv_tree`: chain and 8-row tree, with the engine's own commits. The row hypothesis `~rinv` is derived from the kernel laws, not assumed. | 15 prompts × tree / chain × normal / capped / all-rejected draft: 90/90 token-identical (#77, #78). |
| 2 | **Speculation adds zero error.** Acceptance compares token ids exactly. Nothing is approximated, sampled or thresholded. | Follows from 1. | Follows from 1. |
| 3 | **No changed op is less accurate than stock.** For each op that elpis changed, decode and prefill, the worst-case rounding-error bound is ≤ the bound of stock ExLlamaV3 `355c6ee` (no speculation, one token per step). This is true for every input. | `err_*_laws`: the rounding steps from each input term to each output, for elpis and for stock, copied from source (file:line, checked by `bend/err_*_diff.py`). A dominated step count has a bound that is not larger (`err_bound_laws.dom_sigma`; Higham 2002, Lemma 3.1). | Error vs an fp64 reference, per op ([benchmarks §10](docs/benchmarks.md#10-lossless-definition-draft-and-m1-checks-proof-status-2026-10-03)). |

Lossless does not mean:

- **Lossless against BF16.** The 4.00 bpw weights and the 3-bit KV cache cost quality. The lane measures this cost. No proof covers it.
- **Bit-identical to stock.** elpis and stock round differently. elpis without the draft also differs: 4 of 15 long generations diverge, each at a near-tie (top-2 logits 0.016-0.17 apart).
- **More accurate on each input.** The proof bounds the worst case. On one input, either kernel can be nearer to the exact value.

Trust base (tested, not proven):

- `H_conform`: the CUDA and host code agree with their Bend models (`bend/*_diff.py` source links, GPU bitwise differentials).
- `H_det`, `H_mma`: the kernels are deterministic. `mma.m16n8k16` computes each row from that row only.
- Rounding follows the standard model, with per-step bounds in the class order of `bend/err_bound.bend`.
- `H_mem`: the GPU memory model holds at the split-K barrier.
- `H_deploy`, `H_route`, `H_stock`: the persisted autotune records, the default environment, and the default dispatch of stock.
- Other hypotheses: each law module names them in its header. Example: `H_park` in `bend/err_pfix_laws.bend` (one prefill CTA per SM; the host checks it before the first launch).

## Speed

**Target:** most tok/s at 262,144 context, one RTX 3090, 350 W, lossless.

**Status:** `p3031b` (#78, `sha256:6f597b13…`) = `p9502` (#77) + attention fixes 3030 (decode) and 3031 (prefill). The fixes make claim 3 true. Cost vs a fresh #77 run: decode +0.6-0.8 % ms per round, time to first token (TTFT) +0.4-0.8 %.

| 350 W | elpis `p3031b` (#78) | elpis-fast `pfast1` |
|---|---|---|
| Cold prefill, geomean over 8K / 32K / 128K / 262K | 1,014.7 tok/s | 1,164.9 tok/s |
| TTFT, 8K / 32K / 128K / 262K | 5.60 / 24.42 / 148.75 / 431.47 s | 5.58 / 22.67 / 123.66 / 322.98 s |
| Decode, median ms per verify round, 1K / 8K / 32K context | 25.75 / 26.40 / 28.60 | 25.50 / 26.24 / 28.39 |
| Lane scores: AIME 2025 · MMLU-Pro · I3 Logic · LiveCodeBench v6 | 3/3 · 8/10 · 2/4 · 1/3 = 14/20 | 3/3 · 8/10 · 1/4 · 1/3 = 13/20 (`p3021p`, #73) |
| Attention error vs fp64, relative to stock | decode 0.9998×, prefill 0.890× (mean) | prefill 25× (median) |

| Workload, 350 W | tok/s | tok/J | Run |
|---|---|---|---|
| Lane: 20 calls, thinking on, whole request | **158.74** | not recorded | #78 |
| GSM8K: 40 questions, 512 tokens, median of 5 runs | **202.9** | 0.617 | #68 (`tree3s`) |
| C1: 1K / 8K / 32K prompt, 1,024 tokens out, whole request | 185.3 / 73.3 / 29.0 | 0.578 / 0.217 / 0.085 | #68 (`tree3s`) |

- #68 is an older image. #78 did not run GSM8K or C1.
- Tokens per round change with the text. Compare tok/s only on the same text.
- #78 data: plan `g6f597b13`, 2026-10-03/04, windows interleaved with #77 ([benchmarks §10](docs/benchmarks.md#10-lossless-definition-draft-and-m1-checks-proof-status-2026-10-03)). elpis-fast data: 2026-09-30.

## Compared

Figures of other projects come from their repositories. elpis did not run them again. No other result uses the same prompts, power cap and metric. This is not a ranking.

| One RTX 3090 | Weights | Speculation | Context / KV | Power | Reported tok/s |
|---|---|---|---|---|---|
| **elpis** (measured) | 4.00 bpw | DFlash2 + 8-row tree | 262,144 / 3-bit | 350 W cap | 158.7 lane (#78); 202.9 GSM8K (#68); whole request |
| [trellis-serve](https://github.com/0xSero/trellis-serve/tree/1ace59c4b43ca16a50fb6b7acf8b3fd7e2351f96) README (MTP) | 3.00 bpw | MTP, 3 steps / 4 tokens | 212,992 / fp8 | not published | 96.2 prose, 141.1 code (thinking off); 141.3 prose, 129.3 code (thinking on); decode only ([sweep](https://github.com/0xSero/local-ai-registry/blob/c6e6f4c796304229a3c11442af6f09673180d4f6/data/registry/speed-sweep/qwen38-27b-exl3-3bpw-mtp-vision-rtx3090-sglang-tp1-sweep.json)) |
| trellis-serve fastest recipe ([DFlash2](https://github.com/0xSero/local-ai-registry/blob/c6e6f4c796304229a3c11442af6f09673180d4f6/data/registry/recipe/qwen38-27b-exl3-3bpw-dflash2-rtx3090-sglang-tp1.json), status "candidate") | 3.00 bpw | DFlash2, 5.0 bpw draft, block 8 | 131,072 / fp8 | not published | 98.2 prose, 225.1 code (thinking off); 227.0 prose, 195.4 code (thinking on); decode only |
| [r0b0tlab](https://github.com/r0b0tlab/qwen38-exl3-dflash2) | 4.00 bpw | DFlash2 | 8,192 / FP16 | 350 W cap | 162.9 GSM8K |

| One RTX 3090 | 32K prompt: TTFT | Longest prompt shown |
|---|---|---|
| **elpis** (#78) | 24.4 s (1,344 tok/s) | 262,052 tokens: 431.5 s |
| **elpis-fast** (`pfast1`) | 22.7 s (1,448 tok/s) | 262,052 tokens: 323.0 s |
| trellis-serve MTP | 21.9 s (1,497 tok/s) | 208,858 tokens: 294 s |
| trellis-serve DFlash2 | 35.9 s (914 tok/s) | 126,782 tokens: 187 s |
| r0b0tlab | not published (150K prompt: 594 tok/s) | 262,080 tokens (needle test) |

- **Same test.** GSM8K, 350 W cap, same 40 questions: elpis 202.9, r0b0tlab 162.9 tok/s (+24.6 %). [`bench/gsm8k_compare.py`](bench/gsm8k_compare.py) runs the workload of r0b0tlab's [`acceptance_check.py`](https://github.com/r0b0tlab/qwen38-exl3-dflash2/blob/main/scripts/acceptance_check.py).
- **Metric.** trellis-serve reports decode only. elpis divides by the full request time: prefill and HTTP included.
- **Bits.** 3.00 bpw reads 25 % fewer weight bits per token than 4.00 bpw (*computed*). Its quantization error is larger. This README does not compare quality.
- **Clocks.** trellis-serve publishes no power limit. Its DFlash2 soak held the SMs at 1.74 GHz. elpis: 1.51 GHz median per call (#68 lane).

## Proofs and tests

| Claim | Evidence | Result |
|---|---|---|
| The draft never changes the output | Bend: `rinv_laws` over `spec_inv` / `spec_inv_tree`; `~rinv` derived (`rowinv_link`, `rowinv_served`, `lmhead`) | proven |
| Same, on the GPU | 15 prompts × normal / capped / all-rejected draft × tree and chain | 90/90 on #76, #77, #78 |
| No changed op is less accurate than stock | Bend: `err_bound_laws`, `err_gemm`, `err_gemm_runs`, `err_gdn`, `err_elem`, `err_attn`, `err_attn_dec` (3030), `err_prefill`, `err_pfix` (3031) | proven |
| Same, measured against fp64 | Each op, decode and prefill; attention on captured q and 3-bit K/V at 10 context lengths | decode ops 0.05-0.84× stock; attention mean error 0.9998× (decode), 0.890× (prefill) stock |
| Acceptance logic | `exl3_accept`, `exl3_tree_accept` = list references; emitted to C; checked by table at build | proven |
| Full contract | `bend PROOF.bend --verdict`: 58 law modules, 62 proof modules | ALL PROOFS CHECK |
| Kernel changes | GDN state hashes, 1-8 steps (5108); 64 layers × rows 1-8 × 30 graph replays (2113); all 5,040 tree shapes vs the chain kernel (3012) | bit-exact |
| Decode speedups `cs10` → `tree3s` keep the text | lane 20 + C1 15 answers | byte-identical |
| Power and clocks keep the text | 250 W vs 350 W; memory offsets 0 … −2000 MHz | byte-identical |

- [`LAWS.bend`](LAWS.bend) = contract. [`PROOF.bend`](PROOF.bend) = proofs. Order for each engine change: law → proof → measurement.
- Bend proves facts about Bend models of the kernels. Source links and GPU tests check the link from model to CUDA. No proof covers this link. See the trust base in [Lossless](#lossless).
- `err_attn_finding` and `err_prefill_finding` prove that the attention before 3030 / 3031 did not meet claim 3.

## How

| Lever | Measured |
|---|---|
| DFlash2 draft: one pass proposes 7 tokens | 1.00 → 3.39 tokens per round at 1K; round time unchanged (≈34 ms, 250 W) |
| 8-row token tree: 7 nodes, best first; commit the longest matching path + 1 | 3.39 → 3.89 tokens per round at 1K; lane 111.85 → 122.33 tok/s (250 W) |
| 52 engine patches: 5 [`patches/exl3`](patches/exl3) + 47 [`patches/exl3-ext`](patches/exl3-ext) | each changed op: worst-case error bound ≤ stock (claim 3) |
| 350 W cap, quiet fans (≤ 80 % to 84 °C) | lane +32.3 % tok/s vs 250 W at equal tok/J (0.497 vs 0.495) |
| Stock memory clock at 350 W | +5.4 % tok/s, +6.4 % tok/J vs −1500 MHz ([sweep](docs/benchmarks.md#3-power)) |

## Run

1. Make a private `QWEN_STATE_ROOT` with `models/qwen38-27b-exl3/`, `models/dflash2-exl3/`, `cache/`, `prefix-cache/` (mode 0700), `api-key` and `qwen-inference-launch.lock` ([docs/docker.md](docs/docker.md)).
2. Put the pinned weights (see [Setup](#setup)) in `models/`. The server does not start if one byte is different.
3. Install Docker Compose and the NVIDIA Container Toolkit (CDI `nvidia.com/gpu=0`). Load the authenticated base image locally.
4. Build and start:

```sh
bash docker/build-exl3.sh candidate-ext qwen-inference:exl3   # or: baseline, candidate
export QWEN_STATE_ROOT=/absolute/path/to/state QWEN_IMAGE=qwen-inference:exl3
export QWEN_ALLOW_UNQUALIFIED=1
docker compose --project-name qwen-inference up --no-build --pull never --detach --wait
```

- API: `http://127.0.0.1:18020/v1`, model `qwen3.8-27b`. Do not run another inference service on the same GPU.
- Prefix cache: kept across restarts if `QWEN_IMAGE_ID` = the full sha256 of `QWEN_IMAGE`. `QWEN_PREFIX_PERSIST=0` turns it off.
- Docker owns runtime and restarts. Nix pins the tools, the `.#bend` toolchain and a Compose adapter ([nix/STANDALONE.md](nix/STANDALONE.md)).

## Measure

```sh
bash autoresearch.sh   # the lane; protocol: docs/benchmarks.md; scoring: Prime Envs + Verifiers (eval/README.md)
curl -o gsm8k-test.jsonl https://raw.githubusercontent.com/openai/grade-school-math/3101c7d5072418e28b9008a6636bde82a006892c/grade_school_math/data/test.jsonl
python3 -m bench.gsm8k_compare --api-key-file /path/to/api-key --data gsm8k-test.jsonl --out gsm8k.json
```

## Prove

```sh
nix run .#bend -- PROOF.bend                     # every law, TypeScript checker (about 11 min)
nix run .#bend-verdict -- PROOF.bend --verdict   # the same, checked again by the Lean-proven kernel (about 1.7 h)
python3 -B bend/err_gemm_diff.py                 # one source link: Bend model text vs patched source
```

## Setup

| | |
|---|---|
| GPU | RTX 3090 24 GiB (GA102, SM86), VBIOS 94.02.42.80.1F, PCIe 4.0 ×16, driver 595.71.05 |
| Power, clocks | 350 W cap since 2026-09-28 (250 W before); core and memory offsets 0; the lane checks all three via NVML |
| Host | Ryzen 7 5800X (8 cores / 16 threads), 125.7 GiB, NixOS 26.05, Linux 6.18.50 |
| Runtime | rootless Docker 29.7.2, CDI, read-only root; Ubuntu 24.04 CUDA base; Python 3.13.10, PyTorch 2.10.0+cu130, CUDA 13.0.96, cuBLAS 13.1.0.3, Triton 3.6.0 |
| Engine | ExLlamaV3 1.5.0 `355c6ee` (r0b0tlab `community`, native DFlash2) + 5 [`patches/exl3`](patches/exl3) + 47 [`patches/exl3-ext`](patches/exl3-ext), SHA256-pinned |
| Server | [`serve/exl3_server.py`](serve/exl3_server.py): authenticated OpenAI-compatible `/v1` chat/completions + tool calls, greedy, one sequence |
| Target | [`r0b0tlab/Qwen3.8-27B-EXL3-4.00bpw`](https://huggingface.co/r0b0tlab/Qwen3.8-27B-EXL3-4.00bpw) @ `3f1771b8` (`Qwen/Qwen3.8-27B`): 48 Gated DeltaNet + 16 full-attention layers, hidden 5,120, vocab 248,320; 4.00 bpw, 6 bpw head; 16.5 GB |
| Draft | [`r0b0tlab/Qwen3.8-27B-DFlash2-EXL3-4.00bpw`](https://huggingface.co/r0b0tlab/Qwen3.8-27B-DFlash2-EXL3-4.00bpw) @ `265b5240` (`incoai/Qwen3.8-27B-DFlash2`): 5 sliding-attention layers, block 8, reads target layers 5/19/33/47/61, top-16 selector; 1.25 GB |
| Recipe | [`serve/exl3-entrypoint.sh`](serve/exl3-entrypoint.sh): context 262,144, cache 270,336, 3-bit KV (12 KiB per token: 16 of 64 layers keep KV); 8 verify rows per round; each file hashed again against [`prepare/exl3-manifest.json`](prepare/exl3-manifest.json) at start |

## Limitations

```
- 262K prompts run only in the prefill suite: one 262,052-token prompt per run.
  Sustained 262K capacity, quality and speed are not qualified.
- The proof bounds the worst case only. On #78, prefill attention is <= stock in mean,
  p99 and max in 29/32 cells (31/32 within one fp16 ulp). Decode attention max error
  is above stock in some cells; the kernel before 3030 has the same cells.
- Live serving runs the elpis-fast lineage (p3021r and later, int8 Q·Kᵀ).
  It makes no lossless claim. #78 is not promoted.
- Greedy only. One sequence at a time.
- Chat stream=true sends buffered SSE. The first event is not the TTFT.
- Exact logit ties can depend on max_tokens (cs12: token 39457 at 8192 vs 54185 at 256,
  p = 0.28775 each). Compare only at equal request parameters.
- Speed changes with the text (3.37-6.69 tokens per round), host CPU load and GPU temperature.
- Quality: lane samples only. The full Prime Envs suite and the 4-bit vs BF16 loss are not measured.
- Long-context reasoning with 3-bit KV vs fp16 KV is not measured.
- Draft fine-tune and draft 4-8 bpw sweep: stopped before a result (GPU queue paused
  2026-09-30). A different draft can change the speed, not the output (claim 1).
- GDDR6X temperature is not readable on this card. The memory runs at the stock clock.
```

## References

- Protocol, every run, every change, every dropped attempt: [docs/benchmarks.md](docs/benchmarks.md)
- Architecture and the Bend proof boundary: [docs/architecture.md](docs/architecture.md)
- Deployment: [docs/docker.md](docs/docker.md)
- Evaluator: [eval/README.md](eval/README.md)
- All docs: [docs/README.md](docs/README.md)
