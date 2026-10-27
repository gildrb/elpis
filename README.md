# elpis-fast

The fastest decode and prefill for 4-bit Qwen3.8-27B on one RTX 3090 that a pre-registered quality gate accepts, with the serving path's decision logic proven in Bend. Status: finished, no further optimization planned.

[elpis](https://github.com/gildrb/elpis) is the lossless sibling: same model, every changed op proven no less accurate than stock.

| | |
|---|---|
| Model | [Qwen3.8-27B](https://huggingface.co/r0b0tlab/Qwen3.8-27B-EXL3-4.00bpw), EXL3 4.00 bpw, 6 bpw head, 16.5 GB |
| Draft | [DFlash2](https://huggingface.co/r0b0tlab/Qwen3.8-27B-DFlash2-EXL3-4.00bpw), 8-row token tree, greedy, 1.25 GB |
| Context | 262,144 native, 3-bit KV cache (12 KiB per token, 16 of 64 layers), 270,336-token GPU prefix cache |
| GPU | one RTX 3090 24 GiB, 350 W cap, stock clocks |
| Engine | ExLlamaV3 1.5.0 + 54 SHA-pinned patches |

## Speed

`bash autoresearch.sh`, 2026-10-06, 350 W, geomeans, whole request (prefill and HTTP included):

| | elpis-fast `pfast5` | elpis `p3031b` stock |
|---|---|---|
| Prefill tok/s, 8K/32K/128K/262K | **1,220.7** | 997.4 |
| TTFT 8K/32K/128K/262K | 5.5 / 21.9 / 114.3 / **299.5 s** | 5.8 / 24.6 / 149.9 / 434.3 s |
| Decode tok/s, 1K/8K/32K/262K | **125.7** | 82.7 |
| ms per verify round, 1K → 262K | 25.4 → 45.6 | 26.7 → 112.9 |
| GSM8K, 40 questions (`pfast4`) | **205.3 tok/s**, 0.630 tok/J | 193.7 tok/s, 0.586 tok/J |
| Lane scores: AIME 2025, MMLU-Pro, I3 Logic, LiveCodeBench v6 | 14/20 | 14/20 |

Decode tok/s depends on the text (tokens per round); ms per round is engine speed. `pfast5` changes the text, the lane scores do not.

## What fast means

A speedup ships only if the text is unchanged or a pre-registered gate passes. Gates compare teacher-forced logits and 512-token continuations against two exact-numerics floors at 8K/32K/128K, with pre-set limits and a paired block bootstrap (rules R2, R3; decode rule D1 up to 262K).

| Change | Verdict |
|---|---|
| DFlash2 draft + 8-row tree | proven never to change the output |
| int8 Q·Kᵀ prefill (3021c) + decode verify (3032) | changes text; passes R2, R3, D1; shipped |
| int8 MLP linears (5115) | fails R2 and R3; rejected |
| fp16-accumulated P·V in decode | unresolved; not shipped (`EXL3_AV_FAST=0` restores the exact kernel) |

Fast is not lossless: prefill attention error vs fp64 is 3.6-33× stock (median 25×); 4.00 bpw weights and 3-bit KV cost quality vs BF16. Gate details and every dropped attempt: [bench/RESULTS.md](bench/RESULTS.md).

## Compared

Figures from their repositories, not rerun: different prompts, power and metric. Not a ranking.

| One RTX 3090 | Weights | Speculation | Metric | tok/s |
|---|---|---|---|---|
| elpis-fast | 4.00 bpw | DFlash2 + 8-row tree | whole request, 350 W | 161.9 lane; 205.3 GSM8K |
| elpis | 4.00 bpw | DFlash2 + 8-row tree | whole request, 350 W | 158.7 lane; 193.7 GSM8K |
| [trellis-serve](https://github.com/0xSero/trellis-serve/tree/1ace59c4b43ca16a50fb6b7acf8b3fd7e2351f96) MTP | 3.00 bpw | MTP | decode only | 96.2-141.3 |
| [trellis-serve](https://github.com/0xSero/local-ai-registry/blob/c6e6f4c796304229a3c11442af6f09673180d4f6/data/registry/recipe/qwen38-27b-exl3-3bpw-dflash2-rtx3090-sglang-tp1.json) DFlash2 | 3.00 bpw | DFlash2 | decode only | 98.2-227.0 |
| [r0b0tlab](https://github.com/r0b0tlab/qwen38-exl3-dflash2) | 4.00 bpw | DFlash2 | whole request, 350 W, same GSM8K test | 162.9 |

Same GSM8K workload, 350 W: elpis-fast is 26% faster. Prefill: trellis-serve MTP 21.9 s at 32K and 294 s at 209K; elpis-fast 21.9 s at 32K and 299.5 s at 262K, whole request.

## Why fast

| Lever | Measured |
|---|---|
| DFlash2 draft proposes 7 tokens in one pass | 1.00 → 3.39 tokens per round, round time unchanged |
| 8-row token tree, commit the longest match + 1 | 3.39 → 3.89 tokens per round; lane 111.9 → 122.3 tok/s |
| Prefill int8 Q·Kᵀ (3021c) | 262K TTFT 362.5 → 322.0 s |
| Prefill fusions: 8-warp attention, GDN conv, SiLU·up, 4096-row merge, no host syncs | 977.9 → 1,200.0 tok/s |
| Prefill K/V double-buffered ring (3022): next tile loads during compute, one barrier per tile | 262K TTFT 312.4 → 300.5 s |
| Tree verify pipe (9601): host check after launch, not before | −0.5 to −0.7% per round |
| Decode verify int8 Q·Kᵀ (3032): 3-bit K codes as exact int8, integer IMMA | −4.8% per round at 262K |
| 350 W cap, quiet fans | +32.3% tok/s vs 250 W at equal tok/J |
| Stock memory clock | +5.4% tok/s vs −1500 MHz |

The 54 patches: [patches/exl3](patches/exl3), [patches/exl3-ext](patches/exl3-ext).

## Bend

Every engine change ships as law → proof → measurement. The acceptance logic and kernel schedules are Bend programs with machine-checked proofs; the proven acceptor compiles to C, and the build checks it against a table.

| Proven in Bend | GPU evidence |
|---|---|
| Acceptance logic = list references (`exl3_accept`, `exl3_tree_accept`) | build-time table check |
| The draft never changes the output: `spec_inv`, `spec_inv_tree` over chain and 8-row tree, under row independence `~rinv` | 90/90 prompts bit-identical (normal, capped, all-rejected draft) |
| Each kernel schedule computes each output once, in a fixed order (GEMM, MLP, attention, GDN, prefill merge, draft head) | exact patches byte-identical; kernel state hashes bit-exact |
| Tree verify pipe (9601) always emits the sequential round's tokens; a mismatch always discards and recomputes | 5 injected faults, 243 recovered rounds, output identical |

```sh
nix run .#bend -- PROOF.bend                                    # 50 law + 52 proof modules: ALL PROOFS CHECK
nix run .#bend-verdict -- bend/tree_pipe_proof.bend --verdict   # one module, re-checked by the Lean 4 kernel; run each bend/*_proof.bend
nix develop --no-write-lock-file -c python3 -I -B bend/engine_trees.py OUT         # stock + patched ExLlamaV3
nix develop --no-write-lock-file -c python3 -I -B bend/pattn_sched_diff.py OUT/patched   # one source link: Bend model vs patched source
```

Boundary: proofs cover Bend models. Source links and the GPU tests above cover the link to CUDA. No proof covers numeric precision.

## Run

1. Install Docker with Compose and Buildx, the NVIDIA Container Toolkit (CDI `nvidia.com/gpu=0`) and Nix with flakes.
2. Make a private `QWEN_STATE_ROOT` with `models/`, `cache/`, `prefix-cache/` (mode 0700), `api-key` and `qwen-inference-launch.lock`.
3. Download the pinned weights and check every byte:

```sh
export QWEN_STATE_ROOT=/absolute/path/to/state
hf download r0b0tlab/Qwen3.8-27B-EXL3-4.00bpw --revision 3f1771b8c21f83cbb8e82169559ced9f38ca04e5 --local-dir "$QWEN_STATE_ROOT/models/qwen38-27b-exl3"
hf download r0b0tlab/Qwen3.8-27B-DFlash2-EXL3-4.00bpw --revision 265b5240592907d2d55ff0dc4d5f66569692604d --local-dir "$QWEN_STATE_ROOT/models/dflash2-exl3"
python3 -B prepare/verify-models.py --target "$QWEN_STATE_ROOT/models/qwen38-27b-exl3" --draft "$QWEN_STATE_ROOT/models/dflash2-exl3" --representation exl3
```

4. Build from source and start:

```sh
nix develop --no-write-lock-file -c true    # pinned Nix toolchain, once
bash docker/fetch-base.sh                   # the only network step: sha256-checks every base input
bash docker/build-base.sh                   # tags qwen-elpis:exl3-base only on a manifest match
bash docker/build-exl3.sh candidate-ext qwen-inference:exl3
export QWEN_IMAGE=qwen-inference:exl3
export QWEN_IMAGE_ID="$(docker image inspect -f '{{.Id}}' "$QWEN_IMAGE")"
export QWEN_ALLOW_UNQUALIFIED=1
docker compose --project-name qwen-inference up --no-build --pull never --detach --wait
```

- API: `http://127.0.0.1:18020/v1`, model `qwen3.8-27b`, greedy, one sequence. No second inference service on the GPU.
- Every model file is re-hashed against `prepare/exl3-manifest.json` at start.

## Measure

```sh
bash autoresearch.sh   # build this checkout + one GPU window: prefill and decode tok/s at 1K-262K
bash bench/lane.sh     # the served prefill suite; scoring: eval/README.md
curl -o gsm8k-test.jsonl https://raw.githubusercontent.com/openai/grade-school-math/3101c7d5072418e28b9008a6636bde82a006892c/grade_school_math/data/test.jsonl
python3 -m bench.gsm8k_compare --api-key-file /path/to/api-key --data gsm8k-test.jsonl --out gsm8k.json
```

## Setup

| | |
|---|---|
| GPU | RTX 3090 24 GiB (GA102, SM86), driver 595.71.05, PCIe 4.0 ×16, 350 W cap since 2026-09-28 |
| Host | Ryzen 7 5800X, 125.7 GiB RAM, NixOS 26.05, Linux 6.18.50 |
| Runtime | rootless Docker 29.7.2, CDI, read-only root, Ubuntu 24.04 CUDA base; Python 3.13.10, PyTorch 2.10.0+cu130, CUDA 13.0.96, Triton 3.6.0 |
| Server | [`serve/exl3_server.py`](serve/exl3_server.py): authenticated OpenAI-compatible `/v1` chat/completions + tool calls |
| Draft detail | 5 sliding-attention layers, block 8, reads target layers 5/19/33/47/61, top-16 selector |

## Limitations

- Greedy only, one sequence at a time, one GPU prefix cache for all clients.
- Evicted prefix pages wait in an 8 GiB host-RAM tier; no persistent prefix cache across restarts while the tier is on.
- Stream=true streams reasoning and content as generated; tool calls arrive at the end of the turn.
- Prefill and decode attention compute Q·Kᵀ in int8: outputs can differ from fp16.
- Exact logit ties can depend on max_tokens: compare outputs only at equal request parameters.

## References

| | |
|---|---|
| Protocol, every run, every kept and dropped attempt | [bench/RESULTS.md](bench/RESULTS.md) |
| Quality evaluator | [eval/README.md](eval/README.md) |
| Nix adapter | [nix/STANDALONE.md](nix/STANDALONE.md) |
| Upstream notices | [THIRD-PARTY.md](THIRD-PARTY.md) |
| Security reports | [SECURITY.md](SECURITY.md) |
| License | MIT ([LICENSE](LICENSE)) |
