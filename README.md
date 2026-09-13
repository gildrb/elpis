# Qwen3.8-27B on one RTX 3090

Self-contained SGLang serving recipe for a 24 GB RTX 3090. This repository
contains the local patches, offline model preparation, Docker deployment,
Nix integration and fresh reasoning benchmarks. See the [documentation map](docs/README.md)
and [architecture contracts](docs/architecture.md). Any OpenAI-compatible client
can use the authenticated API; no agent application is required.

**Install the model files separately.** Nothing here downloads models or falls
back to different weights. Follow [offline preparation](prepare/REPRODUCE.md)
to reproduce and verify the exact supplied artifacts.

## Uploaded patches and recorded runs

- [Complete patch chain](patches/README.md): eight patch files covering 38 upstream files.
- [Benchmark run reports](bench/results/README.md): reasoning, cache, vision and trial results.

## Measured baseline speed

Actual RTX 3090 runs from [bench/results/native.json](bench/results/native.json):

| Run | End-to-end output | Decode (`1000 / mean TPOT`) |
|---|---:|---:|
| native-a | **132.78 tokens/s** | **137.69 tokens/s** |
| native-b | **130.99 tokens/s** | **135.90 tokens/s** |

Each run used eight short prompts, concurrency 1, cold cache, and up to 1,024
output tokens per request. These are **64K baseline timing measurements**, not
hard-reasoning scores or results for the unqualified 245,760-token candidate.

### Where the additional patches are

`patches/base/` holds original upstream source, **not patch files**.
The three baseline patches are directly under `patches/`. The five additional
patches are uploaded under [`patches/qualification/`](patches/qualification/):

- [`qwen3_5.patch`](patches/qualification/qwen3_5.patch)
- [`packed_w8_embedding.patch`](patches/qualification/packed_w8_embedding.patch)
- [`mm_utils.patch`](patches/qualification/mm_utils.patch)
- [`kvarn-candidate.patch`](patches/qualification/kvarn-candidate.patch)
- [`sampler-checkpoint2.patch`](patches/qualification/sampler-checkpoint2.patch)

Those candidate patches are packaged but **not enabled in default serving**.

## Single-profile target

The final deployment targets **245,760 total tokens with DFlash2**, using this
repository's SGLang patches. There will be no profile selector. The 64K runtime
below remains the temporary live baseline and rollback target until the 240K
candidate passes GPU memory, numerical, cache, quality and lifecycle checks.
Native and CUDA-graph runs are internal qualification stages, not user profiles.

## Current live baseline — not the final target

| Component | Fixed configuration |
|---|---|
| Runtime | SGLang v0.5.19; digest-pinned stock image |
| Target | Qwen3.8-27B W4A16, packed head, BF16-dequantized embeddings |
| Draft | W4A16 DFlash2, block 8, window 2048 |
| Capacity | Context 65,536; output budget 8,192; C1; pool cap 66,560 |
| Memory | FP8 KV, BF16 Mamba state, `extra_buffer`, K8, static fraction 0.94 |
| Execution | Prefill chunk 1024, logprob chunk 256, sleep-on-idle, `NCCL_MAX_CTAS=1` |
| API | `http://127.0.0.1:18020/v1`, model `qwen3.8-27b`, key required |

The exact image and source hashes are in [patches/manifest.json](patches/manifest.json).
Three local patches reproduce the temporary baseline runtime files. The complete
[qualification source bundle](docs/patches.md) contains eight ordered patch
stages covering 38 upstream files, including packed embeddings, KVarN and sampler
repairs. Its Docker/Nix inputs are build-only; they do not activate the candidate.
There is no fork checkout, remote patch fetch, runtime profile selector, or
source-guard opt-out.
Drivers, GPU selection, storage, fan policy and the measured setup's 280 W
power cap belong to the host. A working NVIDIA driver/container runtime is
required; installing Nix alone does not install a kernel driver.

## Start with Docker

Prepare this private directory first:

```text
STATE_ROOT/
  api-key
  qwen-inference-launch.lock
  cache/
  models/compact-target-rholsc8k/artifact/
  models/Qwen3.8-27B-DFlash2-W4A16/
```

Create the lock file only if absent, as described in the Docker guide; never
replace an existing lock. Use your own absolute path. Keep `api-key` private and do not place credentials
in commands, Git, or the image. Only one deployment may own the GPU and port.

```sh
export QWEN_STATE_ROOT=/absolute/path/to/state
docker compose up --build -d
```

Read [Docker setup](docs/docker.md) for prerequisites, key preparation, guards,
readiness and recovery. Build verifies stock sources, local patches and exact
patched bytes. Runtime verifies sources and model inventories before serving.
The reorganized packaging is not yet live-qualified; see
[qualification](docs/qualification.md).

## Start with Nix

The flake pins the package set and exposes the same guarded serving setup:

```sh
nix flake check path:. --no-write-lock-file
nix run path:.#serve -- --state-root /absolute/path/to/state
```

For always-on NixOS use, import `nix/qwen-inference.nix` or the exported NixOS
module. The existing consumer import path is preserved. The host still owns
its account, drivers and storage. See [Nix integration](nix/STANDALONE.md).
Do not run Docker and Nix deployments simultaneously.

## Measure reasoning, not easy arithmetic

[The benchmark guide](docs/benchmarks.md) runs pinned Reasoning Gym generators
with fresh private seeds, exact verified answers, frozen task banks and replay.
The suite covers logic deduction, constrained pathfinding, Sokoban planning
and RE-ARC grid induction. It separates correct answers, parser failures,
truncations and API failures.
Fresh instances reduce exact-answer memorization; public task families may
still be familiar to a model. No benchmark guarantees contamination-free rules.

The held-out hard suite scored **78/180 (43.3%)** with 8,192 output tokens:
**96 truncations**, **6 incorrect completed answers**, and zero API/parser/scorer
failures. This is budget-bound quality evidence, not a passing qualification.
See the [verified evaluation](bench/results/reasoning-evaluation.json) and
[measurement limits](docs/qualification.md#held-out-reasoning-evaluation).

The old numeric and passcode quality gates are removed. The retained eight
short prompts are only a throughput timing control. Their measured decode
rate was **135.9–137.7 tokens/s**; a cold 65K-input probe measured **114.9 tokens/s**.
These are scoped measurements, not promised performance or broad quality proof.
See [results and limits](docs/qualification.md).

## Repository

Development uses pinned `uv`, Ruff and `ty` with strict checks. See the
[development policy](docs/development.md) for commands, scope and known blockers.

- `patches/`: original-file provenance, local patches and strict verification.
- `serve/`, `docker/`, `Dockerfile`, `docker-compose.yml`: one serving recipe and lifecycle.
- `nix/`, `flake.nix`, `flake.lock`: pinned tools, deployment generation and NixOS integration.
- `prepare/`: offline artifact assembly, conversion and mandatory inventories.
- `bench/`, `docs/`: reasoning/cache diagnostics, measured results and operating instructions.

Never commit weights, keys, caches or private benchmark prompts/answers.
