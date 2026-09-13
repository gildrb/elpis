# Qwen3.8-27B + DFlash2 on one RTX 3090

**A reproducible SGLang optimization recipe targeting 262144 tokens—not yet a
qualified native-context deployment.** Optimize C1 agent latency, reusable long
prefixes and useful code/reasoning output on one 24 GiB SM86 GPU.

| Question | Current answer |
|---|---|
| Model / quantization | Qwen3.8-27B, W4A16 compressed-tensors and packed head; BF16 embeddings reconstructed from W8 |
| Engine | Public SGLang v0.5.19 at `0bcd822377da7b5718e674eaf9c870d349424dd1` + explicit Git patches |
| Runtime | `lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9` |
| Draft | `syvai/Qwen3.8-27B-DFlash2-W4A16` at `4d30ec736ffc6b8688dc2ae2b502d9b48bdec279`; exact repository/inventory in [preparation](prepare/REPRODUCE.md) |
| Hardware | 1× NVIDIA RTX 3090, 24 GiB, SM86, TP=1; observed host driver 595.71.05 |
| Context objective | **262144 total tokens**, with six qualification rungs from 131072 |
| C1 speed / deep-context speed | Not measured for the refactored recipe |
| VRAM / quality delta | FP8 startup peak sampled 22978 MiB; no steady-serving measurement or Prime Envs A/B result |
| Cache strategy | FP8 control; KVarN retained as an explicit experiment, not rejected or promoted without measurements |

[The first bounded GPU trial](bench/results/refactor-fp8-startup.json) requested
262144 context but allocated only **68004 pool tokens** with FP8. It did not reach
API readiness before the controlled stop. Native context remains unproven.

The pin is the latest release found during the [current upstream/reference
audit](docs/reference-audit.md). Newer main is a qualification candidate, not a
proven 3090 improvement. This is **pinned upstream + a visible patch layer**,
not a private fork. No whole upstream files or source-reconstruction framework
are retained.

## Reproduce

1. Supply the exact public inputs and follow [model preparation](prepare/REPRODUCE.md).
   Serving does not download, transform or silently replace weights. That guide
   records complete offline reproduction: exact target/draft inventories and a
   byte-identical all-row embedding proof. Historical producer records stay intact.
2. Install Docker Compose and NVIDIA Container Toolkit. Prepare a private
   `QWEN_STATE_ROOT` with `models/`, `cache/`, `api-key` and the shared ownership
   lock as described in [Docker setup](docs/docker.md). Do not start beside an
   existing inference service.
3. Build and explicitly opt into the unqualified candidate:

```sh
export QWEN_STATE_ROOT=/absolute/path/to/state
docker compose build
export QWEN_ALLOW_UNQUALIFIED=1
docker compose up -d
```

The requested native context can fail allocation. Opt-in acknowledges that risk;
it does not certify capacity. There is no automatic lower-context fallback.
Experimental patches require separate explicit selection. See [patch ordering
and evidence](patches/README.md) and [qualification gates](docs/qualification.md).
The authenticated OpenAI-compatible API is at `http://127.0.0.1:18020/v1`,
model `qwen3.8-27b`. Keep credentials out of commands and Git.

Docker owns runtime/restarts. Nix pins development tools and provides a thin
Compose adapter; it is not a second launch recipe. See [Nix](nix/STANDALONE.md).
The host owns driver, storage, fan policy and optional power limiting. No new
power default is recommended until the exact recipe's 200–350 W sweep completes.

## Measure before promoting

[The benchmark protocol](docs/benchmarks.md) specifies an isolated optimization
ladder, context-capacity and context-depth tables, prefix cold/warm/extension,
C1/C2/C4 crossover and power efficiency. Use official SGLang utilities for normal
throughput, TTFT and TPOT. Keep custom diagnostics only for questions they do
not answer, such as recurrence/cache consistency or kernel correctness.

[Prime Envs + Verifiers](eval/README.md) own capability tasks, scoring, rewards
and traces, with fixed smoke/quick/full A/B configurations. This repository
does not define its own quality tasks, scorers or combined intelligence score. File-search environments
must not be reported as direct-context capacity evidence.

The methodology follows [syv-ai/qwen38-27b-rtx3090](https://github.com/syv-ai/qwen38-27b-rtx3090):
measure quantization, memory, speculation, graphs, cache and power separately.
Translate ideas to SGLang; do not port vLLM internals or copy its performance
numbers. [Reference findings](docs/reference-audit.md) include Roycorp source
availability, Ampere tradeoffs and upstream patch-removal candidates.

Historical runtime results remain [separately indexed](bench/results/README.md).
They do not qualify this refactor. See the [documentation map](docs/README.md)
and [strict development checks](docs/development.md).
