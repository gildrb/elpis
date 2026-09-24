# Qwen3.8-27B EXL3 + DFlash2 on one RTX 3090, with Bend-proved decisions

**The live endpoint serves Qwen3.8-27B EXL3 with native DFlash2 speculative
decoding at 262144 native context on one 24 GiB SM86 GPU. Bend states and proves
the decision logic the serving path must get right.** Optimize C1 agent latency
and useful code/reasoning output at native context.

| Question | Current answer |
|---|---|
| Target | `r0b0tlab/Qwen3.8-27B-EXL3-4.00bpw` at `3f1771b8c21f83cbb8e82169559ced9f38ca04e5` |
| Draft | `r0b0tlab/Qwen3.8-27B-DFlash2-EXL3-4.00bpw` at `265b5240592907d2d55ff0dc4d5f66569692604d` |
| Engine | ExLlamaV3 `355c6ee10fbd25b79070316a81ea0708cc18155a` + native DFlash2 from base image `sha256:b35314f48c7684b4c9cf3d59f4c21395316aa1fc0925db782f460005aa2602ff`; `baseline` image leaves it unchanged, `candidate` applies the SHA-pinned `patches/exl3` series and the Bend acceptance artifact |
| Server | `serve/exl3_server.py`: authenticated OpenAI-compatible chat/completions, tool calls, greedy only, one sequence |
| Recipe | context 262144, cache 270336, CQ3 ([launcher](serve/exl3-entrypoint.sh)) |
| Hardware | 1× NVIDIA RTX 3090, 24 GiB, SM86 |
| Weights identity | Every runtime file SHA256-pinned in [prepare/exl3-manifest.json](prepare/exl3-manifest.json), rehashed at each start |

## Bend's role

`LAWS.bend` holds the accepted contract; `PROOF.bend` proves the production
Bend definitions against it. The current work is **EXL3 greedy speculative
acceptance**: the accepted-prefix and bonus-token decision for each DFlash2
block, proved in Bend and executed in the serving path. Further engine changes
follow the same order: state the law, prove the implementation, then measure.
A Bend proof covers the Bend definition only; kernels, the Python server and
speed need their own evidence. See [architecture](docs/architecture.md).

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
bash docker/build-exl3.sh baseline qwen-inference:exl3   # or: candidate
export QWEN_STATE_ROOT=/absolute/path/to/state QWEN_IMAGE=qwen-inference:exl3
export QWEN_ALLOW_UNQUALIFIED=1
docker compose --project-name qwen-inference up --no-build --pull never --detach --wait
```

Do not start beside an existing inference service. The API is at
`http://127.0.0.1:18020/v1`, model `qwen3.8-27b`. Keep credentials out of
commands and Git. Docker owns runtime and restarts; Nix pins development tools,
the `.#bend` toolchain and a thin Compose adapter ([Nix](nix/STANDALONE.md)).

## Measure before promoting

`bash autoresearch.sh` runs the EXL3 benchmark lane; its protocol is in
[docs/benchmarks.md](docs/benchmarks.md). [Prime Envs + Verifiers](eval/README.md)
own capability tasks, scoring, rewards and traces. This repository defines no
quality tasks, scorers or combined intelligence score.

## Limitations

- The deployment is an explicitly acknowledged **unqualified** candidate:
  262144-token capacity, sustained quality and throughput are not established
  by the recipe settings.
- Generation is greedy only; chat `stream=true` is buffered SSE, so first-event
  time is not TTFT.
- Bend-proved acceptance is in progress and not yet executed by the live server.
- Prime Envs quality results for this engine are pending.

See the [documentation map](docs/README.md).
