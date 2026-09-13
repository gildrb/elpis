# Measurement protocol

**Status:** the matrix is frozen planning, not a measured optimization result.
The new FP8 trial allocated only 68004 pool tokens and stopped before readiness.
No refactored recipe has passed the full capacity and quality gates.
See [qualification](qualification.md) and [machine-readable matrix](../bench/matrix.json).

## 1. Freeze the comparison

Use one RTX 3090, TP1, an exclusive quiet endpoint, and exact image, ordered patch,
launch and target/draft inventory hashes. Save tokenizer/template identity,
sampling settings, actual input IDs, output budget, seed, cache condition and
power policy. Reject failed/truncated requests; do not count them as fast outputs.
Never combine percentage gains from different prompts or configurations.

Quality uses the frozen **Prime Envs + Verifiers** profiles under `eval/`.
`bench/` contains engineering measurements only. Current MRCR/GraphWalks
file-search tasks do not prove direct-context capability. Historical direct
runtimes under `eval/direct/` must pass their separate compatibility gates first.

## 2. Use the official serving benchmark

Run `python3 -m sglang.benchmark.serving` from the exact runtime image. Its CLI
help was checked successfully in the frozen ordinary image on CPU. Do not install
a different SGLang benchmark package. The upstream module accepts
`OPENAI_API_KEY`; load it privately inside the container, never in argv or logs.

The dataset is upstream's ShareGPT source, frozen in `bench/matrix.json` at
revision `192ab2185289094fc556ec8ce5ce1e8e587154ca`. Download its named JSON from
that revision, verify its listed SHA256 and size, and mount it read-only at
`/bench-fixtures/sharegpt.json`. The recorded hash is public LFS metadata, not a
claim that this refactor downloaded the full dataset. Do not allow an implicit
upstream download or replacement when the local fixture is missing.

After verifying that fixture, create a new private output directory under
`/cache/bench-RUN` in the candidate container. Replace `RUN` with a unique run ID.
The official module appends JSONL: never reuse an old output filename.

```sh
docker exec "$CONTAINER" bash -c '
  set -eu
  set +x
  export OPENAI_API_KEY
  OPENAI_API_KEY="$(cat /app/api_key.txt)"
  exec python3 -m sglang.benchmark.serving "$@"
' benchmark \
  --backend sglang --base-url http://127.0.0.1:18020 \
  --model qwen3.8-27b \
  --tokenizer /models/compact-target-rholsc8k/artifact \
  --dataset-name random --dataset-path /bench-fixtures/sharegpt.json \
  --tokenize-prompt --seed 20260913 --random-range-ratio 1 \
  --random-input-len 1024 --random-output-len 1024 \
  --num-prompts 8 --request-rate inf --max-concurrency 1 \
  --temperature 0 --top-p 1 --warmup-requests 0 --flush-cache \
  --cache-report --output-details --disable-tqdm \
  --output-file /cache/bench-RUN/c1-depth1024-cold.jsonl
```

This is a **cold, synthetic repeated-text throughput** fixture, not a capability
score or an agent workload. The upstream `random` implementation samples and
repeats/truncates ShareGPT input tokens. Integer inputs preserve exact lengths;
no chat template is applied. EOS is ignored by default for the fixed output
budget. `random-ids` is not substituted: upstream warns it can induce NaNs.
For a warm paired run, omit `--flush-cache` and reuse the same seed/fixture after
an explicitly recorded warmup. Never flush a shared production endpoint.

Keep raw official JSONL and request details private. Record completed output
throughput, TTFT and TPOT distributions, end-to-end latency and failures.
Measure prefill throughput from engine phase metrics; do not rename total input
throughput or input/TTFT as pure prefill throughput. Record DFlash acceptance and
accepted tokens per verify from engine telemetry where available; otherwise null.

## 3. Optimization ladder

Every row is **unmeasured** until its before/after artifacts and frozen Prime Envs
results exist. Dependencies may force a bundled correctness change; label that
bundle instead of assigning a gain to one patch.

| Step | Controlled question | Admission / comparison rule |
| --- | --- | --- |
| A | Exact upstream, target-only, public target | Zero-patch control; report unsupported artifact or memory limits honestly |
| B | W4A16 target preparation / packed head | Compare exact artifact identities; full BF16 weights alone exceed 24 GiB |
| C | FP8 KV versus BF16 KV | Same model, source, execution and prompt; measure quality and usable context |
| D | DFlash2 off/on | Same image and weights; minimal required compatibility fixes form a disclosed bundle |
| E | Packed W8 embedding versus dense representation | Same all-row dequantized values; different runtime kernel still needs qualification |
| F | KVarN off/on versus applicable upstream compression | Same experimental image: active sampler repairs must not confound the KV comparison |
| G | Recurrent-state precision | BF16/FP16 only if actually supported; preserve restore correctness |
| H | Block size, draft window, prefill chunk | Change one variable; current KVarN admits only its strict block8/window2048/chunk1024 envelope |
| I | CUDA graphs and attention execution | Current eager control also disables overlap/autotune; not a graph-only attribution |
| J | Final power policy | Same qualified recipe/workload; choose efficiency without hiding latency or throttling |

`bench/matrix.json` lists candidate values, not supported configurations.
Ampere lacks native NVFP4. Portable `fp4_mx_block16` is a distinct path with
whole-layer BF16 materialization; evaluate only if the pinned runtime admits it.
KVarN target-only is blocked by missing generic worker sticky-status propagation.
Do not relax that guard to manufacture an off/on comparison. C2/C4 are optional
regression points and may be unsupported by the C1-only KVarN implementation.

## 4. Depth and cache

Throughput depths are 1024, 8192, 32768, 65536, 131072, 196608, 245760 and
261118 input tokens with 1024 outputs plus two engine-reserve tokens at the
262144 objective. Attempt only a measured usable capacity; do not silently lower
an input to make it pass. Separately apply all six total-context rungs in
[capacity](capacity.md), whose diagnostic reserves 128 outputs plus two tokens.

At each admitted depth report cold and warm TTFT, prefill/decode throughput,
output length, VRAM and failures. Use official `generated-shared-prefix` options
(`--gsp-num-groups`, `--gsp-prompts-per-group`, `--gsp-system-prompt-len`,
`--gsp-question-len`, `--gsp-output-len`, `--gsp-ordered`) for prefix reuse
throughput. Freeze their values and seed separately from the random fixture.
Use [cache diagnostics](cache.md) for identical prefixes, extensions, divergent
continuations and recurrent-state restoration. Correctness diagnostics are not
quality scores. Preserve both cached-token counts and numerical evidence.

## 5. Power and acceptance

Sweep **200, 225, 250, 280, 300 and 350 W** only after recipe qualification and
with explicit maintenance ownership. Validate the board's allowed range first.
Record and restore the original cap; containers must not modify host power/fans.
The observed historical cap is 280 W, not a new recommendation.

Use the fixed C1 1024-in/1024-out workload, 32 prompts, three repetitions per
point, identical warm-cache conditions and a documented thermal settling rule.
Measure actual watts, clocks, temperature, throttle reasons, latency and completed
output tokens. Integrate sampled board power over the stated interval to obtain
joules; report tokens/joule for that interval, not an invented decode-only value.
Do not benchmark while preparation or other GPU/CPU work confounds results.

Each retained step needs speed, VRAM, usable context and per-environment quality
before/after evidence. Record OOM, allocation rejection, truncation, retries and
numerical failures. The default stays explicitly unqualified until deep prefill,
meaningful generation, repeated stability and Prime Envs quality all pass.
