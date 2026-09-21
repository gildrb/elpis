# Measurement protocol

**Status:** the frozen matrix contains candidate comparisons and partial historical
measurements, not a qualified optimization result. The historical FP8 startup
trial allocated only 68004 pool tokens and stopped before readiness; that failed
trial is not the fixed packed KVarN recipe's current capacity verdict.
Individual native smoke/measurement successes do not satisfy the full capacity
and quality gates.
See [qualification](qualification.md) and [machine-readable matrix](../bench/matrix.json).

## 1. Freeze the comparison

Use one RTX 3090, TP1, an exclusive quiet endpoint, and exact image, ordered patch,
launch and target/draft inventory hashes. Save tokenizer/template identity,
sampling settings, actual input IDs, output budget, seed, cache condition and
power policy. Record failures and truncations explicitly; operational completion
is not a successful quality result. Each lane below states its admission rule.
Never combine percentage gains from different prompts or configurations.

Quality uses the frozen **Prime Envs + Verifiers** profiles under `eval/`.
`bench/` measures and orchestrates those unchanged native tasks; it does not
define their prompts, graders or a combined intelligence score. Current
MRCR/GraphWalks file-search tasks do not prove direct-context capability.
Historical direct runtimes under `eval/direct/` require their separate native
source, input and raw-result admission.

### Frozen finite autoresearch suite

The varied suite is a **new comparison segment requiring a fresh baseline**.
Its measured successful runtime is pending; the existing 2400-second bound is
a deadline, not evidence that all lanes finish within an hour. Do not compare
its results to the old math/C1-only 93 tok/s result as a like-for-like run.

Every invocation runs these mandatory lanes, exactly once in this order:

| Order | Native workload | Frozen selection and settings |
| --- | --- | --- |
| 1 | `tiny/aime25` | Unchanged three native seed-zero shuffled tasks, one rollout each, C1, greedy/thinking, 32768 output-token budget |
| 2 | `diverse/i3-logic` | First native eligible source-order task, one rollout, C1, greedy/thinking, 8192 output-token budget; unchanged native grader |
| 3 | Direct `diverse/graphwalks-bfs` | First native filtered source-order BFS row, frozen message/token hashes, 178769 templated input tokens, one rollout, 8192 output-token budget, original sampling parameters and exact BFS grader; new-segment request seed zero and native programmatic client with transport retries zero |
| 4 | C1 depth matrix | Unchanged 1024/8192/32768-input depths, five repetitions each in depth-then-repetition order, 1024 output-token budget and existing sampling/cache/nonce policy |

The long lane retains temperature 0.6, top-p 0.95, top-k 20 and thinking.
Its native `131073-262144` filter counts prompt characters, not tokens;
the independently frozen templated input count is 178769.
Request seed zero is a new expanded-segment freeze, not a historical config
default. The existing native environment/selection seed remains zero.

The short producer remains `eval/scripts/run diverse i3-logic --measure-power
--output <fresh-short-root>`. Direct collection uses
`python -m bench.direct_context collect --output <fresh-long-root> --key-file
<private-key-file> --container <owned-container-id>`, then independently replays
native evidence admission. These are orchestrated by `bash autoresearch.sh`
inside the existing already-owned maintenance window; they do not deploy,
recover, promote, flush a shared endpoint or change power policy.

The supervisor retains `supervisor.json` immediately. Before the first model
request, its deadline-supervised worker freezes both modern native task plans,
the direct GraphWalks identity, every lane's config/source/data hash closure,
repository producer snapshots and exact order into `benchmark.json`. Its
canonical `workload_sha256` excludes only the fresh modern launch-config path,
not the launch bytes or selected task hashes. Admission binds that workload
and benchmark digest, replays all lane-specific raw validators, requires the
same serving instance, and rejects any changed/missing lane. Old suite artifacts
cannot supply complete admission for this protocol.

`model_call_output_tok_s` remains the **math-only primary**:
all three math episodes' completion tokens divided by the sum of their native
model-call wall intervals. These intervals cover request send through the
fully received response, including prefill/decode/HTTP, not pure decode or
GPU time. Incorrect and length-truncated but operationally complete graded
answers stay in both the throughput denominator and the original quality
report. Failed/missing calls, invalid clocks and skipped episodes reject the
entire measurement; no faster subset is admitted.

Report `short_i3_model_call_output_tok_s` and `short_i3_reward` separately.
Report `long_graphwalks_model_call_output_tok_s` and
`long_graphwalks_reward` separately, retaining the historical native model-call
clock's exact scope as well as wrapper/native-evaluator durations. Do not pool
these clocks, rewards or C1 committed-counter windows into the math primary.
The same inclusion rule applies to the short and long lanes: an operationally
complete, natively graded length-truncated answer retains its official reward,
actual tokens and full model-call duration, with its truncation/finish status.
Operational errors or incomplete evidence still reject the entire suite.
Each native lane retains actual input/completion usage, original reward
components, truncation/error evidence, full requests/responses or traces and
producer logs. Modern native prompt usage excludes cache reads: reported
`input_tokens` adds available cached-input usage back, while retaining nullable
cache telemetry. Reasoning tokens are already a completion-token subset.
C1 rates still pool committed counter tokens over their own counter windows;
TTFT still averages the five observations per depth.

The single shared 2400-second limit, guardian recovery headroom, termination
reserve and owned-descendant cleanup remain unchanged. Selection, startup,
all four lanes and raw admission consume that same budget. A timeout or
missing case fails the run, retaining partial/failure artifacts and emitting
no successful metric lines. Successful whole-suite elapsed time is separate
from every per-lane model-call clock. This small suite is not full quality,
262144-token capability, or promotion qualification.

## 2. Use the official serving benchmark

Run `python3 -m sglang.benchmark.serving` from the exact runtime image. Its CLI
help was checked successfully in the frozen ordinary image on CPU. Do not install
a different SGLang benchmark package. The upstream module accepts
`OPENAI_API_KEY`; load it privately inside the container, never in argv or logs.

The dataset is upstream's ShareGPT source, frozen in `bench/matrix.json` at
revision `192ab2185289094fc556ec8ce5ce1e8e587154ca`. Download its named JSON from
that revision, verify its listed SHA256 and size, and mount it read-only at
`/bench-fixtures/sharegpt.json`. The full 672837942-byte file was downloaded from the pinned revision and its
SHA256 verified during this refactor; the raw fixture remains outside Git. Do not allow an implicit
upstream download or replacement when the local fixture is missing.

Use the fixed serving tokenizer path `/models/compact-target-rholsc8k/packed`.
The verified tokenizer bytes match the offline dense artifact, but that dense
directory is not required by the canonical container. Do not select a different
runtime representation or fall back to a Hub tokenizer.

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
  --tokenizer /models/compact-target-rholsc8k/packed \
  --dataset-name random --dataset-path /bench-fixtures/sharegpt.json \
  --tokenize-prompt --seed 20260913 --random-range-ratio 1 \
  --random-input-len 1024 --random-output-len 1024 \
  --num-prompts 8 --request-rate inf --max-concurrency 1 \
  --temperature 0 --top-p 1 --warmup-requests 0 --flush-cache \
  --cache-report --output-details --disable-tqdm \
  --output-file /cache/bench-RUN/c1-depth1024-cold.jsonl
```

This is a **cold-start, synthetic repeated-text throughput** fixture, not a capability
score or an agent workload. The upstream `random` implementation samples and
repeats/truncates ShareGPT input tokens. Integer inputs preserve exact lengths;
no chat template is applied. EOS is ignored by default for the fixed output
budget. `random-ids` is not substituted: upstream warns it can induce NaNs.
`--flush-cache` runs once after warmup, not before each request. Later requests
can reuse prefixes. For a warm paired run, first prime the complete same fixture,
omit `--flush-cache`, and require `SGLANG_IS_IN_CI` to be unset/false: upstream
also flushes when that variable is true. Built-in warmup only uses the first
prompt and caps its output at32 tokens; it does not warm every fixture request.
Never flush a shared production endpoint.

Keep raw official JSONL and request details private: they include full server
information. `--output-details` does not save input IDs; preserve a separate
exact-ID fixture snapshot. The [CPU-generated snapshot manifest](../bench/throughput-fixture.json)
records all eight planned depths; it is not a record of sent HTTP payloads. The seed controls client Python/NumPy generation, not
the server sampler. HTTP200 alone is counted as success upstream; independently
check nonempty output, requested completion length, truncation and errors.
Record completed output throughput, TTFT and TPOT distributions, end-to-end
latency and failures. Official output throughput divides successful output
tokens by the entire benchmark interval (including a server-info fetch); it is
not pure decode tokens/s. Missing cached-token telemetry is treated as zero
upstream, so verify field availability before claiming zero cache hits.
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
| I | CUDA graphs and attention execution | FP8/BF16 eager also disables overlap/autotune; KVarN disables both in either mode; eager requires commit graphs off |
| J | Final power policy | Same qualified recipe/workload; choose efficiency without hiding latency or throttling |

`bench/matrix.json` lists candidate questions, not supported configurations.
The current launcher fixes packed Qwen + DFlash2 at context 262144 and requires
the experimental image. Target-only, dense serving, smaller context rungs and
zero-patch serving are not admitted controls; preserve their historical evidence
without presenting them as current launch options. Dense offline numerical
references/oracles remain valid. FP8/BF16 controls require
`QWEN_COMMIT_GRAPH=0`; eager KVarN requires that setting too.
The launcher requires explicit `QWEN_ALLOW_UNQUALIFIED=1` for diagnostic
operation; this is not qualification or promotion.
Ampere lacks native NVFP4. Portable `fp4_mx_block16` is a distinct path with
whole-layer BF16 materialization and is not exposed by the launcher.
Do not relax guards to manufacture an off/on comparison. C2/C4 remain optional
regression questions, not supported settings of the fixed C1 launcher.

## 4. Depth and cache

Throughput depths are 1024, 8192, 32768, 65536, 131072, 196608, 245760 and
261118 input tokens with 1024 outputs plus two engine-reserve tokens at the
262144 objective. Attempt only a measured usable capacity; do not silently lower
an input to make it pass. The historical six-rung total-context ladder in
[capacity](capacity.md) is not a current runtime context selector; the launcher
admits only 262144. Keep the capacity diagnostic's 128-output-plus-two-token
reserve distinct from the throughput budget above.

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
