# Measurement protocol

**Status:** the serving stack is EXL3 with native DFlash2 speculative decoding
(greedy, one sequence, native context 262144, CQ3 cache) on one RTX 3090. The
frozen lane below is protocol `exl3-native-math3-c1-request-v1`, a **new
comparison segment that needs a fresh baseline**. Numbers from earlier serving
segments are not comparable, except that the math primary keeps its exact
definition (same native producer, tasks, budget and formula) and is therefore a
whole-stack comparison only. No lane here is full quality, capacity or promotion
qualification.

## 1. Freeze the comparison

Use one RTX 3090, an exclusive quiet endpoint, and exact image, engine patch
manifest, Bend acceptance identity and target/draft inventory hashes. Save
tokenizer identity, sampling settings, actual input IDs, output budget, cache
condition and power policy. Record failures and truncations explicitly;
operational completion is not a successful quality result. Never combine
percentage gains from different prompts or configurations, and never compare
numbers across runner-configuration changes.

Quality uses the frozen **Prime Envs + Verifiers** profiles under `eval/`
(prime-envs `c4d04dfe`, verifiers `ef47b2e9`). `bench/` orchestrates those
unchanged native tasks; it does not define their prompts, graders or a combined
intelligence score.

## 2. Frozen autoresearch lane

`bash autoresearch.sh` (`bench/autoresearch.py` supervisor/worker,
`bench/exl3.py` identity, math and C1 logic) runs exactly once, in this order:

| Order | Workload | Frozen selection and settings |
| --- | --- | --- |
| 1 | `tiny/aime25` | Unchanged three native seed-zero shuffled tasks, one rollout each, one call each, greedy/thinking, 32768 output-token budget, `eval/configs/local.toml` sampling |
| 2 | C1 depth matrix | Raw-content depths 1024/8192/32768 (±2 tokens), five repetitions each in depth-then-repetition order, 1024 output-token budget, greedy, `top_p` 1, `n` 1, normal EOS, non-streaming |

### Operator contract

Main installs a fresh private descriptor at
`/run/user/1000/litos-autoresearch-operator.json` (uid 1000, mode 0600, regular
file, no symlink) with exactly `schema_version` 1, the full 64-hex
`container_id`, canonical absolute `api_key_file` (0400/0600),
`maintenance_directory` of an already armed guardian window, and a not yet
existing `output_directory`. The supervisor binds the descriptor's inode and
digest, verifies guardian lease/launch-lock/mutex ownership on every poll,
requires the container to be the guardian candidate publishing only
`127.0.0.1:18020`, and enforces `min(2400 s, guardian deadline - 120 s)` over
capture, both workloads and admission. The worker runs inside pinned offline
Nix. There is no retry, task reduction, warmup, flush, capacity probe, power
change, deployment or promotion.

Prerequisites: prepared offline `eval/.venv` (including `tokenizers`), pinned
Prime/Verifiers sources and AIME25 snapshot, the pinned local sandbox image in
`eval/.cache/sandbox-image`, host `docker` and `nvidia-smi`, and a healthy
owned EXL3 instance serving `qwen3.8-27b` with target/draft mounted under
`/models`. The server must accept the native client's identity sampling fields
(`top_p` 1, `min_p` 0, frequency/presence penalty 0, repetition penalty 1) and
reject other values.

### Serving identity

Before any workload and again after both, the worker captures and requires
byte-identical identity (`identity-before.json`, `identity-after.json`):

- Docker: full container ID, name, immutable image ID, creation and start time,
  PID, restart count, entrypoint/command, public `QWEN_*` environment, network,
  published ports, read-only root and mounts; image labels and layer digests.
- One read-only in-container probe (`docker exec` of the image's
  `/opt/venv/bin/python -I -B`): SHA256 of every file under `/opt/qwen` (baked
  server, launchers, engine patch manifest, Bend artifacts) and
  `/model-preparation`; the installed `exllamav3` package tree and its
  `exllamav3_ext` extension; engine distribution version and install URL; all
  installed distributions; target/draft inventories (every file size; SHA256 of
  each file up to 64 MiB, checked against `prepare/exl3-manifest.json`; weights
  are rehashed by the image's own startup inventory).
- Engine patch manifest `/opt/qwen/exl3-patches.json`: when present, its bytes
  must match image label `io.litos.exl3.patches-sha256` and every listed
  installed file must rehash to its recorded post-patch SHA256. When absent the
  record is explicit `null` and the label must be absent.
- Bend acceptance identity `/opt/qwen/bend-exl3/identity.json`: when present,
  schema `litos-exl3-bend-accept/1`, `identity_sha256` must recompute over the
  document's other keys and every listed artifact must match its baked bytes.
  When absent the record is explicit `null`.
- Authenticated `/health` and `/v1/models` (`max_model_len` 262144 is the
  reported limit, not a capacity test).
- Host `nvidia-smi`: exactly one `NVIDIA GeForce RTX 3090`, power limit and
  enforced limit 280 W (declared operating point; never changed here), UUID,
  bus, driver and memory.
- The host tokenizer file behind the target mount, whose bytes must equal both
  the served file and its manifest pin.

### Math primary

`model_call_output_tok_s` is the **math-only primary**: all three native episode
calls' completion tokens divided by the sum of their native model-call wall
intervals (`bench.autoresearch.model_call_observations`). These intervals cover
request send through the fully received response, including prefill, decode and
HTTP; they are not decode-only or GPU time. Incorrect and length-truncated but
operationally complete graded answers stay in both numerator/denominator and
quality report. Failed or missing calls, invalid clocks, skipped/reordered
episodes, changed sampling/model/endpoint, an unpinned scorer, a resolved config
differing from the offline-replayed frozen plan, or traces outside the identity
capture window reject the whole measurement.

The native producer is invoked directly as
`uv run --project eval --no-sync eval @ eval/configs/local.toml @ <launch>
-o <group>/aime25 --no-rich --no-push --env.taskset.dataset-name <snapshot>`
from `eval/.sources/prime-envs`, where `<launch>` is `eval/configs/tiny/aime25.toml`
with only its sandbox image replaced by the pin. The evaluator/source/config/data
hash closure and native seed-zero task selection are frozen before the run and
must be unchanged afterwards. `tiny_math_reward` is the mean native weighted
reward of the three episodes.

Replaying the historical EXL3 same-three traces through this admission path
reproduces 23127 tokens / 233.5167772769928 s = 99.03785188233918 tok/s with
reward 1.0 (a pre-segment comparison run, not a baseline for this protocol).

### C1 whole-request secondaries

Before any generation, the worker sizes each of the 15 prompts from the frozen
`bench/throughput-prompts.jsonl` corpus (deterministic nonce
`[measurement run R of 5 at depth D]`, fixed instruction) to raw-content depth
within two tokens using the served tokenizer bytes on CPU, writes the exact
request bytes, and retains the server's `/v1/chat/completions/render` token IDs.
Raw-content depth is not total templated depth; both counts are recorded.

Each row is one non-streaming `/v1/chat/completions` request. Its wall time runs
from request send through the complete response body. Admission replays every
row from raw files: HTTP 200, one assistant choice, `stop`/`length` finish
(`length` only at the 1024 budget), `prompt_tokens` equal to the rendered ID
count, consistent totals, and sequential non-overlapping requests.

`c1_request_tok_s_<depth>` = sum of the five rows' completion tokens / sum of
their request wall times. It is **whole-request output throughput including
prefill**, not TTFT and not decode-only. TTFT and committed decode rates are
unavailable on this transport and are never reported or estimated.

### Speculative acceptance

When every C1 row's usage carries `exl3_spec` = `{rounds, committed}` (native
verify rounds and tokens committed by them; `rounds <= committed <=
min(completion_tokens, 8 * rounds)`), `spec_accept_length` = total committed /
total rounds over all 15 C1 rows is reported. It is absent when the server does
not report the field; partial reporting rejects the run. Math traces do not
retain this field.

### Admission and output

Artifacts: `supervisor.json`, `benchmark.json` (frozen workload and
`workload_sha256`), `identity-before.json`, `identity-after.json`,
`tiny-math/{provenance,aime25}`, `c1/{plan.json,depth-D-rep-R/}`, `logs/`,
`sources/`, `admitted.json` (all metrics, per-call/per-row records and the
retained evidence hash closure) and `measurement.json`. Only a complete admitted
run prints `METRIC` lines: `model_call_output_tok_s`, the three
`c1_request_tok_s_*`, `tiny_math_reward`, optional `spec_accept_length`, and
`elapsed_seconds` (whole command, not a per-lane clock). Any rejection writes
`failure.json` (and `worker-failure.json` from the worker) and exits nonzero.

Not measured by this lane: TTFT, committed decode throughput, power/energy and
262144-token capacity.

## 3. Power

The declared operating point is 280 W, checked but never changed by the lane.
Sweep other caps only with explicit maintenance ownership, recording and
restoring the original cap; containers must not modify host power or fans.
Measure actual watts, clocks, temperature and throttle reasons over a stated
interval before reporting tokens per joule.
