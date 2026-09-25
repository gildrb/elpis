#!/usr/bin/env bash
# Finite EXL3 + Bend native broad-taskset + C1 measurement; never a deployment/promotion command.
set -euo pipefail
set +x
umask 077
if [[ ${1:-} == --help || ${1:-} == -h ]]; then
    cat <<'USAGE'
Usage: bash autoresearch.sh
Protocol exl3-native-broad-c1-request-v2: EXL3 + native DFlash2 serving, with the
Bend acceptance identity and engine patch manifest recorded when the image bakes
them (explicit null when absent). A new comparison segment: not comparable to
exl3-native-math3-c1-request-v1 or earlier segments; it needs a fresh baseline.
Required private operator descriptor (no inferred inputs or environment fallback):
  /run/user/1000/litos-autoresearch-operator.json
Exactly these JSON keys (replace placeholders; schema_version is integer 1):
  {"schema_version":1,"container_id":"<full 64-hex candidate ID>",
   "api_key_file":"/private/api-key",
   "maintenance_directory":"/private/existing-armed-maintenance",
   "output_directory":"/private/parent/new-autoresearch"}
Main atomically installs a NEW uid1000-owned regular 0600 descriptor for each run.
No symlinks; paths must be canonical and absolute. Key mode is 0400/0600.
The window must already be armed; output must not exist. Never edit the descriptor
during a run: supervisor/worker bind its file identity and exact content digest.
Prerequisites: prepared offline eval/.venv (with tokenizers and mmlu-pro), pinned
Prime/Verifiers sources, verified AIME25, MMLU-Pro, I3 Logic and LiveCodeBench
snapshots (eval/scripts/data --check <taskset>), the pinned local sandbox image,
Docker access (read-only inspect, one read-only in-container hashing probe via
docker exec, and the native evaluator's own sandbox containers), host nvidia-smi,
and a healthy owned EXL3 instance at http://127.0.0.1:18020 serving qwen3.8-27b
with max_model_len 262144, target/draft mounted under /models, on one RTX 3090 at
350 W. The server must accept the native client's identity sampling fields
(top_p 1, min_p 0, frequency/presence penalty 0, repetition penalty 1).
Rootless Docker is fixed to unix:///run/user/1000/docker.sock.
The prepared Python supervisor enters pinned offline Nix only for its worker;
Nix startup and owned-process cleanup are inside the whole-command deadline.
Main must already own the maintenance window and perform recovery afterwards.
The deadline is min(2400 seconds, guardian remaining time minus 120 seconds).
There is no retry, task reduction, capacity probe, deployment or promotion.
Workload, in this order, each taskset through the unchanged native Prime/Verifiers
evaluator (null harness, local Docker runtime, 1 rollout, native seed0 shuffle,
greedy thinking sampling from eval/configs/local.toml, per-call output budget):
  aime25         3 tasks, 32768 budget (eval/configs/tiny/aime25.toml)
  mmlu-pro      20 tasks,  8192 budget, zero-shot (eval/configs/broad/mmlu-pro.toml)
  i3-logic       6 tasks, 16384 budget (eval/configs/broad/i3-logic.toml)
  livecodebench  3 tasks, 16384 budget, official v6 date filter, sandbox-scored
                 (eval/configs/broad/livecodebench.toml)
then C1 raw-content depths 1024/8192/32768 (5 repetitions each,
depth-then-repetition, 1024 output budget, non-streaming, frozen nonce corpus).
No LLM judge is used anywhere.
Only complete raw-evidence-admitted measurements print METRIC name=value:
  model_call_output_tok_s (primary: all native model calls of all four tasksets
    pooled, sum of completion tokens / sum of call wall time; wall time includes
    prefill/decode/HTTP, not decode-only, monotonic or GPU timing),
  <ts>_output_tok_s, <ts>_reward, <ts>_truncated for ts in aime25, mmlu_pro,
    i3_logic, livecodebench (that taskset's calls pooled the same way; mean native
    reward over its episodes; number of calls with finish_reason length),
  c1_request_tok_s_1024, c1_request_tok_s_8192, c1_request_tok_s_32768
    (whole-request output tok/s: completion tokens / request wall time per depth,
    including prefill; not TTFT or decode-only),
  spec_accept_length (only when the server reports usage.exl3_spec on every C1
    row: committed tokens per native verify round, pooled over C1 rows),
  elapsed_seconds.
TTFT and committed decode rates are unavailable on this transport and never reported.
Artifacts: OUTPUT/{aime25,mmlu-pro,i3-logic,livecodebench,c1,logs,sources},
identity-before/after.json, supervisor.json, benchmark.json, admitted.json,
measurement.json; failure.json/worker-failure.json on rejection (nonzero exit, no
METRIC lines).
Sampled tasksets are not full qualification, a Prime-wide score, or proof of fluent
reasoning; there is no combined quality score. Inspect the retained upstream
text/reasoning and grades yourself.
USAGE
    exit 0
fi
[[ $# -eq 0 ]] || { printf 'Use bash autoresearch.sh --help\n' >&2; exit 2; }
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
[[ -x "$root/eval/.venv/bin/python" ]] || { printf 'Prepared eval/.venv is required; no installation is performed.\n' >&2; exit 2; }
unset PYTHONPATH PYTHONHOME QWEN_API_KEY OPENAI_API_KEY DOCKER_CONTEXT DOCKER_TLS_VERIFY DOCKER_CERT_PATH
export PYTHONDONTWRITEBYTECODE=1 PYTHONUNBUFFERED=1 LC_ALL=C
export HF_HUB_OFFLINE=1 HF_DATASETS_OFFLINE=1 HF_HUB_DISABLE_TELEMETRY=1
export UV_OFFLINE=1 UV_PYTHON_DOWNLOADS=never
export DOCKER_HOST=unix:///run/user/1000/docker.sock
cd -- "$root"
exec "$root/eval/.venv/bin/python" -m bench.autoresearch
