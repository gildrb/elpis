#!/usr/bin/env bash
# Finite EXL3 + Bend native-math + C1 measurement; never a deployment/promotion command.
set -euo pipefail
set +x
umask 077
if [[ ${1:-} == --help || ${1:-} == -h ]]; then
    cat <<'USAGE'
Usage: bash autoresearch.sh
Protocol exl3-native-math3-c1-request-v1: EXL3 + native DFlash2 serving, with the
Bend acceptance identity and engine patch manifest recorded when the image bakes
them (explicit null when absent). Not comparable to earlier segments except the
math primary definition; a new segment needs a fresh baseline.
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
Prerequisites: prepared offline eval/.venv (with tokenizers), pinned Prime/Verifiers
+ AIME25 data, the pinned local sandbox image, Docker access (read-only inspect and
one read-only in-container hashing probe via docker exec), host nvidia-smi, and a
healthy owned EXL3 instance at http://127.0.0.1:18020 serving qwen3.8-27b with
max_model_len 262144, target/draft mounted under /models, on one RTX 3090 at 280 W.
The server must accept the native client's identity sampling fields (top_p 1,
min_p 0, frequency/presence penalty 0, repetition penalty 1).
Rootless Docker is fixed to unix:///run/user/1000/docker.sock.
The prepared Python supervisor enters pinned offline Nix only for its worker;
Nix startup and owned-process cleanup are inside the whole-command deadline.
Main must already own the maintenance window and perform recovery afterwards.
The deadline is min(2400 seconds, guardian remaining time minus 120 seconds).
There is no retry, task reduction, capacity probe, deployment or promotion.
Workload: tiny AIME25 (3 native seed0 shuffled tasks, 1 rollout, 32768 budget,
greedy, thinking), then C1 raw-content depths 1024/8192/32768 (5 repetitions each,
depth-then-repetition, 1024 output budget, non-streaming, frozen nonce corpus).
Only complete raw-evidence-admitted measurements print METRIC name=value:
  model_call_output_tok_s (primary: all native math calls pooled; wall time
    includes prefill/decode/HTTP, not decode-only, monotonic or GPU timing),
  c1_request_tok_s_1024, c1_request_tok_s_8192, c1_request_tok_s_32768
    (whole-request output tok/s: completion tokens / request wall time per depth,
    including prefill; not TTFT or decode-only),
  tiny_math_reward,
  spec_accept_length (only when the server reports usage.exl3_spec on every C1
    row: committed tokens per native verify round, pooled over C1 rows),
  elapsed_seconds.
TTFT and committed decode rates are unavailable on this transport and never reported.
Artifacts: OUTPUT/{tiny-math,c1,logs,sources}, identity-before/after.json,
supervisor.json, benchmark.json, admitted.json, measurement.json;
failure.json/worker-failure.json on rejection (nonzero exit, no METRIC lines).
Sampled math is not full qualification, a Prime-wide score, or proof of fluent
reasoning. Inspect the retained upstream text/reasoning and grades yourself.
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
