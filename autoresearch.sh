#!/usr/bin/env bash
# Finite sampled-math + C1 measurement; never a deployment/promotion command.
set -euo pipefail
set +x
umask 077
if [[ ${1:-} == --help || ${1:-} == -h ]]; then
    cat <<'USAGE'
Usage: bash autoresearch.sh
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
Prerequisites: prepared offline eval/.venv, pinned Prime/Verifiers + AIME25 data,
locked sandbox images/caches, Docker access, nvidia-smi, and a healthy owned
native262144 Qwen/DFlash2 instance at http://127.0.0.1:18020 (280 W, Bend2.0.20).
Rootless Docker is fixed to unix:///run/user/1000/docker.sock.
The prepared Python supervisor enters pinned offline Nix only for its worker;
Nix startup and owned-process cleanup are inside the whole-command deadline.
Main must already own the maintenance window and perform recovery afterwards.
The deadline is min(2400 seconds, guardian remaining time minus 120 seconds).
There is no retry, task reduction, capacity probe, deployment or promotion.
Workload: tiny AIME25 (3 native seed0 shuffled tasks, 1 rollout, 32768 budget),
then fixed C1 depths1024/8192/32768 (5 repetitions each, 1024 output budget).
Only complete raw-evidence-admitted measurements print METRIC name=value:
  model_call_output_tok_s (primary: all native math calls pooled; wall time
    includes prefill/decode/HTTP, not decode-only, monotonic or GPU timing),
  committed_tps_32768, committed_tps_1024, committed_tps_8192,
  ttft_seconds_1024, ttft_seconds_8192, ttft_seconds_32768,
  tiny_math_reward, elapsed_seconds.
Artifacts: OUTPUT/{tiny-math,decode,logs,sources}, identity-before/after.json,
benchmark.json, admitted.json, measurement.json; failure/worker-failure.json
on rejection. C1 committed-counter rates and TTFT remain separate secondaries.
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
