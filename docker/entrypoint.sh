#!/usr/bin/env bash
# Foreground PID 1: Docker restart repeats every guard, not just the API probe.
set -euo pipefail
if (( $# > 0 )); then
  echo "This image accepts no runtime profile or command overrides." >&2
  exit 1
fi
# The host and container must lock the same inode. Never unlink this file.
# Acquire before guards or children; a losing launcher must not clean up a winner.
if [[ ! -f /run/qwen-inference-launch.lock || -L /run/qwen-inference-launch.lock ]]; then
  echo "An existing regular deployment lock file must be mounted." >&2
  exit 1
fi
exec 9<>/run/qwen-inference-launch.lock
if flock --exclusive --nonblock 9; then
  echo "Acquired Qwen deployment ownership lock."
else
  echo "Another Qwen launcher owns this state directory." >&2
  exit 1
fi
export PORT=18020 SERVED_MODEL_NAME=qwen3.8-27b PREPARE=0
export MODELS_DIR=/models API_KEY_FILE=/app/api_key.txt
export SGLANG_HEALTH_CHECK_TIMEOUT=300
image='lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9'
patches=/opt/qwen/patches
python3 "$patches/verify.py" --manifest "$patches/manifest.json" --phase original --root /sglang-original --image "$image"
python3 "$patches/verify.py" --manifest "$patches/manifest.json" --phase replacement --root /sgl-workspace/sglang/python/sglang/srt --image "$image"

# Separate process groups include SGLang's worker descendants.
set -m
bash /opt/qwen/serve/entrypoint.sh &
server=$!
python3 /opt/qwen/serve/supervisor.py "$PORT" "$API_KEY_FILE" "$SERVED_MODEL_NAME" --standalone &
monitor=$!
cleanup() {
  trap '' TERM INT
  for child in "$server" "$monitor"; do
    if kill -0 -- "-$child" 2>/dev/null; then
      if ! kill -TERM -- "-$child"; then
        echo "Child group $child exited during termination." >&2
      fi
    fi
  done
  # Observe whole groups, not just leaders: workers can outlive their parent.
  deadline=$((SECONDS + 45))
  while (( SECONDS < deadline )); do
    remaining=0
    for child in "$server" "$monitor"; do
      if kill -0 -- "-$child" 2>/dev/null; then
        remaining=$((remaining + 1))
      fi
    done
    if (( remaining == 0 )); then
      break
    fi
    sleep 0.2
  done
  for child in "$server" "$monitor"; do
    if kill -0 -- "-$child" 2>/dev/null; then
      if ! kill -KILL -- "-$child"; then
        echo "Child group $child exited during forced termination." >&2
      fi
    fi
  done
  for child in "$server" "$monitor"; do
    if wait "$child"; then
      echo "Child $child stopped."
    else
      echo "Child $child stopped with failure." >&2
    fi
  done
}
trap 'cleanup; exit 0' TERM INT
if wait -n "$server" "$monitor"; then
  echo "A required service child exited unexpectedly." >&2
else
  echo "A required service child failed; requesting guarded restart." >&2
fi
cleanup
exit 1
