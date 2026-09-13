#!/usr/bin/env bash
# Guard once, then exec SGLang. Docker owns stop, reaping and process restart.
set -euo pipefail
if (( $# > 0 )); then
  echo "Command overrides are not supported; use documented qualification controls." >&2
  exit 1
fi
# Preserve the shared inode. A losing container cannot stop a winning container.
if [[ ! -f /run/qwen-inference-launch.lock || -L /run/qwen-inference-launch.lock ]]; then
  echo "Mount an existing regular deployment lock file." >&2
  exit 1
fi
exec 9<>/run/qwen-inference-launch.lock
if flock --exclusive --nonblock 9; then
  echo "Acquired Qwen deployment ownership lock."
else
  echo "Another deployment owns this state directory." >&2
  exit 1
fi
exec bash /opt/qwen/serve/entrypoint.sh
