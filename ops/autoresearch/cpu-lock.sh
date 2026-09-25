#!/usr/bin/env bash
# usage: cpu-lock.sh COMMAND... : run a CPU-heavy command under the shared compile lock,
# yielding first to any timing GPU window that is waiting (/tmp/litos-gpu.pending).
while [ -e /tmp/litos-gpu.pending ]; do sleep 5; done
exec flock -s /tmp/litos-gpu.lock nice -n 19 "$@"
