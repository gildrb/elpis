#!/usr/bin/env bash
# usage: cpu-lock.sh COMMAND... : run a CPU-heavy command under the shared compile lock,
# yielding first to any timing GPU window that is waiting (/tmp/eta-gpu.pending).
while [ -e /tmp/eta-gpu.pending ]; do sleep 5; done
exec flock -s /tmp/eta-gpu.lock nice -n 19 "$@"
