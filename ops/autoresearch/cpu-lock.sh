#!/usr/bin/env bash
# usage: cpu-lock.sh COMMAND... : run a CPU-heavy command under the shared compile lock,
# yielding first to any timing GPU window that is waiting (/tmp/elpis-gpu.pending).
while [ -e /tmp/elpis-gpu.pending ]; do sleep 5; done
exec flock -s /tmp/elpis-gpu.lock nice -n 19 "$@"
