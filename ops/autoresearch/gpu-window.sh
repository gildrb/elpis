#!/usr/bin/env bash
# One guarded GPU window (window lock always; exclusive compile lock for timing windows).
# usage: gpu-window.sh run   NAME IMAGE WINDOW SECONDS LOGFILE
#        gpu-window.sh serve NAME IMAGE WINDOW SECONDS OUTPUT_DIR
#   run  : start the precreated one-shot container, wait for it, save logs, restore baseline.
#   serve: start the server candidate, wait healthy, install the autoresearch descriptor
#          for OUTPUT_DIR, touch /tmp/gpu-window.ready, then wait for /tmp/gpu-window.release
#          (Main runs run_experiment in between), then restore baseline.
set -uo pipefail
export DOCKER_HOST=unix:///run/user/1000/docker.sock
S=/mnt/ssd/storage/ai/qwen3.8-27b/exl3-serving-2
MODE=$1 NAME=$2 IMG=$3 WIN=$4 SECS=$5 ARG=$6
W=$S/$WIN
LOG=/tmp/guardian-$WIN.log
# Two locks: the window lock serializes GPU windows; the compile lock (agents/builds take it
# shared) is taken exclusively only by timing windows, so CPU compiles proceed during
# non-timing windows (parity/repro/memcheck, or GPU_WINDOW_NONTIMING=1).
exec 8>/tmp/litos-gpu-window.lock
flock -x 8
rm -f /tmp/gpu-window.ready /tmp/gpu-window.release
case $WIN in parity-window-*|repro-window-*) NONTIMING=1 ;; *) NONTIMING=${GPU_WINDOW_NONTIMING:-0} ;; esac
if [[ $NONTIMING == 1 ]]; then
  echo "window lock held (non-timing) $(date +%T)"
else
  exec 9>/tmp/litos-gpu.lock
  # Priority flag: CPU jobs check it before taking the shared lock, so a waiting timing
  # window is not starved by a stream of overlapping shared holders.
  touch /tmp/litos-gpu.pending
  flock -x 9
  rm -f /tmp/litos-gpu.pending
  echo "lock held $(date +%T)"
fi
python3 "$S/recovery.py" --baseline-id b5e51bc1f6ac85b1b2af8db3612ff300190145397bb48b31e4cb7bf0f2d30f28 \
  --baseline-image sha256:fca4c263b6ba5c049f6f670f657798af6f1f6b630d1db94353a07604506606eb \
  --candidate-name "$NAME" --candidate-image "$IMG" --directory "$W" \
  --key-file /mnt/ssd/storage/ai/qwen3.8-27b/api-key \
  --lease /run/user/1000/qwen-packed64-docker-gpu0-maintenance.lock --seconds "$SECS" > "$LOG" 2>&1 &
GPID=$!
for _ in $(seq 1 180); do
  grep -qx armed "$LOG" && break
  kill -0 "$GPID" 2>/dev/null || { echo "guardian refused: $(cat "$LOG")"; exit 1; }
  sleep 1
done
grep -qx armed "$LOG" || { echo "guardian not armed"; kill "$GPID"; exit 1; }
python3 "$S/operate.py" --directory "$W" stop && python3 "$S/operate.py" --directory "$W" launch
rc=0
if [[ $MODE == run ]]; then
  rc=$(timeout 1500 docker wait "$NAME") || rc=124
  docker logs "$NAME" > "$ARG" 2>&1
  echo "payload exit=$rc"
else
  for _ in $(seq 1 240); do
    h=$(docker inspect -f '{{.State.Health.Status}}' "$NAME")
    [[ $h == healthy ]] && break
    [[ $(docker inspect -f '{{.State.Running}}' "$NAME") == true ]] || { h=died; break; }
    sleep 3
  done
  echo "health=$h"
  if [[ $h == healthy ]]; then
    CID=$(docker inspect -f '{{.Id}}' "$NAME")
    python3 - "$CID" "$W" "$ARG" <<'PY'
import json, os, sys
cid, win, out = sys.argv[1:4]
d = {"schema_version": 1, "container_id": cid,
     "api_key_file": "/mnt/ssd/storage/ai/qwen3.8-27b/api-key",
     "maintenance_directory": win, "output_directory": out}
p = '/run/user/1000/litos-autoresearch-operator.json'; t = p + '.tmp'
if os.path.lexists(p): os.unlink(p)
fd = os.open(t, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
os.write(fd, json.dumps(d).encode()); os.close(fd); os.rename(t, p)
PY
    touch /tmp/gpu-window.ready
    echo "ready for run_experiment $(date +%T)"
    for _ in $(seq 1 2400); do [[ -e /tmp/gpu-window.release ]] && break; sleep 1; done
  else
    docker logs "$NAME" 2>&1 | tail -30; rc=1
  fi
fi
python3 "$S/operate.py" --directory "$W" rollback
wait "$GPID"; g=$?
echo "guardian exit=$g last=$(tail -1 "$LOG") $(date +%T)"
[[ $(tail -1 "$LOG") == baseline_restored_authenticated ]] || { echo "RESTORE NOT CONFIRMED"; exit 2; }
exit "$rc"
