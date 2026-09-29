#!/usr/bin/env bash
# One guarded GPU window (window lock always; exclusive compile lock for timing windows).
# usage: gpu-window.sh run   NAME IMAGE WINDOW SECONDS LOGFILE     (env RUN_TIMEOUT: payload wait, default 1500 s)
#        gpu-window.sh serve NAME IMAGE WINDOW SECONDS OUTPUT_DIR
#   run  : start the precreated one-shot container, wait for it, save logs, restore baseline.
#   serve: start the server candidate, wait healthy, install the autoresearch descriptor
#          for OUTPUT_DIR, touch /tmp/gpu-window.ready, then wait for /tmp/gpu-window.release
#          (Main runs run_experiment in between), then restore baseline.
# Heat policy (user, 2026-09-25: the GPU gets very hot, so runs are rare, batched and delayed):
#   - approval: a window runs only if NAME matches a glob line of /tmp/elpis-gpu-allow. Only Main
#     writes that file, for an approved batch, and clears it afterwards. Checked before the window
#     lock and again once the lock is held;
#   - cool-down: before the guardian is armed the GPU must be <= GPU_COOL_C (default 50) C and
#     >= GPU_COOL_GAP (default 600) s must have passed since the previous window ended; waits up
#     to 1800 s, then refuses;
#   - evidence: temperature, power, SM clock and fan are sampled every 5 s into /tmp/gpu-thermal-WINDOW.csv.
set -uo pipefail
export DOCKER_HOST=unix:///run/user/1000/docker.sock
S=/mnt/ssd/storage/ai/qwen3.8-27b/exl3-serving-2
(( $# == 6 )) || { echo "usage: gpu-window.sh run|serve NAME IMAGE WINDOW SECONDS LOGFILE|OUTPUT_DIR"; exit 2; }
MODE=$1 NAME=$2 IMG=$3 WIN=$4 SECS=$5 ARG=$6
W=$S/$WIN
LOG=/tmp/guardian-$WIN.log
ALLOW=/tmp/elpis-gpu-allow
LAST=/tmp/elpis-gpu-last-window-end
TH=/tmp/gpu-thermal-$WIN.csv
COOL_C=${GPU_COOL_C:-50} GAP=${GPU_COOL_GAP:-600} RUN_TIMEOUT=${RUN_TIMEOUT:-1500}
case $MODE in run|serve) ;; *) echo "bad mode '$MODE'"; exit 2 ;; esac
for v in "$SECS" "$COOL_C" "$GAP" "$RUN_TIMEOUT"; do
  [[ $v =~ ^[0-9]+$ ]] || { echo "not a non-negative integer: '$v'"; exit 2; }
done
(( SECS >= 60 && SECS <= 2700 )) || { echo "lease $SECS s outside the guardian's 60-2700 s"; exit 2; }
[[ $MODE == serve ]] || (( RUN_TIMEOUT < SECS )) || { echo "RUN_TIMEOUT $RUN_TIMEOUT s must stay below the lease $SECS s"; exit 2; }
allowed() {
  local pat
  [[ -f $ALLOW ]] || return 1
  while IFS= read -r pat || [[ -n $pat ]]; do
    [[ -z $pat || $pat == \#* ]] && continue
    # shellcheck disable=SC2053  # glob match on purpose
    [[ $NAME == $pat ]] && return 0
  done < "$ALLOW"
  return 1
}
allowed || { echo "GPU HOLD: $NAME is not approved in $ALLOW (runs are batched and approved by Main)"; exit 3; }
# Two locks: the window lock serializes GPU windows; the compile lock (agents/builds take it
# shared) is taken exclusively only by timing windows, so CPU compiles proceed during
# non-timing windows (parity/repro/memcheck, or GPU_WINDOW_NONTIMING=1).
exec 8>/tmp/elpis-gpu-window.lock
flock -x 8
allowed || { echo "GPU HOLD: approval for $NAME withdrawn while it was queued"; exit 3; }
rm -f /tmp/gpu-window.ready /tmp/gpu-window.release
t0=$(date +%s)
while :; do
  temp=$(nvidia-smi --query-gpu=temperature.gpu --format=csv,noheader,nounits | tr -d ' ')
  [[ $temp =~ ^[0-9]+$ ]] || { echo "cannot read the GPU temperature: '$temp'"; exit 1; }
  since=$GAP
  [[ -f $LAST ]] && since=$(( $(date +%s) - $(stat -c %Y "$LAST") ))
  (( temp <= COOL_C && since >= GAP )) && break
  (( $(date +%s) - t0 < 1800 )) || { echo "GPU not cooled after 1800 s: $temp C, $since s since the last window"; exit 1; }
  sleep 30
done
echo "cool-down ok: $temp C, $since s since the last window $(date +%T)"
case $WIN in parity-window-*|repro-window-*) NONTIMING=1 ;; *) NONTIMING=${GPU_WINDOW_NONTIMING:-0} ;; esac
if [[ $NONTIMING == 1 ]]; then
  echo "window lock held (non-timing) $(date +%T)"
else
  exec 9>/tmp/elpis-gpu.lock
  # Priority flag: CPU jobs check it before taking the shared lock, so a waiting timing
  # window is not starved by a stream of overlapping shared holders.
  touch /tmp/elpis-gpu.pending
  flock -x 9
  rm -f /tmp/elpis-gpu.pending
  echo "lock held $(date +%T)"
fi
nvidia-smi --query-gpu=timestamp,temperature.gpu,power.draw,clocks.sm,fan.speed --format=csv,noheader,nounits -lms 5000 > "$TH" 2>&1 &
SPID=$!
finish() {
  kill "$SPID" 2>/dev/null
  wait "$SPID" 2>/dev/null
  touch "$LAST"
  awk -F', *' '$2 ~ /^[0-9]+$/ { n++; if ($2 > m) m = $2; p += $3 }
    END { if (n) printf "thermal: max %d C, mean %.0f W over %d samples\n", m, p / n, n; else print "thermal: no samples" }' "$TH"
}
trap finish EXIT
# Baseline = the live deployment, discovered rather than hard-coded (as elpis-promote.sh does): exactly
# one running guardian-gated container publishing 18020 whose promoted window verifies itself.
# Candidate windows keep S=exl3-serving-2: the guardian only needs the candidate's
# /maintenance-control to be the window's parent; the live container restarts via its own window.
read -r BASE_ID BASE_IMG < <(python3 - <<'PY'
import json, subprocess, sys
from pathlib import Path
def docker(*a):
    return subprocess.run(['docker', *a], check=True, capture_output=True, text=True, timeout=30).stdout
ids = docker('ps', '--filter', 'publish=18020', '--filter', 'status=running', '--format', '{{.ID}}').split()
if len(ids) != 1:
    sys.exit(f'baseline discovery: expected one running container on 18020, found {len(ids)}')
c = json.loads(docker('inspect', ids[0]))[0]
ep = c['Config']['Entrypoint'] or []
if not (len(ep) > 8 and ep[:3] == ['python3', '/maintenance-control/launch-gate.py', '--window']
        and ep[5] == c['Name'][1:] and ep[7] == c['Image']):
    sys.exit('baseline discovery: live container is not guardian-gated')
state = [m['Source'] for m in c['Mounts'] if m['Destination'] == '/maintenance-control']
st = json.loads((Path(state[0]) / ep[3] / 'status.json').read_text())
if not (st['state'] == 'promoted_authenticated_main_verified'
        and st.get('verified_baseline') == {'id': c['Id'], 'image': c['Image'], 'name': c['Name']}
        and st.get('main_verification') == {'completion': True, 'configuration': True}):
    sys.exit('baseline discovery: live window is not promoted for this container')
print(c['Id'], c['Image'])
PY
) && [[ $BASE_ID =~ ^[0-9a-f]{64}$ && $BASE_IMG =~ ^sha256:[0-9a-f]{64}$ ]] || { echo "cannot discover the live baseline"; exit 1; }
echo "baseline $BASE_ID $BASE_IMG"
python3 "$S/recovery.py" --baseline-id "$BASE_ID" \
  --baseline-image "$BASE_IMG" \
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
  rc=$(timeout "$RUN_TIMEOUT" docker wait "$NAME") || rc=124
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
p = '/run/user/1000/elpis-autoresearch-operator.json'; t = p + '.tmp'
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
