#!/usr/bin/env bash
# usage: ar-serve.sh TAG IMAGE_ID [WAIT_PATTERN] [extra mkcand args...]
# Timing serve window for autoresearch: container qwen-exl3-ar-TAG, window ar-window-TAG, output
# .../ar/run-TAG (must not exist). Optionally waits until no process matches WAIT_PATTERN first.
# Then: wait for /tmp/gpu-window.ready, run_experiment, touch /tmp/gpu-window.release.
set -uo pipefail
export DOCKER_HOST=unix:///run/user/1000/docker.sock
T=$1; I=$2; WAITP=${3:-}; shift $(( $# < 3 ? $# : 3 ))
S=/mnt/ssd/storage/ai/qwen3.8-27b/exl3-serving-2
OUT=$S/ar/run-$T
[[ -e $OUT ]] && { echo "$OUT exists"; exit 2; }
# the pattern must stay absent for 30 s (back-to-back build queues leave only short gaps)
if [[ -n $WAITP ]]; then
  while :; do
    while pgrep -f "$WAITP" >/dev/null; do sleep 10; done
    sleep 30
    pgrep -f "$WAITP" >/dev/null || break
  done
fi
limit=$(nvidia-smi --query-gpu=power.limit --format=csv,noheader,nounits | awk '{printf "%.0f", $1}')
declared=$(python3 -c 'import re, sys; t = open(sys.argv[1]).read(); m = re.findall(r"^POWER_LIMIT_WATTS = ([0-9]+)\.0$", t, re.M); print(m[0]) if len(m) == 1 else sys.exit("cannot read POWER_LIMIT_WATTS from " + sys.argv[1])' /home/gilrodrigues/Repos/elpis/bench/exl3.py) || exit 3
[[ $limit == "$declared" ]] || { echo "power limit $limit W != declared $declared W (bench/exl3.py)"; exit 3; }
echo "$T image $I $(date +%T)"
python3 /tmp/mkcand.py serve "qwen-exl3-ar-$T" "$I" "ar-window-$T" "$@" || { echo "mkcand failed"; exit 1; }
bash /tmp/gpu-window.sh serve "qwen-exl3-ar-$T" "$I" "ar-window-$T" 2700 "$OUT"
