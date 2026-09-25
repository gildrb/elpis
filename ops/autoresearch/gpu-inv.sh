#!/usr/bin/env bash
# usage: gpu-inv.sh TAG IMAGE_ID [ARMS] [REF_TAG] [extra mkcand args...]
# Non-timing invariance run (parity-window): draft arms on the 15 parity cases; with REF_TAG, also
# compares normal-arm ids to out/run-REF_TAG (bit-exact candidates).
set -uo pipefail
export DOCKER_HOST=unix:///run/user/1000/docker.sock
T=$1; I=$2; ARMS=${3:-normal,cap,wrong0}; REF=${4:-}; shift $(( $# < 4 ? $# : 4 ))
V=/tmp/kernel-work/Invariance
P=/mnt/ssd/storage/ai/qwen3.8-27b/exl3-serving-2/evidence/parity-1
[[ -e $V/out/run-$T ]] && { echo "out/run-$T exists"; exit 2; }
TS=$(date +%H%M)
name=qwen-exl3-inv-run-$T-$TS win=parity-window-inv-run-$T-$TS
python3 /tmp/mkcand.py run "$name" "$I" "$win" \
  --cmd "[\"/opt/venv/bin/python\",\"-I\",\"-B\",\"/work/invariance.py\",\"run\",\"--arms\",\"$ARMS\",${NOPROBE:+\"--no-probe\",}\"--out\",\"/work/out/run-$T\"]" \
  --mount "$P:/parity:ro" --mount "$V:/work" "$@" >/dev/null || { echo "mkcand failed for $name"; exit 1; }
echo "== invariance run $T ($ARMS) $(date +%T)"
bash /tmp/gpu-window.sh run "$name" "$I" "$win" 2400 "$V/run-$T.log" | grep -e payload -e guardian
python3 -c "L=open('$V/run-$T.log').read().splitlines();print('\n'.join(L[-18:]))"
[[ -n $REF ]] && python3 /tmp/inv-compare.py "$V/out/run-$REF/result.json" "$V/out/run-$T/result.json"
echo "INV-$T-DONE $(date +%T)"
