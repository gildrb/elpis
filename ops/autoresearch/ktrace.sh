#!/usr/bin/env bash
# usage: ktrace.sh TAG EVIDENCE_NAME   CUPTI kernel trace of qwen-inference:exl3-cand-TAG (timing-class
# window, exclusive compile lock) into .../evidence/EVIDENCE_NAME. Run it detached (/tmp/detach.sh).
set -uo pipefail
export DOCKER_HOST=unix:///run/user/1000/docker.sock
T=$1; N=$2
I=$(docker image inspect -f '{{.Id}}' "qwen-inference:exl3-cand-$T") || { echo "no image for $T"; exit 1; }
E=/mnt/ssd/storage/ai/qwen3.8-27b/exl3-serving-2/evidence/$N
[[ -e $E ]] && { echo "$E exists"; exit 2; }
mkdir -m 700 "$E"; cp /tmp/kernel-work/KernelTrace/kernel_trace.py "$E/"; chmod 444 "$E/kernel_trace.py"
TS=$(date +%H%M%S)
name=qwen-exl3-ktrace-$T-$TS win=ktrace-window-$T-$TS
python3 /tmp/mkcand.py run "$name" "$I" "$win" --cmd '["/opt/venv/bin/python","-I","-B","/kernel_trace.py","/out"]' \
  --mount "$E/kernel_trace.py:/kernel_trace.py:ro" --mount "$E:/out" >/dev/null || { echo "mkcand failed"; exit 1; }
echo "== ktrace $T $(date +%T)"
bash /tmp/gpu-window.sh run "$name" "$I" "$win" 2700 "$E/trace.log" | grep -e payload -e guardian -e refused
echo "KTRACE-$T-DONE $(date +%T)"
