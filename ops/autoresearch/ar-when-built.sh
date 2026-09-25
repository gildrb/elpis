#!/usr/bin/env bash
# usage: ar-when-built.sh TAG   wait for qwen-inference:exl3-cand-TAG, then open its timing serve window
# once no build-one.sh has run for 30 s (ar-serve.sh). Run it detached (/tmp/detach.sh).
set -uo pipefail
export DOCKER_HOST=unix:///run/user/1000/docker.sock
T=$1
while ! docker image inspect "qwen-inference:exl3-cand-$T" >/dev/null 2>&1; do sleep 10; done
I=$(docker image inspect -f '{{.Id}}' "qwen-inference:exl3-cand-$T")
bash /tmp/ar-serve.sh "$T" "$I" '[b]uild-one.sh'
