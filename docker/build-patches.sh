#!/usr/bin/env bash
set -euo pipefail
# The immutable stock image supplies this exact upstream Git checkout.
# Explicit upstream and experimental sets are qualification build inputs.
if [[ $# -gt 1 ]]; then
  printf 'Usage: %s [upstream|baseline|experimental]\n' "$0" >&2
  exit 2
fi
exec bash /opt/qwen/patches/apply.sh /sgl-workspace/sglang "${1:-baseline}"
