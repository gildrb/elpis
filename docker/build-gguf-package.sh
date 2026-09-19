#!/usr/bin/env bash
set -euo pipefail
# Apply the pinned gguf-py extension (PQ2_0 type registration) to the
# site-packages copy inside the image. This is build-time integration: no
# runtime module patching happens anywhere in the serving path.
patch=/opt/qwen/patches/gguf-package/pq2-type-registration.patch
target=/opt/sglang/lib/python3.12/site-packages/gguf/constants.py

if grep -q "PQ2_0" "$target"; then
  echo "$target already contains PQ2_0; refusing a double application" >&2
  exit 1
fi

# Apply from the python3.12 tree root so the a/site-packages/... paths match.
cd /opt/sglang/lib/python3.12
git init -q
git apply --check "$patch"
git apply "$patch"
rm -rf .git

python3 - <<'PY'
from gguf.constants import GGMLQuantizationType, GGML_QUANT_SIZES
assert int(GGMLQuantizationType.PQ2_0) == 142
assert GGML_QUANT_SIZES[GGMLQuantizationType.PQ2_0] == (128, 34)
assert int(GGMLQuantizationType.TQ2_0) == 35
assert GGML_QUANT_SIZES[GGMLQuantizationType.TQ2_0] == (256, 66)
print("gguf-pq2 package extension verified: PQ2_0=142 (128,34), TQ2_0 unchanged")
PY
