#!/usr/bin/env bash
set -euo pipefail

cd /app
export PATH=/app/venv/bin:$PATH
export HF_HUB_DISABLE_TELEMETRY=1

base_revision=1f05c441c4e64ae0549de44fa9ea5a6d43610314
fast_revision=124c14e7e8c7d2f5402933b9af368e772a9fcf0c
dflash_revision=4d30ec736ffc6b8688dc2ae2b502d9b48bdec279
marker=/app/models/.prepared-revisions
expected="image=8d832f8758ae4fd36c29a15d3c45888922bc4377
base=$base_revision
fast=$fast_revision
dflash=$dflash_revision"

if [[ -f "$marker" ]] && [[ "$(cat "$marker")" == "$expected" ]]; then
  echo "Pinned Qwen model set is already prepared."
  exit 0
fi
if [[ -e "$marker" ]]; then
  echo "Refusing to mutate a Qwen model set prepared from different revisions." >&2
  exit 1
fi

base=/app/models/Qwen3.8-27B-W4A16-AutoRound
hf download dbirks/Qwen3.8-27B-W4A16-AutoRound \
  --revision "$base_revision" --local-dir "$base"

python - "$fast_revision" "$dflash_revision" <<'PY'
from pathlib import Path
import sys

fast_revision, dflash_revision = sys.argv[1:]
replacements = {
    Path("prepare/fetch_fast_variant.py"): (
        'snapshot_download("syvai/qwen3.8-27b-3090-fast-variant",',
        f'snapshot_download("syvai/qwen3.8-27b-3090-fast-variant", revision="{fast_revision}",',
    ),
    Path("prepare/fetch_dflash2.py"): (
        "snapshot_download(REPO, local_dir=D,",
        f'snapshot_download(REPO, revision=None if BF16 else "{dflash_revision}", local_dir=D,',
    ),
}
for path, (old, new) in replacements.items():
    text = path.read_text()
    if text.count(old) != 1:
        raise SystemExit(f"expected one pinned-download patch point in {path}")
    path.write_text(text.replace(old, new))
PY

HF_REPO=dbirks/Qwen3.8-27B-W4A16-AutoRound \
  FAST_VARIANT=1 DFLASH2=1 bash docker/prepare.sh
for required in \
  /app/models/Qwen3.8-27B-W4A16-AutoRound-fast/model.safetensors.index.json \
  /app/models/Qwen3.8-27B-DFlash2-W4A16/model.safetensors; do
  [[ -s "$required" ]] || {
    printf 'required prepared model artifact is missing: %s\n' "$required" >&2
    exit 1
  }
done
printf '%s\n' "$expected" >"$marker.tmp"
mv "$marker.tmp" "$marker"
