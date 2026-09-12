#!/usr/bin/env bash
set -euo pipefail

PORT="${PORT:-18020}"
MODELS="${MODELS_DIR:-/models}"
SERVED_MODEL_NAME="${SERVED_MODEL_NAME:-qwen3.8-27b}"
API_KEY_FILE="${API_KEY_FILE:-/app/api_key.txt}"
PREPARE="${PREPARE:-0}"
INFERENCE_PROFILE="${INFERENCE_PROFILE:-awq}"
case "$PREPARE" in
  0 | 1) ;;
  *) echo "[entrypoint] PREPARE must be 0 or 1." >&2; exit 1 ;;
esac
AWQ="${MODELS}/Qwen3.8-27B-AWQ-INT4"
AWQ_REPO=cyankiwi/Qwen3.8-27B-AWQ-INT4
AWQ_REVISION=63768c10df38c0395e12ef49edac1bd539eaeeea

export HF_HUB_DISABLE_TELEMETRY=1
export DO_NOT_TRACK=1
export HOME="${HOME:-/cache}"
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
# Bound full-vocabulary input-logprob temporary allocations in both profiles.
export SGLANG_ENABLE_LOGPROB_CHUNK=1
export SGLANG_LOGPROB_CHUNK_SIZE=256

download_pinned_model() {
  local repository=$1
  local revision=$2
  local model_dir=$3
  local required_file=$4
  local revision_file="${model_dir}/.inference-index-revision"
  local expected_revision="${repository}@${revision}"

  if [[ -f $required_file && -f $revision_file && $(<"$revision_file") == "$expected_revision" ]]; then
    echo "[entrypoint] using pinned cache $expected_revision"
    return
  fi

  echo "[entrypoint] downloading pinned model $expected_revision"
  mkdir -p "$model_dir"
  python3 - "$repository" "$revision" "$model_dir" "$required_file" <<'PY'
from pathlib import Path
import sys
from huggingface_hub import snapshot_download

repository, revision, model_dir, required_file = sys.argv[1:]
snapshot_download(repo_id=repository, revision=revision, local_dir=model_dir)
required = Path(required_file)
if not required.is_file() or required.stat().st_size == 0:
    raise SystemExit(f"required model file is missing after download: {required_file}")
PY
  printf '%s\n' "$expected_revision" >"${revision_file}.tmp"
  mv "${revision_file}.tmp" "$revision_file"
}

speculative_args=()
case "$INFERENCE_PROFILE" in
  awq)
    download_pinned_model "$AWQ_REPO" "$AWQ_REVISION" "$AWQ" "$AWQ/model.safetensors.index.json"
    model_path="$AWQ"
    ;;
  compact-dflash)
    model_path="${MODELS}/compact-target-rholsc8k/artifact"
    draft_path="${MODELS}/Qwen3.8-27B-DFlash2-W4A16"
    # No download, conversion, stamp, or fallback for qualified local artifacts.
    python3 /model-preparation/verify-models.py --target "$model_path" --draft "$draft_path"
    speculative_args=(
      --attention-backend flashinfer
      --speculative-algorithm DFLASH
      --speculative-draft-model-path "$draft_path"
      --speculative-draft-attention-backend flashinfer
      --speculative-dflash-block-size 8
      --speculative-draft-window-size 2048
    )
    ;;
  *)
    echo "[entrypoint] unsupported inference profile: $INFERENCE_PROFILE" >&2
    exit 1
    ;;
esac

if [[ "$PREPARE" == "1" ]]; then
  echo "[entrypoint] pinned SGLang model set is prepared."
  exit 0
fi

if [[ ! -s "$API_KEY_FILE" ]]; then
  echo "[entrypoint] API key file is missing: $API_KEY_FILE" >&2
  exit 1
fi
api_key="$(tr -d '\n' <"$API_KEY_FILE")"
if [[ -z "$api_key" ]]; then
  echo "[entrypoint] API key file is empty: $API_KEY_FILE" >&2
  exit 1
fi

echo "[entrypoint] launching sglang on port $PORT as $SERVED_MODEL_NAME"
exec python3 -m sglang.launch_server \
  --model-path "$model_path" \
  --served-model-name "$SERVED_MODEL_NAME" \
  --tp 1 \
  --context-length 24576 \
  "${speculative_args[@]}" \
  --max-running-requests 1 \
  --chunked-prefill-size 4096 \
  --mamba-radix-cache-strategy extra_buffer \
  --mem-fraction-static 0.89 \
  --max-mamba-cache-size 8 \
  --mamba-ssm-dtype bfloat16 \
  --kv-cache-dtype fp8_e4m3 \
  --disable-prefill-cuda-graph \
  --cuda-graph-max-bs 8 \
  --reasoning-parser qwen3 \
  --tool-call-parser qwen3_coder \
  --enable-metrics \
  --api-key "$api_key" \
  --host 0.0.0.0 \
  --port "$PORT"
