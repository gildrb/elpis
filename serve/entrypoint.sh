#!/usr/bin/env bash
set -euo pipefail

PORT="${PORT:-18020}"
MODELS="${MODELS_DIR:-/models}"
SERVED_MODEL_NAME="${SERVED_MODEL_NAME:-qwen3.8-27b}"
API_KEY_FILE="${API_KEY_FILE:-/app/api_key.txt}"
PREPARE="${PREPARE:-0}"
case "$PREPARE" in
  0 | 1) ;;
  *) echo "[entrypoint] PREPARE must be 0 or 1." >&2; exit 1 ;;
esac

export HF_HUB_DISABLE_TELEMETRY=1
export DO_NOT_TRACK=1
export HOME="${HOME:-/cache}"
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
# Bound the singleton NCCL communicator used by structured-output sampling.
export NCCL_MAX_CTAS=1
# Bound full-vocabulary input-logprob temporary allocations.
export SGLANG_ENABLE_LOGPROB_CHUNK=1
export SGLANG_LOGPROB_CHUNK_SIZE=256

model_path="${MODELS}/compact-target-rholsc8k/artifact"
draft_path="${MODELS}/Qwen3.8-27B-DFlash2-W4A16"
# No download, conversion, stamp, or fallback for qualified local artifacts.
python3 /model-preparation/verify-models.py --target "$model_path" --draft "$draft_path"

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
  --context-length 65536 \
  --max-total-tokens 66560 \
  --attention-backend flashinfer \
  --speculative-algorithm DFLASH \
  --speculative-draft-model-path "$draft_path" \
  --speculative-draft-attention-backend flashinfer \
  --speculative-dflash-block-size 8 \
  --speculative-draft-window-size 2048 \
  --max-running-requests 1 \
  --sleep-on-idle \
  --chunked-prefill-size 1024 \
  --mamba-radix-cache-strategy extra_buffer \
  --mem-fraction-static 0.94 \
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
