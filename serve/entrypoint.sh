#!/usr/bin/env bash
set -euo pipefail

# Fixed API identity; the host port is mapped by Compose.
PORT=18020
MODELS=/models
SERVED_MODEL_NAME=qwen3.8-27b
API_KEY_FILE=/app/api_key.txt
# The single deployment objective is a candidate, not a measured capacity claim.
context="${QWEN_QUALIFICATION_CONTEXT:-262144}"
case "$context" in
  131072 | 163840 | 196608 | 229376 | 245760 | 262144) ;;
  *) echo "Unknown qualification context rung." >&2; exit 1 ;;
esac
pool=$((context + 1024))
mem_fraction="${QWEN_MEM_FRACTION_STATIC:-0.94}"
case "$mem_fraction" in
  0.94 | 0.95 | 0.96 | 0.97 | 0.98) ;;
  *) echo "Unsupported static memory fraction; choose 0.94..0.98 in 0.01 steps." >&2; exit 1 ;;
esac
speculation=1
if [[ "${QWEN_ALLOW_UNQUALIFIED:-0}" != "1" ]]; then
  echo "This unqualified candidate requires QWEN_ALLOW_UNQUALIFIED=1." >&2
  exit 1
fi
case "${QWEN_QUALIFICATION:-speculative}" in
  speculative) ;;
  target-only) speculation=0 ;;
  *) echo "Unknown qualification control." >&2; exit 1 ;;
esac
attention_backend=flashinfer
draft_backend=flashinfer
graph_args=(--cuda-graph-max-bs 8)
qualification_args=()
case "${QWEN_QUALIFICATION_EXECUTION:-default}" in
  default) ;;
  eager)
    graph_args=(--disable-cuda-graph)
    qualification_args=(--disable-overlap-schedule --disable-flashinfer-autotune)
    ;;
  *) echo "Unknown qualification execution control." >&2; exit 1 ;;
esac
case "${QWEN_QUALIFICATION_KV:-fp8}" in
  fp8) kv_dtype=fp8_e4m3 ;;
  bf16) kv_dtype=bfloat16 ;;
  kvarn)
    if [[ "$(cat /opt/qwen/patch-series)" != "experimental" ]]; then
      echo "KVarN requires an explicitly built experimental image." >&2
      exit 1
    fi
    if [[ "$speculation" != "1" ||
          "${QWEN_QUALIFICATION_EXECUTION:-default}" != "eager" ]]; then
      echo "KVarN requires speculative/eager; target-only is source-blocked." >&2
      exit 1
    fi
    kv_dtype=kvarn_k4v2_g128
    attention_backend=kvarn
    draft_backend=kvarn_draft
    qualification_args+=(--page-size 128 --kvarn-qualification-mode native
      --speculative-draft-kv-cache-dtype kvarn_k4v2_g128)
    echo "EXPERIMENTAL KVarN: same BF16-embedding artifacts; no startup or quality claim." >&2
    ;;
  *) echo "Unknown or unsupported qualification KV control." >&2; exit 1 ;;
esac
echo "UNQUALIFIED ${context}-token candidate: capacity and quality are not established." >&2

export HF_HUB_DISABLE_TELEMETRY=1
export DO_NOT_TRACK=1
export HOME="${HOME:-/cache}"
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
# Bound the singleton NCCL communicator used by structured-output sampling.
export NCCL_MAX_CTAS=1
# Bound full-vocabulary input-logprob temporary allocations.
export SGLANG_ENABLE_LOGPROB_CHUNK=1
export SGLANG_LOGPROB_CHUNK_SIZE=256

representation="${QWEN_MODEL_REPRESENTATION:-dense}"
representation_args=()
case "$representation" in
  dense)
    # Fail closed on a contradictory inherited loader selection.
    case "${SGLANG_EXPERIMENTAL_PACKED_W8_EMBEDDING:-}" in
      "" | 0) unset SGLANG_EXPERIMENTAL_PACKED_W8_EMBEDDING ;;
      *) echo "Dense representation rejects an inherited packed-loader flag." >&2; exit 1 ;;
    esac
    model_path="${MODELS}/compact-target-rholsc8k/artifact"
    ;;
  packed)
    if [[ "$(cat /opt/qwen/patch-series)" != "experimental" ]]; then
      echo "Packed embeddings require an explicitly built experimental image." >&2
      exit 1
    fi
    if (( speculation != 1 )); then
      echo "Packed embeddings require DFLASH; target-only is source-blocked." >&2
      exit 1
    fi
    export SGLANG_EXPERIMENTAL_PACKED_W8_EMBEDDING=1
    representation_args=(--load-format safetensors --dtype bfloat16)
    model_path="${MODELS}/compact-target-rholsc8k/packed"
    echo "EXPERIMENTAL packed embeddings: no runtime or quality qualification claim." >&2
    ;;
  *) echo "Unknown model representation; no fallback is permitted." >&2; exit 1 ;;
esac
draft_path="${MODELS}/Qwen3.8-27B-DFlash2-W4A16"
# No download, conversion, stamp, or fallback for supplied local artifacts.
python3 /model-preparation/verify-models.py --target "$model_path" --draft "$draft_path" \
  --representation "$representation"

# Validate the private credential size and reject whitespace/control characters.
if [[ ! -f "$API_KEY_FILE" || -L "$API_KEY_FILE" ]]; then
  echo "API key must be a regular file." >&2
  exit 1
fi
key_bytes="$(wc -c < "$API_KEY_FILE")"
if (( key_bytes == 0 || key_bytes > 4096 )); then
  echo "API key must contain 1..4096 bytes." >&2
  exit 1
fi
# The sentinel preserves trailing newlines so only one optional newline is removed.
export LC_ALL=C
api_key="$(cat "$API_KEY_FILE"; printf '.')"
api_key="${api_key%.}"
if (( ${#api_key} != key_bytes )); then
  echo "API key contains an unsupported byte." >&2
  exit 1
fi
api_key="${api_key%$'\n'}"
if [[ ! "$api_key" =~ ^[!-~]+$ ]]; then
  echo "API key must be printable ASCII without whitespace." >&2
  exit 1
fi
speculative_args=()
if (( speculation == 1 )); then
  speculative_args=(
    --speculative-algorithm DFLASH
    --speculative-draft-model-path "$draft_path"
    --speculative-draft-attention-backend "$draft_backend"
    --speculative-dflash-block-size 8
    --speculative-draft-window-size 2048
  )
fi

echo "[entrypoint] launching sglang on port $PORT as $SERVED_MODEL_NAME"
exec python3 -m sglang.launch_server \
  --model-path "$model_path" \
  "${representation_args[@]}" \
  --served-model-name "$SERVED_MODEL_NAME" \
  --tp 1 \
  --context-length "$context" \
  --max-total-tokens "$pool" \
  --attention-backend "$attention_backend" \
  "${speculative_args[@]}" \
  --max-running-requests 1 \
  --sleep-on-idle \
  --chunked-prefill-size 1024 \
  --mamba-radix-cache-strategy extra_buffer \
  --mem-fraction-static "$mem_fraction" \
  --max-mamba-cache-size 8 \
  --mamba-ssm-dtype bfloat16 \
  --kv-cache-dtype "$kv_dtype" \
  --disable-prefill-cuda-graph \
  "${graph_args[@]}" \
  "${qualification_args[@]}" \
  --reasoning-parser qwen3 \
  --tool-call-parser qwen3_coder \
  --enable-metrics \
  --api-key "$api_key" \
  --host 0.0.0.0 \
  --port "$PORT"
