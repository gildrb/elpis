#!/usr/bin/env bash
set -euo pipefail

# ONE production path: native Ternary-Bonsai-2-27B (PQ2_0 GGUF) target +
# SGLang + DFlash2 speculative decoding + KVarN packed KV, TP=1, one RTX 3090.
# The architecture is fixed here and in the pinned build. It is not selectable.

# Refuse legacy architecture selectors: the target family, representation and
# speculative algorithm no longer have runtime switches. Any value (even the
# old default) means the launcher was written for the retired multi-path
# deployment and must be rewritten, not silently honored.
for legacy in QWEN_MODEL_FAMILY QWEN_MODEL_REPRESENTATION QWEN_SPEC_ALGORITHM QWEN_DSPARK_DRAFT SGLANG_EXPERIMENTAL_PACKED_W8_EMBEDDING; do
  if [[ -n "${!legacy:-}" ]]; then
    echo "Refusing retired architecture selector ${legacy} (one fixed path: Bonsai PQ2_0 + DFlash2)." >&2
    exit 1
  fi
done

PORT=18020
MODELS=/models
API_KEY_FILE=/app/api_key.txt
# The wrapper pins config, tokenizer and the exact GGUF payload identity.
MODEL_PATH="${MODELS}/bonsai-pq2-wrapper"
DRAFT_PATH="${MODELS}/Qwen3.8-27B-DFlash2-W4A16"
SERVED_MODEL_NAME=qwen3.8-27b

if [[ "$(cat /opt/qwen/patch-series)" != "experimental" ]]; then
  echo "The production path requires the pinned experimental patch series (KVarN + PQ2)." >&2
  exit 1
fi

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

if [[ "${QWEN_ALLOW_UNQUALIFIED:-0}" != "1" ]]; then
  echo "This unqualified candidate requires QWEN_ALLOW_UNQUALIFIED=1." >&2
  exit 1
fi
echo "UNQUALIFIED ${context}-token Bonsai PQ2_0 candidate: capacity and quality are not established." >&2

# Speculation: DFlash2 is the only algorithm. target-only is an explicit
# qualification control (diagnostic target execution without the draft).
speculation=1
case "${QWEN_QUALIFICATION:-speculative}" in
  speculative) ;;
  target-only) speculation=0 ;;
  *) echo "Unknown qualification control." >&2; exit 1 ;;
esac

commit_graph=0
case "${QWEN_COMMIT_GRAPH:-0}" in
  0) ;;
  1) commit_graph=1 ;;
  *) echo "Unknown commit-graph control." >&2; exit 1 ;;
esac

attention_backend=flashinfer
draft_backend=flashinfer
graph_args=(--cuda-graph-max-bs 8)
qualification_args=()
serialized=0
case "${QWEN_QUALIFICATION_EXECUTION:-default}" in
  default) ;;
  eager)
    graph_args=(--disable-cuda-graph)
    serialized=1
    qualification_args=(--disable-overlap-schedule --disable-flashinfer-autotune)
    ;;
  *) echo "Unknown qualification execution control." >&2; exit 1 ;;
esac
case "${QWEN_QUALIFICATION_KV:-kvarn}" in
  kvarn)
    kv_dtype=kvarn_k4v2_g128
    attention_backend=kvarn
    draft_backend=kvarn_draft
    # Every KVarN qualification mode is serialized and autotune-free.
    if [[ "$serialized" != 1 ]]; then
      qualification_args+=(--disable-overlap-schedule --disable-flashinfer-autotune)
    fi
    kvarn_mode=native
    if [[ "$commit_graph" == 1 ]]; then
      if [[ "${QWEN_QUALIFICATION_EXECUTION:-default}" != default ]]; then
        echo "The commit graph requires CUDA-graph execution (default)." >&2
        exit 1
      fi
      kvarn_mode=graph
      graph_args=(--cuda-graph-backend-decode full --cuda-graph-bs-decode 1
        --cuda-graph-backend-prefill disabled)
      qualification_args+=(--kvarn-commit-graph)
    elif [[ "${QWEN_QUALIFICATION_EXECUTION:-default}" == default ]]; then
      echo "KVarN requires QWEN_QUALIFICATION_EXECUTION=eager or QWEN_COMMIT_GRAPH=1." >&2
      exit 1
    fi
    qualification_args+=(--page-size 128 --kvarn-qualification-mode "$kvarn_mode"
      --speculative-draft-kv-cache-dtype kvarn_k4v2_g128)
    if [[ "$speculation" != "1" ]]; then
      echo "KVarN requires speculative; target-only is source-blocked." >&2
      exit 1
    fi
    ;;
  bf16) kv_dtype=bfloat16 ;;
  fp8) kv_dtype=fp8_e4m3 ;;
  *) echo "Unknown or unsupported qualification KV control." >&2; exit 1 ;;
esac
if [[ "$commit_graph" == 1 && "$attention_backend" != kvarn ]]; then
  echo "The commit graph requires KV=kvarn." >&2
  exit 1
fi

export HF_HUB_DISABLE_TELEMETRY=1
export DO_NOT_TRACK=1
export HOME="${HOME:-/cache}"
export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True
# Bound the singleton NCCL communicator used by structured-output sampling.
export NCCL_MAX_CTAS=1
# Bound full-vocabulary input-logprob temporary allocations.
export SGLANG_ENABLE_LOGPROB_CHUNK=1
export SGLANG_LOGPROB_CHUNK_SIZE=256

# DFlash2 draft-vocabulary restriction (syv-ai 40960-id list). The tuned
# acceptance profile depends on it; serving refuses to start without the pin.
if [[ "$speculation" == "1" ]]; then
  if [[ -z "${QWEN_DRAFT_VOCAB_JSON:-}" || ! -f "$QWEN_DRAFT_VOCAB_JSON" ]]; then
    echo "QWEN_DRAFT_VOCAB_JSON must point at the pinned draft-vocabulary file." >&2
    exit 1
  fi
fi

# Authenticate the exact target and draft bytes before anything loads.
python3 /model-preparation/verify-models.py \
  --target "$MODEL_PATH" --draft "$DRAFT_PATH" --representation gguf

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
  # The target is GGUF; the draft stays a safetensors checkpoint.
  speculative_args=(
    --speculative-algorithm DFLASH
    --speculative-draft-model-path "$DRAFT_PATH"
    --speculative-draft-load-format auto
    --speculative-draft-attention-backend "$draft_backend"
    --speculative-dflash-block-size 8
    --speculative-draft-window-size 2048
  )
fi

echo "[entrypoint] launching sglang on port $PORT as $SERVED_MODEL_NAME (Bonsai PQ2_0 + DFlash2)"
exec python3 -m sglang.launch_server \
  --model-path "$MODEL_PATH" \
  --quantization gguf \
  --load-format gguf \
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
  --stream-interval 4 \
  --reasoning-parser qwen3 \
  --tool-call-parser qwen3_coder \
  --enable-metrics \
  --api-key "$api_key" \
  --host 0.0.0.0 \
  --port "$PORT"
