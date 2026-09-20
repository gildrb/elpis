#!/usr/bin/env bash
set -euo pipefail

# ONE model path: Qwen3.8-27B W4 weights with packed W8 embeddings +
# SGLang + DFlash2 speculative decoding + KVarN packed KV, TP=1, one RTX 3090.
# The optional A8 target-body backend is an explicit approximate experiment.

# Refuse legacy architecture selectors: the target family, representation and
# speculative algorithm no longer have runtime switches. Any value (even the
# old default) means the launcher was written for the retired multi-path
# deployment and must be rewritten, not silently honored.
for legacy in QWEN_MODEL_FAMILY QWEN_MODEL_REPRESENTATION QWEN_SPEC_ALGORITHM QWEN_DSPARK_DRAFT; do
  if [[ -n "${!legacy:-}" ]]; then
    echo "Refusing retired architecture selector ${legacy} (one fixed path: packed Qwen3.8 + DFlash2)." >&2
    exit 1
  fi
done
case "${SGLANG_EXPERIMENTAL_PACKED_W8_EMBEDDING:-1}" in
  1) export SGLANG_EXPERIMENTAL_PACKED_W8_EMBEDDING=1 ;;
  *) echo "The packed Qwen target requires the packed W8 embedding loader." >&2; exit 1 ;;
esac

QWEN_MARLIN_ACTIVATION_BITS="${QWEN_MARLIN_ACTIVATION_BITS-16}"
case "$QWEN_MARLIN_ACTIVATION_BITS" in
  16 | 8) export QWEN_MARLIN_ACTIVATION_BITS ;;
  *) echo "QWEN_MARLIN_ACTIVATION_BITS must be exactly 16 or 8." >&2; exit 1 ;;
esac
if [[ "$QWEN_MARLIN_ACTIVATION_BITS" == 8 ]]; then
  echo "EXPERIMENTAL W4A8 target-body precision; head, embeddings and DFlash2 remain unchanged. Quality and performance are unqualified." >&2
fi

PORT=18020
MODELS=/models
API_KEY_FILE=/app/api_key.txt
# The verifier authenticates the original packed target and unchanged draft.
MODEL_PATH="${MODELS}/compact-target-rholsc8k/packed"
DRAFT_PATH="${MODELS}/Qwen3.8-27B-DFlash2-W4A16"
SERVED_MODEL_NAME=qwen3.8-27b

if [[ "$(cat /opt/qwen/patch-series)" != "experimental" ]]; then
  echo "The production path requires the pinned experimental patch series (packed Qwen + KVarN)." >&2
  exit 1
fi

context="${QWEN_QUALIFICATION_CONTEXT:-262144}"
case "$context" in
  262144) ;;
  *) echo "The Bend-backed production plan requires native context262144." >&2; exit 1 ;;
esac
pool=$((context + 1024))
# Execute the compiled Bend planner once, not on the token path. Its emitted
# pool/page geometry drives the actual engine arguments; native allocation and
# capture guards still validate the resulting backed resources independently.
bend_geometry="$(python3 - "$context" "$pool" <<'PY'
import sys
from pathlib import Path

from bend.adapter import checked_plan

plan = checked_plan(Path("/opt/qwen/bend"), int(sys.argv[1]), int(sys.argv[2]), 128)
print(plan["pool"], plan["page_size"], plan["pages"])
PY
)"
read -r pool page_size physical_pages <<< "$bend_geometry"
echo "[entrypoint] Bend native plan: context=${context} pool=${pool} page_size=${page_size} physical_pages=${physical_pages}"
# Historical native-capacity candidate; allocation and quality remain unqualified.
mem_fraction="${QWEN_MEM_FRACTION_STATIC:-0.98}"
case "$mem_fraction" in
  0.94 | 0.95 | 0.96 | 0.97 | 0.98) ;;
  *) echo "Unsupported static memory fraction; choose 0.94..0.98 in 0.01 steps." >&2; exit 1 ;;
esac

if [[ "${QWEN_ALLOW_UNQUALIFIED:-0}" != "1" ]]; then
  echo "This unqualified candidate requires QWEN_ALLOW_UNQUALIFIED=1." >&2
  exit 1
fi
echo "UNQUALIFIED ${context}-token packed Qwen3.8 candidate: capacity and quality are not established." >&2

# Packed embeddings require DFlash; do not expose an unsupported target-only arm.
case "${QWEN_QUALIFICATION:-speculative}" in
  speculative) ;;
  target-only) echo "Packed embeddings require DFLASH; target-only is source-blocked." >&2; exit 1 ;;
  *) echo "Unknown qualification control." >&2; exit 1 ;;
esac

commit_graph=0
case "${QWEN_COMMIT_GRAPH:-1}" in
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
    if [[ "${QWEN_QUALIFICATION_EXECUTION:-default}" == default ]]; then
      kvarn_mode=graph
      graph_args=(--cuda-graph-backend-decode full --cuda-graph-bs-decode 1
        --cuda-graph-backend-prefill disabled)
    fi
    if [[ "$commit_graph" == 1 ]]; then
      if [[ "$kvarn_mode" != graph ]]; then
        echo "The commit graph requires CUDA-graph execution (default)." >&2
        exit 1
      fi
      qualification_args+=(--kvarn-commit-graph)
    fi
    qualification_args+=(--page-size "$page_size" --kvarn-qualification-mode "$kvarn_mode"
      --speculative-draft-kv-cache-dtype kvarn_k4v2_g128)
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

# DFlash2 restriction: authenticate the ordered input against the independent
# pinned mtp_draft_vocab_ids.pt int64-le storage before its Boolean mask conversion.
if [[ "${QWEN_DRAFT_VOCAB_JSON:-}" != /state/draft_vocab_ids.json ||
      ! -f "$QWEN_DRAFT_VOCAB_JSON" || -L "$QWEN_DRAFT_VOCAB_JSON" ]]; then
  echo "Mount the pinned regular draft-vocabulary file at its canonical container path." >&2
  exit 1
fi
python3 - <<'PY'
import hashlib
import json
import math
import os
import struct
import sys

try:
    simulated = float(os.environ.get("SGLANG_SIMULATE_ACC_LEN", "-1"))
except ValueError as error:
    raise SystemExit("SGLANG_SIMULATE_ACC_LEN must be a finite disabled value.") from error
if not math.isfinite(simulated) or simulated > 0:
    raise SystemExit("Production qualification forbids simulated DFLASH acceptance.")

try:
    with open("/state/draft_vocab_ids.json", "rb") as source:
        data = source.read(1024 * 1024 + 1)
    if len(data) > 1024 * 1024:
        raise ValueError
    ids = json.loads(data)
    if (
        not isinstance(ids, list)
        or len(ids) != 40960
        or any(type(token) is not int or not 0 <= token < 248320 for token in ids)
        or len(set(ids)) != 40960
    ):
        raise ValueError
    # Independent reference: fast-variant revision124c14e7e8c7d2f5402933b9af368e772a9fcf0c,
    # mtp_draft_vocab_ids.pt SHA2568af9028616e41932e0c949cd5364d2da0a69d15375af9bb404cab1e4d723f581.
    # Authenticated CPU int64[40960], storage offset0/stride1, little endian.
    if hashlib.sha256(struct.pack("<40960q", *ids)).hexdigest() != (
        "328af76c651b989efb40e31e6b1bfdb1b4a0928e1124359f8fb04654b1e44584"
    ):
        raise ValueError("Ordered draft vocabulary differs from the pinned model input")
except (OSError, ValueError, TypeError, RecursionError):
    print("Draft vocabulary must match the pinned 40960 ordered target token IDs.", file=sys.stderr)
    sys.exit(1)
PY

# Authenticate the exact target and draft bytes before anything loads.
python3 /model-preparation/verify-models.py \
  --target "$MODEL_PATH" --draft "$DRAFT_PATH" --representation packed

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

# Both target and draft are the exact authenticated safetensors checkpoints.
speculative_args=(
  --speculative-algorithm DFLASH
  --speculative-draft-model-path "$DRAFT_PATH"
  --speculative-draft-load-format safetensors
  --speculative-draft-attention-backend "$draft_backend"
  --speculative-dflash-block-size 8
  --speculative-draft-window-size 2048
)

echo "[entrypoint] launching sglang on port $PORT as $SERVED_MODEL_NAME (packed Qwen3.8 + DFlash2)"
exec python3 -m sglang.launch_server \
  --model-path "$MODEL_PATH" \
  --load-format safetensors \
  --dtype bfloat16 \
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
