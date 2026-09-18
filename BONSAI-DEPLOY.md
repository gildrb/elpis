# Bonsai 2 + DSpark Deployment Guide

## 1. Download model files

```bash
# Bonsai 2 PQ2_0 GGUF (target model)
cd /srv/ai/models/qwen3.8-27b
huggingface-cli download prism-ml/Ternary-Bonsai-2-27B-gguf \
    --local-dir /tmp/bonsai-dl \
    --include "Ternary-Bonsai-2-27B-PQ2_0.gguf"
cp /tmp/bonsai-dl/Ternary-Bonsai-2-27B-PQ2_0.gguf /models/

# DSpark draft model (for speculative decoding)
huggingface-cli download deepseek-ai/dspark_qwen3_14b_block7 \
    --local-dir /models/dspark-qwen3-14b
```

## 2. Adapt DSpark draft to Qwen3.8 vocab

```bash
docker compose run --rm inference \
    python3 /opt/qwen/serve/adapt_dspark_draft.py \
    /models/dspark-qwen3-14b \
    /models/dspark-qwen3.8-adapted
```

## 3. Convert Bonsai GGUF to W4A16 (optional, for compatibility)

```bash
docker compose run --rm inference \
    python3 /opt/qwen/serve/convert-bonsai-to-w4a16.py \
    /models/Ternary-Bonsai-2-27B-PQ2_0.gguf \
    /models/bonsai-w4a16
```

## 4. Launch with Bonsai + DSpark

```bash
# Native PQ2_0 path (7.2GB weights, fastest decode)
export QWEN_MODEL_FAMILY=bonsai
export QWEN_MODEL_REPRESENTATION=gguf
export QWEN_SPEC_ALGORITHM=DSPARK
export QWEN_DSPARK_DRAFT=/models/dspark-qwen3.8-adapted
export QWEN_ALLOW_UNQUALIFIED=1
docker compose up -d

# or W4A16 path (16GB, best compatibility)
export QWEN_MODEL_FAMILY=bonsai
export QWEN_MODEL_REPRESENTATION=w4a16
export QWEN_SPEC_ALGORITHM=DFLASH  # DSPARK also works
export QWEN_ALLOW_UNQUALIFIED=1
docker compose up -d
```

## 5. Benchmark

```bash
python3 bench/decode.py --port 18020 --key "$(cat /srv/ai/models/qwen3.8-27b/api-key)" --depth 1024 --output-tokens 1024
```

## Expected performance

With native PQ2_0 (7.2GB) + DSpark:
- Memory bandwidth: 936 GB/s / 7.2 GB = **130 raw tok/s**
- DSpark acceptance rate ~1.5-2x → **~195-260 tok/s effective**

With W4A16 (16GB) + DSpark:
- Memory bandwidth: 936 / 16 = **58 raw tok/s**
- DSpark acceptance rate ~3-4x → **~170-230 tok/s effective**

## File inventory

| File | Purpose |
|------|---------|
| `serve/convert-bonsai-to-w4a16.py` | GPU converter: PQ2_0 → W4A16 |
| `serve/adapt_dspark_draft.py` | Extend DSpark draft vocab to 248K |
| `serve/bonsai_bootstrap.py` | Runtime PQ2_0 patch (for gguf path) |
| `bend/dequant_pq2.bend` | PQ2_0 dequant CUDA kernel (Bend) |
| `bend/gather.bend` | KVarN gather CUDA kernel (Bend) |
| `bend/LAWS.bend` | Performance targets: 170/140/100 tok/s |