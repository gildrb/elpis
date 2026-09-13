#!/usr/bin/env bash
set -euo pipefail
image='lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9'
root=/sgl-workspace/sglang/python/sglang/srt
patches=/opt/qwen/patches
# Check the actual stock image before saving or changing any source bytes.
python3 "$patches/verify.py" --manifest "$patches/manifest.json" --phase original --root "$root" --image "$image"
cd "$patches"
printf '%s\n' \
  '4142de575ae778793864eb964b55e30abd1ef601d2ebe0aecb88b8446154518f  packed-head-predicate.patch' \
  'f5dca6a51f996d39d30eb86df68fce3d1eb956e8879aa6fd65b11af20e5ca1e9  quant-aware-fc.patch' \
  'a9592305b414b0b4faefb93eeb306bd62579249990bb834cea926d0787289404  mamba-cache-prefix.patch' | sha256sum --check --strict
mkdir -p /sglang-original/{layers,models,speculative}
cp "$root/layers/logits_processor.py" /sglang-original/layers/
cp "$root/models/dflash.py" /sglang-original/models/
cp "$root/speculative/dflash_worker_v2.py" /sglang-original/speculative/
for name in packed-head-predicate quant-aware-fc mamba-cache-prefix; do
  patch --batch --forward --fuzz=0 --no-backup-if-mismatch -p4 -d "$root" <"$patches/$name.patch"
done
python3 "$patches/verify.py" --manifest "$patches/manifest.json" --phase original --root /sglang-original --image "$image"
python3 "$patches/verify.py" --manifest "$patches/manifest.json" --phase replacement --root "$root" --image "$image"
