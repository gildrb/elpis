# Explicit build-only source artifact. Not imported by serving configuration.
{ pkgs }:
pkgs.runCommand "qwen-unqualified-38-file-source-overlay" {
  nativeBuildInputs = [ pkgs.python313 ];
} ''
  mkdir -p "$out"
  python3 ${../patches/chain.py} \
    --bundle ${../patches} \
    --manifest-sha256 b8bb8e83b57dbdb01acf121bf640b2447c9cd3bf13849198d02b8aef443396a2 \
    --image lmsysorg/sglang@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9 \
    --exclusive-build-tree --mode overlay --root "$out/source"
  mkdir -p "$out/provenance"
  cp ${../patches/qualification/manifest.json} "$out/provenance/manifest.json"
  printf '%s  manifest.json\n' b8bb8e83b57dbdb01acf121bf640b2447c9cd3bf13849198d02b8aef443396a2 > "$out/provenance/manifest.sha256"
  cp ${../patches/qualification/source-evidence.json} "$out/provenance/source-evidence.json"
  cp ${../patches/LICENSE.sglang} "$out/provenance/LICENSE.sglang"
''
