#!/usr/bin/env bash
# CPU-only image build. Never pull or retag the existing native EXL3 base.
#   baseline  - installed engine unchanged
#   candidate - baseline + the sha-pinned patches/exl3 series and proven acceptance artifact
set -euo pipefail
umask 077
if (( $# != 2 )) || [[ "$1" != baseline && "$1" != candidate ]]; then
  echo "Usage: bash docker/build-exl3.sh <baseline|candidate> <output-image-tag>" >&2
  exit 1
fi
variant="$1"
image="$2"
base=qwen-litos:exl3-native-comparison
expected=sha256:b35314f48c7684b4c9cf3d59f4c21395316aa1fc0925db782f460005aa2602ff
root="$(realpath -- "$(dirname -- "${BASH_SOURCE[0]}")/..")"
existing_id="$(docker image ls --no-trunc --format '{{.ID}}' --filter "reference=$image")"
if [[ "$existing_id" == "$expected" ]]; then
  echo "Refusing to overwrite a tag of the immutable native base image." >&2
  exit 1
fi

check_base() {
  local actual
  actual="$(docker image inspect --format '{{.Id}}' "$base")"
  if [[ "$actual" != "$expected" ]]; then
    echo "Refusing EXL3 build: existing local base image differs from the pinned ID." >&2
    exit 1
  fi
}

label() {
  docker image inspect --format "{{ index .Config.Labels \"$2\" }}" "$1"
}

patches_sha=""
build_args=()
if [[ "$variant" == candidate ]]; then
  patches_sha="$(sha256sum -- "$root/patches/exl3/exl3-patches.json")"
  patches_sha="${patches_sha%% *}"
  build_args=(--build-arg "EXL3_PATCHES_SHA256=$patches_sha")
  # Proof gate, emitted C, library and admission, all from the pinned flake toolchain;
  # the image build then re-verifies every output against the manifest pins.
  rm -rf -- "$root/build/bend-exl3"
  (cd -- "$root" && nix develop --offline --no-write-lock-file -c \
    python3 -B bend/exl3_build.py --output build/bend-exl3)
fi

# Use the daemon-backed default builder, not an independently selected remote one.
# Require exclusive operator control of image tags throughout this build; the
# before/after checks detect ordinary retagging, not a hostile Docker operator.
check_base
scratch="$(mktemp -d)"
trap 'rm -f -- "$scratch/image-id"; rmdir -- "$scratch"' EXIT
DOCKER_BUILDKIT=1 docker build --builder default --pull=false \
  --file "$root/Dockerfile.exl3" --target "$variant" "${build_args[@]}" \
  --iidfile "$scratch/image-id" "$root"
check_base
built_id="$(< "$scratch/image-id")"
if [[ ! "$built_id" =~ ^sha256:[0-9a-f]{64}$ ||
      "$(label "$built_id" io.litos.exl3.base-image-id)" != "$expected" ||
      "$(label "$built_id" io.litos.exl3.variant)" != "$variant" ||
      "$(label "$built_id" io.litos.exl3.patches-sha256)" != "$patches_sha" ]]; then
  echo "Refusing EXL3 build: missing output identity or baked provenance." >&2
  exit 1
fi
# Publish the local tag only after both base checks and build succeed.
docker image tag "$built_id" "$image"
printf 'Built %s %s as %s from authenticated local base %s\n' \
  "$variant" "$built_id" "$image" "$expected"
