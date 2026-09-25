#!/usr/bin/env bash
# CPU-only image build. Never pull or retag the existing native EXL3 base.
#   baseline          - installed engine unchanged
#   candidate         - baseline + the sha-pinned patches/exl3 series and proven acceptance artifact
#   candidate-rebuilt - candidate + exllamav3_ext recompiled from the unpatched pinned sources
#   candidate-ext     - candidate + exllamav3_ext recompiled with the patches/exl3-ext series
set -euo pipefail
umask 077
variants=(baseline candidate candidate-rebuilt candidate-ext)
if (( $# != 2 )) || [[ ! " ${variants[*]} " == *" $1 "* ]]; then
  echo "Usage: bash docker/build-exl3.sh <${variants[*]// /|}> <output-image-tag>" >&2
  exit 1
fi
variant="$1"
image="$2"
base=qwen-eta:exl3-native-comparison
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

build() {
  DOCKER_BUILDKIT=1 docker build --builder default --pull=false \
    --file "$root/Dockerfile.exl3" "${build_args[@]}" "$@" "$root"
}

patches_sha=""
build_args=()
if [[ "$variant" != baseline ]]; then
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
trap 'rm -rf -- "$scratch"' EXIT
if [[ "$variant" == candidate-rebuilt || "$variant" == candidate-ext ]]; then
  # Both phases read the patch tools from one snapshot (named build context
  # `patches`), so concurrent repository edits cannot split them. Phase one
  # compiles the extension and exports the engine manifest composed around the
  # built shared object; its SHA-256 becomes the final image's label, and the
  # final stage recomposes the manifest from the installed object.
  snap="$scratch/patches"
  mkdir -p -- "$snap/exl3" "$snap/exl3-ext/upstream-355c6ee"
  shopt -s nullglob
  cp -- "$root"/patches/exl3/{series,exl3-patches.json,apply.py} "$root"/patches/exl3/*.patch \
    "$snap/exl3/"
  cp -- "$root"/patches/exl3-ext/{series,exl3-ext.json,ext.py} "$root"/patches/exl3-ext/*.patch \
    "$snap/exl3-ext/"
  shopt -u nullglob
  cp -- "$root/patches/exl3-ext/upstream-355c6ee/setup.py" "$snap/exl3-ext/upstream-355c6ee/"
  build_args+=(--build-context "patches=$snap")
  kind=rebuilt
  [[ "$variant" == candidate-ext ]] && kind=patched
  build --target "ext-$kind-manifest" --output "type=local,dest=$scratch/manifest"
  patches_sha="$(sha256sum -- "$scratch/manifest/exl3-patches.json")"
  patches_sha="${patches_sha%% *}"
  build_args+=(--build-arg "EXL3_ENGINE_MANIFEST_SHA256=$patches_sha")
fi
build --target "$variant" --iidfile "$scratch/image-id"
check_base
built_id="$(< "$scratch/image-id")"
if [[ ! "$built_id" =~ ^sha256:[0-9a-f]{64}$ ||
      "$(label "$built_id" io.eta.exl3.base-image-id)" != "$expected" ||
      "$(label "$built_id" io.eta.exl3.variant)" != "$variant" ||
      "$(label "$built_id" io.eta.exl3.patches-sha256)" != "$patches_sha" ]]; then
  echo "Refusing EXL3 build: missing output identity or baked provenance." >&2
  exit 1
fi
# Publish the local tag only after both base checks and build succeed.
docker image tag "$built_id" "$image"
printf 'Built %s %s as %s from authenticated local base %s\n' \
  "$variant" "$built_id" "$image" "$expected"
