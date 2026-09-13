#!/usr/bin/env bash
# Apply only to an exclusively owned disposable upstream build checkout.
set -euo pipefail
if [[ $# -ne 2 ]]; then
  printf 'Usage: %s UPSTREAM_CHECKOUT upstream|baseline|experimental\n' "$0" >&2
  exit 2
fi
bundle=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
root=$(cd -- "$1" && pwd -P)
case "$2" in
  upstream) series=() ;;
  baseline) series=(baseline.series) ;;
  experimental) series=(baseline.series experimental.series) ;;
  *) printf 'Unknown build patch set: %s\n' "$2" >&2; exit 2 ;;
esac
source "$bundle/source.env"
if [[ ! "$SGLANG_REVISION" =~ ^[0-9a-f]{40}$ ]]; then
  printf 'Invalid upstream revision\n' >&2
  exit 1
fi
if [[ "$(git -C "$root" rev-parse --show-toplevel)" != "$root" ||
      "$(git -C "$root" rev-parse HEAD)" != "$SGLANG_REVISION" ]]; then
  printf 'Expected upstream checkout at %s\n' "$SGLANG_REVISION" >&2
  exit 1
fi
if [[ -n "$(git -C "$root" status --porcelain --untracked-files=all)" ]]; then
  printf 'Upstream build checkout must be clean\n' >&2
  exit 1
fi
patches=()
for list in "${series[@]}"; do
  while read -r digest patch extra; do
    if [[ ! "$digest" =~ ^[0-9a-f]{64}$ ||
          ! "$patch" =~ ^[a-zA-Z0-9_-]+[.]patch$ || -n "$extra" ]]; then
      printf 'Invalid patch series entry in %s\n' "$list" >&2
      exit 1
    fi
    patches+=("$bundle/$patch")
  done < "$bundle/$list"
  (cd -- "$bundle" && sha256sum --check --strict "$list")
done
if [[ ${#patches[@]} -eq 0 && "$2" != "upstream" ]]; then
  printf 'Empty patch series\n' >&2
  exit 1
fi
for patch in "${patches[@]}"; do
  git -C "$root" apply --check --index "$patch"
  git -C "$root" apply --index "$patch"
done
printf 'Applied %s patches to upstream %s (%s build only)\n' \
  "${#patches[@]}" "$SGLANG_REVISION" "$2"
