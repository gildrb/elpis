#!/usr/bin/env bash
# usage: stack-check.sh NAME [EXL3_DIR|-] PATCH...   pin committed series + PATCH... in a scratch copy
# (optional exl3 series dir replaces patches/exl3 series + manifest + adds its patch files)
set -uo pipefail
R=/home/gilrodrigues/Repos/eta
NAME=$1; EXL3=$2; shift 2
D=/tmp/stackcheck/$NAME
rm -rf "$D"; mkdir -p "$D"
git -C "$R" archive HEAD patches | tar -x -C "$D"
X=$D/patches/exl3-ext
for p in "$@"; do
  b=$(basename "$p"); cp -- "$p" "$X/$b"
  printf '%s  %s\n' "$(sha256sum "$X/$b" | cut -d' ' -f1)" "$b" >> "$X/series"
done
if [[ $EXL3 != - ]]; then
  cp -- "$EXL3"/*.patch "$D/patches/exl3/"; cp -- "$EXL3/series" "$EXL3/exl3-patches.json" "$D/patches/exl3/"
fi
if out=$(python3 -I -B "$X/ext.py" pin /tmp/eta-exl3-baseline-1/exllamav3/exllamav3 2>&1); then
  echo "$NAME: OK $(echo "$out" | tail -1 | cut -c1-120)"
else
  echo "$NAME: FAIL $(echo "$out" | tail -2 | tr '\n' ' ' | cut -c1-300)"
fi
