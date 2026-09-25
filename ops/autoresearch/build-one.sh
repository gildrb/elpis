#!/usr/bin/env bash
# usage: [REPO_PATCH=file] build-one.sh NAME "ext patch files to append" "exl3 series+manifest dir or -"
#   Appends the given ext patch files (exact bytes) to the committed ext series, pins, optionally
#   swaps in an exl3 series/manifest dir with its patch files, builds candidate-ext, saves the
#   state to /tmp/variants/NAME/{ext,exl3}, and ALWAYS restores the repo to its committed state.
set -euo pipefail
export DOCKER_HOST=unix:///run/user/1000/docker.sock
NAME=$1; EXT_ADD=$2; EXL3_DIR=${3:--}
R=/home/gilrodrigues/Repos/eta; X=$R/patches/exl3-ext; P=$R/patches/exl3
cd "$R"
# Hold the compile lock shared for the whole build: waits for timing windows (which take it
# exclusively) and keeps them from starting mid-build; non-timing windows don't take it.
exec 7>/tmp/eta-gpu.lock
flock -s 7
# One build at a time: builds edit the repo's series files.
exec 6>/tmp/eta-build.lock
flock -x 6
added=()
replaced=()
repo_patched=0
restore() {
  if [[ $repo_patched == 1 ]]; then git apply -R -- "$REPO_PATCH" || echo "WARNING: could not revert $REPO_PATCH" >&2; fi
  git checkout -- patches/exl3-ext/series patches/exl3-ext/exl3-ext.json patches/exl3/series patches/exl3/exl3-patches.json
  for f in "${added[@]}"; do rm -f -- "$f"; done
  for f in "${replaced[@]}"; do mv -f -- "$f.build-one-orig" "$f"; done
}
trap restore EXIT
# Optional repo-level patch (e.g. Dockerfile/build infrastructure) applied only for this build.
REPO_PATCH=${REPO_PATCH:-}
if [[ -n $REPO_PATCH ]]; then git apply -- "$REPO_PATCH"; repo_patched=1; fi
# Use exactly the given patch file; a different same-named repo file is set aside and restored.
place() {  # src dst
  if [[ -e $2 ]]; then
    if ! cmp -s -- "$1" "$2"; then mv -- "$2" "$2.build-one-orig"; replaced+=("$2"); cp -- "$1" "$2"; fi
  else
    cp -- "$1" "$2"; added+=("$2")
  fi
}
for p in $EXT_ADD; do
  b=$(basename "$p")
  place "$p" "$X/$b"
  printf '%s  %s\n' "$(sha256sum "$X/$b" | cut -d' ' -f1)" "$b" >> "$X/series"
done
if [[ $EXL3_DIR != - ]]; then
  for f in "$EXL3_DIR"/*.patch; do place "$f" "$P/$(basename "$f")"; done
  cp -- "$EXL3_DIR/series" "$P/series"; cp -- "$EXL3_DIR/exl3-patches.json" "$P/exl3-patches.json"
fi
python3 -I -B "$X/ext.py" pin /tmp/eta-exl3-baseline-1/exllamav3/exllamav3
mkdir -p "/tmp/variants/$NAME/ext" "/tmp/variants/$NAME/exl3"
cp -- "$X/series" "$X/exl3-ext.json" "/tmp/variants/$NAME/ext/"
cp -- "$P/series" "$P/exl3-patches.json" "/tmp/variants/$NAME/exl3/"
for p in $EXT_ADD; do cp -- "$p" "/tmp/variants/$NAME/ext/"; done
if [[ $EXL3_DIR != - ]]; then cp -- "$EXL3_DIR"/*.patch "/tmp/variants/$NAME/exl3/"; fi
if [[ -n $REPO_PATCH ]]; then cp -- "$REPO_PATCH" "/tmp/variants/$NAME/"; fi
start=$SECONDS
bash docker/build-exl3.sh candidate-ext "qwen-inference:exl3-cand-$NAME" > "/tmp/variants/$NAME/build.log" 2>&1
echo "$NAME built in $((SECONDS-start))s: $(docker image inspect -f '{{.Id}}' "qwen-inference:exl3-cand-$NAME")"
