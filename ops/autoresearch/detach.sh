#!/usr/bin/env bash
# usage: detach.sh LOG COMMAND...   run COMMAND in its own session (immune to the caller's timeout /
# process-group kill), stdout+stderr to LOG, then append "DETACHED-EXIT rc=<rc> <time>" to LOG.
set -euo pipefail
LOG=$1; shift
: > "$LOG"
setsid nohup bash -c '"$@"; rc=$?; echo "DETACHED-EXIT rc=$rc $(date +%T)"' _ "$@" >> "$LOG" 2>&1 < /dev/null &
echo "detached pid $! -> $LOG"
