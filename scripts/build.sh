#!/bin/bash
# Guarded `lake build`: at most one Lean process at a time, and every `lean` process whose own
# memory (footprint, the "Memory" column of Activity Monitor) exceeds LEAN_MEM_LIMIT_MB
# (default 1024) is killed and the build is aborted.
#
# Why not `lean -M`: it counts resident pages including the memory-mapped Mathlib .olean files
# (shared by all Lean processes), so already small files exceed 1 GB there.
#
# Usage: scripts/build.sh [lake build arguments...]   e.g. scripts/build.sh Pca.Flip
#        scripts/build.sh --lean FILE.lean             check one file (e.g. a #print axioms probe)
set -u
LIMIT_MB=${LEAN_MEM_LIMIT_MB:-1024}
cd "$(dirname "$0")/.." || exit 1

if [ "${1:-}" = "--lean" ]; then
  LEAN_NUM_THREADS=1 lake env lean "$2" &
else
  LEAN_NUM_THREADS=1 lake build "$@" &
fi
LAKE=$!
STATUS_FILE=$(mktemp)
echo 0 > "$STATUS_FILE"

to_mb() { # top's MEM column: 123K / 456M / 1.2G (possibly with a trailing + or -)
  awk -v v="$1" 'BEGIN { sub(/[+-]$/, "", v); u = substr(v, length(v)); x = substr(v, 1, length(v) - 1) + 0;
    if (u == "G") x *= 1024; else if (u == "K") x /= 1024; else if (u == "B") x /= 1048576; printf "%d", x }'
}

while kill -0 "$LAKE" 2>/dev/null; do
  PIDS=$(pgrep -P "$LAKE" -x lean)
  if [ -n "$PIDS" ]; then
    ARGS=()
    for p in $PIDS; do ARGS+=(-pid "$p"); done
    while read -r pid mem; do
      [ -z "$pid" ] && continue
      mb=$(to_mb "$mem")
      if [ "$mb" -gt "$LIMIT_MB" ]; then
        echo "build.sh: lean process $pid uses ${mb} MB > ${LIMIT_MB} MB, aborting:" >&2
        ps -o command= -p "$pid" | cut -c1-200 >&2
        kill "$pid" 2>/dev/null
        kill "$LAKE" 2>/dev/null
        echo 1 > "$STATUS_FILE"
      fi
    done < <(top -l 1 "${ARGS[@]}" -stats pid,mem 2>/dev/null | awk '/^[0-9]+ /{print $1, $2}')
  fi
  sleep 2
done
wait "$LAKE"
RC=$?
if [ "$(cat "$STATUS_FILE")" = 1 ]; then RC=137; fi
rm -f "$STATUS_FILE"
exit $RC
