#!/usr/bin/env bash
# Kernel re-check of every project module with leanchecker, in parallel.
#
# Usage, from the repository root, after a successful build (run inside tmux):
#   bash audit/check-modules.sh
#
# `leanchecker Lib` checks every module whose name starts with `Lib`: for each one it loads that
# module's imports and replays the module's own declarations through the kernel, running the
# modules as parallel tasks inside one process. Checking every top-level library therefore
# re-checks every declaration in the project. Mathlib itself is not re-checked (`bash
# audit/run-build.sh check`, i.e. `leanchecker --fresh Main`, does that, on one core).
#
# One leanchecker process per library, smallest first. A failing library is recorded and the
# others still run. Resumable: libraries that already passed are skipped on a re-run.
# Results in audit-results/leanchecker-modules/:
#   <Lib>.log            leanchecker's output ("replaying <module>" per module, errors at the end)
#   passed.txt / failed.txt   libraries
#   run.log              progress every PROGRESS_EVERY seconds (default 300)
set -uo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$REPO/audit-results/leanchecker-modules"
mkdir -p "$OUT"
cd "$REPO/lean"
[ -d "$HOME/.elan/bin" ] && export PATH="$HOME/.elan/bin:$PATH"

log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$OUT/run.log"; }

LEAN_SYSROOT="$(lean --print-prefix)"
LEAN_PATH="$(lake env printenv LEAN_PATH)"
CHECKER="$LEAN_SYSROOT/bin/leanchecker"
PATH="$LEAN_SYSROOT/bin:$PATH"
export LEAN_SYSROOT LEAN_PATH PATH
LINEBUF=(); command -v stdbuf >/dev/null && LINEBUF=(stdbuf -oL)

find .lake/build/lib/lean -name '*.olean' \
  | sed -e 's|^\.lake/build/lib/lean/||' -e 's|\.olean$||' -e 's|/|.|g' | sort > "$OUT/modules.txt"
TOTAL=$(wc -l < "$OUT/modules.txt" | tr -d ' ')
touch "$OUT/passed.txt"
: > "$OUT/failed.txt"
{ echo "date: $(date -u)"; echo "git: $(git -C "$REPO" rev-parse HEAD 2>/dev/null)"; lean --version; } >> "$OUT/run.log"

# Top-level libraries, smallest first.
LIBS=$(cut -d. -f1 "$OUT/modules.txt" | sort | uniq -c | sort -n | awk '{print $2}')
DONE=0
for lib in $LIBS; do
  n=$(grep -c "^$lib\(\.\|$\)" "$OUT/modules.txt")
  if grep -qx "$lib" "$OUT/passed.txt"; then DONE=$((DONE + n)); continue; fi
  log "checking $lib ($n modules; $DONE/$TOTAL done before it)"
  start=$(date +%s)
  ( while sleep "${PROGRESS_EVERY:-300}"; do
      k=$(grep -c '^replaying ' "$OUT/$lib.log" 2>/dev/null); k=$(( k > 0 ? k - 1 : 0 ))
      el=$(( $(date +%s) - start )); eta="?"
      [ "$k" -gt 0 ] && eta="$(( el * (n - k) / k / 3600 ))h$(( el * (n - k) / k % 3600 / 60 ))m"
      log "  $lib: $k/$n modules checked, ~$eta left for $lib (rough); RAM $(free -g 2>/dev/null | awk '/^Mem:/ {print $3 "/" $2 " GB"}')"
    done ) &
  MON=$!
  "${LINEBUF[@]}" "$CHECKER" --verbose "$lib" > "$OUT/$lib.log" 2>&1
  rc=$?
  kill "$MON" 2>/dev/null; wait "$MON" 2>/dev/null
  if [ "$rc" -eq 0 ]; then
    echo "$lib" >> "$OUT/passed.txt"
    log "$lib passed ($(( ($(date +%s) - start) / 60 )) min)"
  else
    echo "$lib" >> "$OUT/failed.txt"
    log "$lib FAILED (exit $rc): $(grep -m1 'found a problem' "$OUT/$lib.log")"
  fi
  DONE=$((DONE + n))
done

log "finished: passed: $(tr '\n' ' ' < "$OUT/passed.txt"); failed: $(tr '\n' ' ' < "$OUT/failed.txt")"
[ ! -s "$OUT/failed.txt" ]
