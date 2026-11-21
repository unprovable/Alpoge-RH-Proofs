#!/usr/bin/env bash
# Kernel re-check of every project module with leanchecker, one process per module, in parallel.
#
# Usage, from the repository root, after a successful build (run inside tmux):
#   bash audit/check-modules.sh            # JOBS=24 parallel checks by default
#   JOBS=16 bash audit/check-modules.sh
#
# `leanchecker M` loads M's imports and replays every declaration of M through the kernel, so
# checking every module re-checks every declaration in the project. Mathlib itself is not re-checked
# (use `bash audit/run-build.sh check`, i.e. `leanchecker --fresh Main`, for that; it is single-threaded).
#
# Resumable: results accumulate in audit-results/modcheck/, and modules already listed in ok.tsv
# are skipped on a re-run.
#   ok.tsv        module <tab> seconds
#   failed.txt    modules whose check failed;  failures.txt  their output (first 60 lines each)
#   run.log       progress every PROGRESS_EVERY seconds (default 300)
set -uo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$REPO/audit-results/modcheck"
mkdir -p "$OUT"
cd "$REPO/lean"
[ -d "$HOME/.elan/bin" ] && export PATH="$HOME/.elan/bin:$PATH"

log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$OUT/run.log"; }

LEAN_SYSROOT="$(lean --print-prefix)"
LEAN_PATH="$(lake env printenv LEAN_PATH)"
CHECKER="$LEAN_SYSROOT/bin/leanchecker"
PATH="$LEAN_SYSROOT/bin:$PATH"
export LEAN_SYSROOT LEAN_PATH CHECKER OUT PATH
JOBS="${JOBS:-24}"

# Every project module that was built (Mathlib's .olean files live under .lake/packages/).
find .lake/build/lib/lean -name '*.olean' \
  | sed -e 's|^\.lake/build/lib/lean/||' -e 's|\.olean$||' -e 's|/|.|g' | sort > "$OUT/modules.txt"
touch "$OUT/ok.tsv" "$OUT/failed.txt" "$OUT/failures.txt"
cut -f1 "$OUT/ok.tsv" | sort > "$OUT/.done"
comm -23 "$OUT/modules.txt" "$OUT/.done" > "$OUT/todo.txt"
TOTAL=$(wc -l < "$OUT/modules.txt" | tr -d ' ')
TODO=$(wc -l < "$OUT/todo.txt" | tr -d ' ')
{ echo "date: $(date -u)"; echo "git: $(git -C "$REPO" rev-parse HEAD 2>/dev/null)"; lean --version; } >> "$OUT/run.log"
log "$TOTAL project modules, $TODO still to check, $JOBS at a time"
: > "$OUT/failed.txt"   # failures are re-tried on a re-run

now_us() { if [ -n "${EPOCHREALTIME:-}" ]; then echo "${EPOCHREALTIME/./}"; else echo $(( $(date +%s) * 1000000 )); fi; }
check_one() {
  local m=$1 t0 t1 out rc
  t0=$(now_us)
  out=$("$CHECKER" "$m" 2>&1); rc=$?
  t1=$(now_us)
  if [ "$rc" -eq 0 ]; then
    printf '%s\t%d.%d\n' "$m" $(( (t1 - t0) / 1000000 )) $(( (t1 - t0) / 100000 % 10 )) >> "$OUT/ok.tsv"
  else
    printf '%s\n' "$m" >> "$OUT/failed.txt"
    printf '=== %s (exit %d)\n%s\n\n' "$m" "$rc" "$(printf '%s\n' "$out" | head -n 60)" >> "$OUT/failures.txt"
  fi
}
export -f check_one now_us

start=$(date +%s); base=$(wc -l < "$OUT/ok.tsv" | tr -d " ")
( while sleep "${PROGRESS_EVERY:-300}"; do
    ok=$(wc -l < "$OUT/ok.tsv" | tr -d " "); bad=$(wc -l < "$OUT/failed.txt" | tr -d " "); el=$(( $(date +%s) - start ))
    n=$(( ok - base + bad )); eta="?"
    [ "$n" -gt 0 ] && eta="$(( el * (TODO - n) / n / 3600 ))h$(( el * (TODO - n) / n % 3600 / 60 ))m"
    log "checked $ok/$TOTAL ok, $bad failed; ~$eta remaining (rough); RAM $(free -g | awk '/^Mem:/ {print $3 "/" $2 " GB"}')"
  done ) &
MON=$!

xargs -P "$JOBS" -n 1 bash -c 'check_one "$1"' _ < "$OUT/todo.txt"
kill "$MON" 2>/dev/null; wait "$MON" 2>/dev/null

ok=$(wc -l < "$OUT/ok.tsv" | tr -d " "); bad=$(wc -l < "$OUT/failed.txt" | tr -d " ")
log "finished: $ok/$TOTAL modules passed, $bad failed (see failed.txt and failures.txt)"
[ "$bad" -eq 0 ] && [ "$ok" -eq "$TOTAL" ]
