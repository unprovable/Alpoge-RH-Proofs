#!/usr/bin/env bash
# Kernel re-check of every project module, in parallel.
#
# Usage, from the repository root, after a successful build (run inside tmux):
#   bash audit/check-modules.sh             # JOBS=28 processes by default
#   JOBS=16 bash audit/check-modules.sh
#
# Builds audit/checker (a small program running leanchecker's own per-module replay, see
# audit/checker/RHCheck.lean), splits the project's modules round-robin into JOBS lists and runs one
# checker process per list. Each module's imports are loaded and every declaration of the module is
# replayed through the kernel, so checking every module re-checks every declaration in the project.
# Mathlib itself is not re-checked (`bash audit/run-build.sh check`, i.e. `leanchecker --fresh Main`,
# does that, on one core).
#
# Resumable: modules that already passed (in any earlier run) are skipped.
# Results in audit-results/kernel-recheck/:
#   run.log                    progress every PROGRESS_EVERY seconds (default 300) and the summary
#   out/<run>-<n>.txt          per process: "start <m>", then "ok <m> <seconds>" or "FAIL <m> <error>"
#   passed.txt / failed.txt    modules;  crashed.txt  modules whose process died while checking them
set -uo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$REPO/audit-results/kernel-recheck"
RUN="$(date -u +%Y%m%dT%H%M%SZ)"
mkdir -p "$OUT/out" "$OUT/lists"
[ -d "$HOME/.elan/bin" ] && export PATH="$HOME/.elan/bin:$PATH"

log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$OUT/run.log"; }

log "building audit/checker"
( cd "$REPO/audit/checker" && lake build 2>&1 | tail -2 ) | tee -a "$OUT/run.log"
BIN="$REPO/audit/checker/.lake/build/bin/rhcheck"
[ -x "$BIN" ] || { log "checker did not build"; exit 1; }

cd "$REPO/lean"
LEAN_SYSROOT="$(lean --print-prefix)"
LEAN_PATH="$(lake env printenv LEAN_PATH)"
export LEAN_SYSROOT LEAN_PATH
JOBS="${JOBS:-28}"

find .lake/build/lib/lean -name '*.olean' \
  | sed -e 's|^\.lake/build/lib/lean/||' -e 's|\.olean$||' -e 's|/|.|g' | sort > "$OUT/modules.txt"
TOTAL=$(wc -l < "$OUT/modules.txt" | tr -d ' ')
cat "$OUT"/out/*.txt 2>/dev/null | awk -F'\t' '$1 == "ok" {print $2}' | sort -u > "$OUT/passed.txt"
comm -23 "$OUT/modules.txt" "$OUT/passed.txt" > "$OUT/todo.txt"
TODO=$(wc -l < "$OUT/todo.txt" | tr -d ' ')
{ echo "run $RUN: $(date -u)"; echo "git: $(git -C "$REPO" rev-parse HEAD 2>/dev/null)"; lean --version; } >> "$OUT/run.log"
log "$TOTAL project modules, $(wc -l < "$OUT/passed.txt" | tr -d ' ') already passed, $TODO to check with $JOBS processes"

rm -f "$OUT"/lists/*
awk -v n="$JOBS" -v d="$OUT/lists" '{ print > (d "/" (NR % n)) }' "$OUT/todo.txt"

finished() { cat "$OUT"/out/"$RUN"-*.txt 2>/dev/null | grep -cE '^(ok|FAIL)'; }
start=$(date +%s)
( while sleep "${PROGRESS_EVERY:-300}"; do
    k=$(finished); bad=$(cat "$OUT"/out/"$RUN"-*.txt 2>/dev/null | grep -c '^FAIL'); el=$(( $(date +%s) - start )); eta="?"
    [ "$k" -gt 0 ] && eta="$(( el * (TODO - k) / k / 3600 ))h$(( el * (TODO - k) / k % 3600 / 60 ))m"
    log "checked $k/$TODO this run ($bad failed), ~$eta remaining (rough); RAM $(free -g 2>/dev/null | awk '/^Mem:/ {print $3 "/" $2 " GB"}')"
  done ) &
MON=$!

for list in "$OUT"/lists/*; do
  "$BIN" --list "$list" > "$OUT/out/$RUN-$(basename "$list").txt" 2>&1 &
done
wait $(jobs -p | grep -vx "$MON")
kill "$MON" 2>/dev/null; wait "$MON" 2>/dev/null

cat "$OUT"/out/*.txt | awk -F'\t' '$1 == "ok" {print $2}' | sort -u > "$OUT/passed.txt"
cat "$OUT"/out/*.txt | awk -F'\t' '$1 == "FAIL" {print $2}' | sort -u > "$OUT/failed.txt"
# A process that died (e.g. out of memory) leaves "start <m>" as its last line.
for f in "$OUT"/out/"$RUN"-*.txt; do tail -n 1 "$f" | awk -F'\t' '$1 == "start" {print $2}'; done > "$OUT/crashed.txt"
log "finished: $(wc -l < "$OUT/passed.txt" | tr -d ' ')/$TOTAL modules passed, $(wc -l < "$OUT/failed.txt" | tr -d ' ') failed (failed.txt), $(wc -l < "$OUT/crashed.txt" | tr -d ' ') crashed (crashed.txt)"
[ ! -s "$OUT/failed.txt" ] && [ ! -s "$OUT/crashed.txt" ]
