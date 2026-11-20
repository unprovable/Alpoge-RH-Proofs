#!/usr/bin/env bash
# Build the RH Lean project on a Linux server and collect audit data.
#
# Usage, from the repository root (run inside tmux or screen; the build takes about a day):
#   bash audit/run-build.sh            # build, then run audit/Audit.lean
#   bash audit/run-build.sh audit      # only the audit (after a successful build)
#   bash audit/run-build.sh check      # independent kernel re-check with leanchecker (long, single-threaded)
#   JOBS=16 bash audit/run-build.sh    # cap parallel Lean processes (use this if you hit out-of-memory)
#   VERBOSE=1 bash audit/run-build.sh  # also stream every built module to the terminal
#
# A progress line (modules done, rough time remaining, RAM in use) is printed every 5 minutes
# (PROGRESS_EVERY=<seconds> to change). To watch a run from another terminal:
#   tail -f audit-results/*/build.log
#
# The build is incremental: re-running resumes where it stopped.
# Results land in audit-results/<UTC timestamp>/ (small text files, safe to commit and push).
set -uo pipefail

PHASE="${1:-all}"
REPO="$(cd "$(dirname "$0")/.." && pwd)"
RUN_ID="$(date -u +%Y%m%dT%H%M%SZ)-$PHASE"
OUT="$REPO/audit-results/$RUN_ID"
mkdir -p "$OUT"
cd "$REPO/lean"

log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a "$OUT/run.log"; }

# --- toolchain -----------------------------------------------------------------------------
if ! command -v lake >/dev/null 2>&1; then
  if [ ! -x "$HOME/.elan/bin/elan" ]; then
    log "installing elan"
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
  fi
  export PATH="$HOME/.elan/bin:$PATH"
fi

{
  echo "date: $(date -u)"; uname -a; echo "cpus: $(nproc)"; free -g; df -h "$REPO"
  echo "git: $(git -C "$REPO" rev-parse HEAD 2>/dev/null)"
  lean --version; lake --version
} > "$OUT/machine.txt" 2>&1
FREE_GB=$(df -BG --output=avail "$REPO" | tail -1 | tr -dc 0-9)
MEM_GB=$(free -g | awk '/^Mem:/ {print $2}')
[ "${FREE_GB:-0}" -lt 200 ] && log "WARNING: only ${FREE_GB} GB free disk; the build output may need well over 100 GB"
[ "${MEM_GB:-0}" -lt 64 ] && log "WARNING: only ${MEM_GB} GB RAM; consider JOBS=8"

JOBS="${JOBS:-$(nproc)}"
export LEAN_NUM_THREADS="$JOBS"   # caps how many Lean processes Lake runs at once (tested on v4.33.1)

# --- build ---------------------------------------------------------------------------------
hm() { printf '%dh%02dm' $(($1 / 3600)) $(($1 % 3600 / 60)); }

# Every PROGRESS_EVERY seconds: Lake's latest [done/total] counter, a rough time remaining
# (from the average rate so far), and RAM in use.
progress_monitor() {
  local start n total el eta last ram
  start=$(date +%s)
  while sleep "${PROGRESS_EVERY:-300}"; do
    last=$(tail -n 300 "$OUT/build.log" 2>/dev/null | grep -oE '\[[0-9]+/[0-9]+\]' | tail -1 | tr -d '[]')
    [ -z "$last" ] && continue
    n=${last%/*}; total=${last#*/}
    el=$(( $(date +%s) - start ))
    eta="?"; [ "$n" -gt 0 ] && eta=$(hm $(( el * (total - n) / n )))
    ram=$(free -g | awk '/^Mem:/ {print $3 "/" $2 " GB"}')
    log "progress $n/$total ($(( 100 * n / total ))%), elapsed $(hm "$el"), ~$eta remaining (rough), RAM $ram"
  done
}

run_build() {
  log "fetching Mathlib's prebuilt cache"
  lake exe cache get 2>&1 | tee "$OUT/cache-get.log" | tail -3

  log "starting memory sampler (every 20s)"
  (
    echo -e "unix_time\trss_kb\telapsed_s\tfile"
    while true; do
      ps -C lean -o rss=,etimes=,args= --sort=-rss 2>/dev/null | head -n 40 | while read -r rss et args; do
        f=$(echo "$args" | tr ' ' '\n' | grep -m1 '\.lean$')
        echo -e "$(date +%s)\t$rss\t$et\t${f#"$REPO/lean/src/"}"
      done
      sleep 20
    done
  ) > "$OUT/mem-samples.tsv" &
  SAMPLER=$!

  touch "$OUT/build.log"
  progress_monitor &
  PROGRESS=$!

  log "lake build with $JOBS parallel jobs"
  if [ -x /usr/bin/time ]; then TIMER=(/usr/bin/time -v -o "$OUT/build-time.txt"); else TIMER=(); fi
  if [ "${VERBOSE:-0}" = 1 ]; then
    "${TIMER[@]}" lake build -v 2>&1 | grep --line-buffered -v '^trace: ' | tee "$OUT/build.log"
    BUILD_RC=${PIPESTATUS[0]}
  else
    "${TIMER[@]}" lake build -v 2>&1 | grep --line-buffered -v '^trace: ' > "$OUT/build.log"
    BUILD_RC=${PIPESTATUS[0]}
  fi
  kill "$SAMPLER" "$PROGRESS" 2>/dev/null
  echo "$BUILD_RC" > "$OUT/build-exit-code.txt"
  log "lake build exited with code $BUILD_RC"
  summarize
  return "$BUILD_RC"
}

summarize() {
  grep -nE '^(✖|error)|exit code|signal|Killed' "$OUT/build.log" > "$OUT/failures.txt"
  log "$(wc -l < "$OUT/failures.txt") failure/error lines (see failures.txt)"
  command -v python3 >/dev/null || { log "python3 not found; skipping summary"; return; }
  python3 -I - "$OUT" <<'PY'
import os, re, sys, collections
out = sys.argv[1]
def secs(t):
    total = 0.0
    for num, unit in re.findall(r'([\d.]+)\s*(ms|s|m|h)', t):
        total += float(num) * {'ms': 1e-3, 's': 1, 'm': 60, 'h': 3600}[unit]
    return total
built = []
progress = None
for line in open(os.path.join(out, 'build.log'), encoding='utf-8', errors='replace'):
    m = re.search(r'\[(\d+)/(\d+)\] Built (\S+) \(([^)]*)\)', line)
    if m:
        built.append((secs(m.group(4)), m.group(3)))
        progress = (int(m.group(1)), int(m.group(2)))
built.sort(reverse=True)
with open(os.path.join(out, 'timings.tsv'), 'w') as f:
    f.write('seconds\tmodule\n')
    for s, mod in built: f.write(f'{s:.1f}\t{mod}\n')
peak = collections.defaultdict(int)
try:
    for line in open(os.path.join(out, 'mem-samples.tsv')):
        p = line.rstrip('\n').split('\t')
        if len(p) == 4 and p[1].isdigit(): peak[p[3]] = max(peak[p[3]], int(p[1]))
except FileNotFoundError: pass
with open(os.path.join(out, 'summary.txt'), 'w') as f:
    f.write(f'modules built this run: {len(built)}\n')
    if progress: f.write(f'last progress counter: {progress[0]}/{progress[1]}\n')
    f.write(f'total CPU-seconds in built modules: {sum(s for s, _ in built):.0f}\n\n')
    f.write('slowest 40 modules:\n')
    for s, mod in built[:40]: f.write(f'  {s:9.1f}s  {mod}\n')
    f.write('\nlargest peak memory (sampled every 20s), top 40:\n')
    for fn, kb in sorted(peak.items(), key=lambda x: -x[1])[:40]:
        f.write(f'  {kb/1048576:7.2f} GB  {fn}\n')
PY
  log "wrote summary.txt and timings.tsv"
}

# --- audit ---------------------------------------------------------------------------------
run_audit() {
  log "running audit/Audit.lean (loads the whole project; needs ~20-40 GB RAM)"
  RH_AUDIT_OUT="$OUT" lake env lean "$REPO/audit/Audit.lean" > "$OUT/audit.log" 2>&1
  local rc=$?
  log "audit exited with code $rc"
  grep -h '^\[audit\]' "$OUT/audit.log" | tee -a "$OUT/run.log"
  return $rc
}

# --- independent re-check ---------------------------------------------------------------------
run_check() {
  local checker
  checker="$(lean --print-prefix)/bin/leanchecker"
  log "leanchecker --fresh Main: replays every declaration (Mathlib + project) through the kernel"
  if [ -x /usr/bin/time ]; then TIMER=(/usr/bin/time -v -o "$OUT/check-time.txt"); else TIMER=(); fi
  "${TIMER[@]}" lake env "$checker" --fresh Main > "$OUT/leanchecker.log" 2>&1
  local rc=$?
  echo "$rc" > "$OUT/leanchecker-exit-code.txt"
  log "leanchecker exited with code $rc"
  return $rc
}

case "$PHASE" in
  all)   run_build && run_audit ;;
  build) run_build ;;
  audit) run_audit ;;
  check) run_check ;;
  *) echo "unknown phase: $PHASE (use all, build, audit or check)"; exit 2 ;;
esac
RC=$?

gzip -f "$OUT"/build.log "$OUT"/mem-samples.tsv 2>/dev/null
log "done (exit $RC). Results: $OUT"
log "To publish: git add audit-results && git commit -m 'Audit results $RUN_ID' && git push"
exit $RC
