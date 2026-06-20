#!/usr/bin/env bash
# Baseline runner: run freqhorn (default --v4) over bench_horn, record pass/fail/timeout.
set -u
ROOT="/home/daniel/Projects/aeval"
BIN="$ROOT/build/tools/deep/freqhorn"
BENCH="$ROOT/bench_horn"
OUT="${1:-$ROOT/docs/bv-project/benchmarks/baseline-results.csv}"
TO_S="${2:-30}"          # per-file wall timeout (seconds)
JOBS="${3:-6}"           # parallelism

echo "file,status,seconds" > "$OUT"

run_one() {
  local f="$1" to="$2" out="$3"
  local base; base="$(basename "$f")"
  local start end dur rc result
  start=$(date +%s.%N)
  output="$(timeout "${to}s" "$BIN" "$f" 2>&1)"
  rc=$?
  end=$(date +%s.%N)
  dur=$(awk "BEGIN{printf \"%.1f\", $end-$start}")
  if [ $rc -eq 124 ]; then
    result="timeout"
  elif echo "$output" | grep -q "Success"; then
    result="success"
  elif [ $rc -ne 0 ]; then
    result="error_rc$rc"
  else
    result="nosolve"
  fi
  echo "$base,$result,$dur" >> "$out"
}
export -f run_one
export BIN

ls "$BENCH"/*.smt2 | xargs -P "$JOBS" -I {} bash -c 'run_one "$@"' _ {} "$TO_S" "$OUT"

echo "=== DONE ==="
echo "Total: $(($(wc -l < "$OUT")-1))"
sort -t, -k2 "$OUT" | awk -F, 'NR>1{c[$2]++} END{for(k in c) print k": "c[k]}'
