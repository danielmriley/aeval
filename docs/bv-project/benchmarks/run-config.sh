#!/usr/bin/env bash
# Run freqhorn over bench_horn with a given flag set; record pass/fail/timeout.
# usage: run-config.sh <out.csv> <timeout_s> <jobs> [flags...]
set -u
ROOT="/home/daniel/Projects/aeval"
BIN="$ROOT/build/tools/deep/freqhorn"
BENCH="$ROOT/bench_horn"
OUT="$1"; TO_S="$2"; JOBS="$3"; shift 3
FLAGS="$*"

echo "file,status,seconds" > "$OUT"

run_one() {
  local f="$1" to="$2" out="$3" bin="$4"; shift 4
  local flags="$*"
  local base; base="$(basename "$f")"
  local start end dur rc output result
  start=$(date +%s.%N)
  output="$(timeout "${to}s" "$bin" $flags "$f" 2>&1)"
  rc=$?
  end=$(date +%s.%N)
  dur=$(awk "BEGIN{printf \"%.1f\", $end-$start}")
  if [ $rc -eq 124 ]; then result="timeout"
  elif echo "$output" | grep -q "Success"; then result="success"
  elif [ $rc -ne 0 ]; then result="error_rc$rc"
  else result="nosolve"; fi
  echo "$base,$result,$dur" >> "$out"
}
export -f run_one

ls "$BENCH"/*.smt2 | xargs -P "$JOBS" -I {} bash -c 'run_one "$@"' _ {} "$TO_S" "$OUT" "$BIN" $FLAGS

echo "=== DONE ($FLAGS) ==="
awk -F, 'NR>1{c[$2]++} END{for(k in c) print k": "c[k]}' "$OUT"
