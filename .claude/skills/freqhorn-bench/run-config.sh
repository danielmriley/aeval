#!/usr/bin/env bash
# Run freqhorn over a benchmark suite with a given flag set; record the
# per-file outcome as success / timeout / error_rcN / nosolve into a CSV.
#
# usage: run-config.sh <out.csv> <timeout_s> <jobs> [flags...]
#   out.csv      output CSV path (columns: file,status,seconds)
#   timeout_s    per-file WALL timeout in seconds (the --to flag is a separate
#                per-Z3-call timeout; pass it inside [flags...] if you want it)
#   jobs         parallel workers (xargs -P)
#   flags...     freqhorn flags, placed BEFORE the filename on the command line
#
# Suite defaults to bench_horn. Override with BENCH=/abs/path env var.
# Binary defaults to the built freqhorn. Override with BIN=/abs/path.
#
# Completion is observable by polling the CSV line count (one header line +
# one line per benchmark). Do NOT poll progress with `pgrep -f run-config.sh`:
# a waiter whose own command line contains "run-config.sh" matches itself and
# deadlocks. Count CSV lines instead.
set -u

ROOT="/home/daniel/Projects/aeval"
BIN="${BIN:-$ROOT/build/tools/deep/freqhorn}"
BENCH="${BENCH:-$ROOT/bench_horn}"

if [ $# -lt 3 ]; then
  echo "usage: run-config.sh <out.csv> <timeout_s> <jobs> [flags...]" >&2
  exit 2
fi
OUT="$1"; TO_S="$2"; JOBS="$3"; shift 3
FLAGS="$*"

if [ ! -x "$BIN" ]; then
  echo "ERROR: freqhorn binary not found/executable: $BIN" >&2
  echo "       rebuild first: (cd $ROOT/build && make freqhorn)" >&2
  exit 2
fi
if [ ! -d "$BENCH" ]; then
  echo "ERROR: benchmark dir not found: $BENCH" >&2
  exit 2
fi

# Per-file work goes to a private temp dir, then we assemble the CSV at the
# end. This avoids concurrent appends racing on the same file.
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

run_one() {
  local f="$1" to="$2" work="$3" bin="$4"; shift 4
  local flags="$*"
  local base; base="$(basename "$f")"
  local start end dur rc output result
  start=$(date +%s.%N)
  # word-split $flags intentionally; flags come BEFORE the filename.
  output="$(timeout "${to}s" "$bin" $flags "$f" 2>&1)"
  rc=$?
  end=$(date +%s.%N)
  dur=$(awk "BEGIN{printf \"%.1f\", $end-$start}")
  if echo "$output" | grep -q "Success"; then result="success"
  elif [ $rc -eq 124 ]; then result="timeout"
  elif [ $rc -ne 0 ]; then result="error_rc$rc"
  else result="nosolve"; fi
  printf '%s,%s,%s\n' "$base" "$result" "$dur" > "$work/$base.line"
}
export -f run_one

ls "$BENCH"/*.smt2 \
  | xargs -P "$JOBS" -I {} bash -c 'run_one "$@"' _ {} "$TO_S" "$WORK" "$BIN" $FLAGS

# Assemble final CSV: header + sorted per-file lines.
{
  echo "file,status,seconds"
  cat "$WORK"/*.line 2>/dev/null | sort
} > "$OUT"

echo "=== DONE (flags: ${FLAGS:-<none>} | timeout ${TO_S}s | jobs ${JOBS}) ==="
awk -F, 'NR>1{c[$2]++} END{for(k in c) print "  "k": "c[k]}' "$OUT"
echo "  total: $(($(wc -l < "$OUT") - 1))"
