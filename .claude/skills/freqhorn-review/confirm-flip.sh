#!/usr/bin/env bash
# Confirm whether a freqhorn success<->timeout flip is real or just RNG noise.
# freqhorn seeds with std::srand(std::time(0)), so a single flip near the wall
# cutoff is expected. Re-run the SAME benchmark a few times at 2x the original
# timeout: if it solves at least once, the flip was noise, not a regression.
#
# usage: confirm-flip.sh <file.smt2> <orig_timeout_s> [freqhorn flags...]
set -u

BIN="/home/daniel/Projects/aeval/build/tools/deep/freqhorn"
FILE="${1:?usage: confirm-flip.sh <file.smt2> <orig_timeout_s> [flags...]}"
ORIG_TO="${2:?need original timeout in seconds}"
shift 2
FLAGS="$*"
RUNS=3
TO=$(( ORIG_TO * 2 ))

if [ ! -x "$BIN" ]; then
  echo "error: $BIN not found/executable; build first: (cd /home/daniel/Projects/aeval/build && make freqhorn)" >&2
  exit 2
fi
if [ ! -f "$FILE" ]; then
  echo "error: benchmark not found: $FILE" >&2
  exit 2
fi

echo "confirming flip: $(basename "$FILE")  flags=[$FLAGS]  ${RUNS} runs @ ${TO}s (2x of ${ORIG_TO}s)"
solved=0
for i in $(seq 1 "$RUNS"); do
  start=$(date +%s.%N)
  out="$(timeout "${TO}s" "$BIN" $FLAGS "$FILE" 2>&1)"
  rc=$?
  end=$(date +%s.%N)
  dur=$(awk "BEGIN{printf \"%.1f\", $end-$start}")
  if [ $rc -eq 124 ]; then
    echo "  run $i: timeout (${dur}s)"
  elif echo "$out" | grep -q "Success"; then
    echo "  run $i: success (${dur}s)"
    solved=$((solved + 1))
  elif [ $rc -ne 0 ]; then
    echo "  run $i: error rc=$rc (${dur}s)"
  else
    echo "  run $i: nosolve/unknown (${dur}s)"
  fi
done

echo "---"
if [ "$solved" -gt 0 ]; then
  echo "VERDICT: NOISE  ($solved/$RUNS solved at 2x timeout) -> not a regression."
  exit 0
else
  echo "VERDICT: REAL   (0/$RUNS solved at 2x timeout) -> investigate as a regression."
  exit 1
fi
