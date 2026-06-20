#!/usr/bin/env bash
# Enumerate every site that prints "Success" in the FreqHorn solver headers and
# show the surrounding lines so a human/agent can confirm each one is immediately
# guarded by a full SMT re-verification (checkAllLemmas / checkCandidates+checkSafety).
#
# This does NOT decide soundness on its own -- it surfaces the evidence. A gate is
# only sound if a verification call dominates the "Success" print on every path.
#
# Usage: ./check-success-gates.sh [repo_root]
#   repo_root defaults to the aeval checkout two levels up from this script.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="${1:-$(cd "$SCRIPT_DIR/../../.." && pwd)}"
DEEP="$REPO/include/deep"

if [[ ! -d "$DEEP" ]]; then
  echo "ERROR: $DEEP not found. Pass the aeval repo root as arg 1." >&2
  exit 1
fi

# The gate keywords that constitute a *full* SMT re-verification of the whole
# candidate solution against every CHC. checkAllLemmas is the V3/V4 gate;
# checkCandidates()+checkSafety() is the V1 gate; houdini+checkSafetyAndReset
# is the V2 gate. V1/V2 set a `success` bool from these calls, then print
# "Success" later under `if (success)`, so we also accept that guarded pattern.
GATE_RE='checkAllLemmas|checkSafety|checkCandidates|checkSafetyAndReset|houdini'

# Window (lines) to look backward from a "Success" print. Wide enough to span
# the V1/V2 idiom where `success` is assigned a verification result well above
# the conditional print.
WINDOW=80

echo "== FreqHorn Success-gate enumeration =="
echo "repo: $REPO"
echo

grep -rn '"Success' "$DEEP"/*.hpp | while IFS= read -r hit; do
  file="${hit%%:*}"
  rest="${hit#*:}"
  line="${rest%%:*}"
  start=$(( line - WINDOW )); (( start < 1 )) && start=1

  base="$(basename "$file")"
  ctx="$(awk -v a="$start" -v b="$line" 'NR>=a && NR<=b' "$file")"

  if echo "$ctx" | grep -Eq "$GATE_RE"; then
    gate="$(echo "$ctx" | grep -Eo "$GATE_RE" | tail -1)"
    verdict="GATED ($gate)"
  else
    verdict="*** UNGATED -- INVESTIGATE ***"
  fi

  printf '%-22s line %-5s  %s\n' "$base" "$line" "$verdict"
done

echo
echo "Notes:"
echo " - BndExpl.hpp Success lines belong to the 'expl' counterexample tool, not the"
echo "   invariant solver; 'Success after complete unrolling' means the CHC system was"
echo "   fully discharged by bounded unrolling (no inductive guess involved)."
echo " - 'UNGATED' only means no gate keyword appeared within $WINDOW lines above the"
echo "   print. Read the function: confirm a verification call dominates the print on"
echo "   EVERY path before declaring a real soundness hole."
