#!/usr/bin/env bash
# Characterize the CHC shape of a FreqHorn .smt2 benchmark with cheap greps.
# Usage: characterize.sh <file.smt2>
# Read-only: never runs the solver. Pairs with the freqhorn-diagnose skill.
set -euo pipefail

f="${1:?usage: characterize.sh <file.smt2>}"
[ -f "$f" ] || { echo "no such file: $f" >&2; exit 1; }

echo "== $f =="

# Relations (predicates). bench_horn uses the Datalog-style (declare-rel ...).
nrel=$(grep -cE '^\(declare-rel' "$f" || true)
echo "relations (declare-rel) : $nrel"
grep -oE '\(declare-rel +[A-Za-z0-9_]+' "$f" | awk '{print "    " $2}' || true

# Rules and the query/property.
echo "rules (rule)            : $(grep -cE '^\(rule' "$f" || true)"
echo "asserts                 : $(grep -cE '^\(assert' "$f" || true)"
echo -n "query                   : "; grep -hE '^\(query' "$f" | head -1 || echo "(none found)"

# Theory fingerprint.
echo "arrays (Array/select/store): $(grep -cE 'Array|select|store' "$f" || true)"
echo "mod/div (mod|div)       : $(grep -cE '\bmod\b|\bdiv\b' "$f" || true)"
echo "ite                     : $(grep -cE '\bite\b' "$f" || true)"
echo "nonlinear (* of 2 vars) : $(grep -oE '\(\* +[A-Za-z_][A-Za-z0-9_]* +[A-Za-z_]' "$f" | wc -l)"
echo "forall/exists in source : $(grep -cE 'forall|exists' "$f" || true)"

# Loop-shape heuristic: more than one non-query/fact relation -> likely multi-loop
# or a general graph rather than a single transition system.
if [ "$nrel" -gt 2 ]; then
  echo "shape hint              : >2 relations -> multi-loop or general CHC graph"
else
  echo "shape hint              : <=2 relations -> likely single transition system"
fi
