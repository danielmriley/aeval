---
name: freqhorn-bench
description: Runs and compares FreqHorn over CHC benchmark suites with noise-aware regression detection (re-checks every apparent regression at 2x timeout because freqhorn's RNG makes solve/timeout flip run-to-run). Use when benchmarking FreqHorn, measuring how many .smt2 files solve, comparing two flag configurations, or deciding whether a change is a real regression or RNG noise.
allowed-tools: Read Write Edit Bash Glob Grep
argument-hint: "[suite] [flags]"
---

# FreqHorn benchmarking with noise-aware comparison

FreqHorn is a CHC invariant solver. A run prints the substring **`Success`**
when it finds (and verifies) an invariant; a clean give-up prints `unknown`; a
wall-timeout prints neither. The default algorithm is `--v4` (confirmed in
`tools/deep/DeepHorn.cpp`: `if (!vers1 && !vers2 && !vers3 && !vers4) vers4 = true;`).

Paths (all absolute):
- Solver: `/home/daniel/Projects/aeval/build/tools/deep/freqhorn`
- CEX tool: `/home/daniel/Projects/aeval/build/tools/bnd/expl`
- Suites: `bench_horn` (352 sat .smt2, the main suite), `bench_horn_multiple`,
  `bench_horn_cex` (UNSAT systems where freqhorn is *expected* to diverge).
- Helper script: `run-config.sh` next to this SKILL.md.

## THE TWO GOTCHAS THAT WILL BITE YOU

1. **Stale binary.** The committed binary can lag the source. ALWAYS rebuild
   before measuring anything. Numbers from an un-rebuilt binary are worthless.

2. **RNG nondeterminism is real.** `freqhorn` calls `std::srand(std::time(0))`,
   so for a borderline benchmark, solve-vs-timeout **flips between runs of the
   exact same binary**. A file recorded success@30s in one run and timeout@60s
   in another, same binary. CONSEQUENCE: a single `success -> timeout` flip is
   NOT a regression. Never report one as a regression without the 2x re-check
   in Step 4.

## Step 1 - Rebuild first (always)

```bash
cd /home/daniel/Projects/aeval/build && make freqhorn
```

Z3 is already built; this takes ~1-2 min. gcc deprecation warnings are normal.
Asserts are ON in the default build (no `-DNDEBUG`), which is what we want.

## Step 2 - Run a suite into a CSV

Use the helper. Flags go BEFORE the filename inside the script. Make it
executable once:

```bash
chmod +x /home/daniel/Projects/aeval/.claude/skills/freqhorn-bench/run-config.sh
```

Signature: `run-config.sh <out.csv> <timeout_s> <jobs> [flags...]`
- `out.csv`     columns `file,status,seconds`; status is one of
  `success | timeout | error_rcN | nosolve`.
- `timeout_s`   per-file **wall** timeout in seconds. This is distinct from
  freqhorn's `--to` (per-Z3-call timeout in ms, default 1000) which you pass
  inside `[flags...]` if you want it.
- `jobs`        parallel workers. Use roughly `nproc` for a full suite.
- `[flags...]`  freqhorn flags, e.g. `--v4 --disj`, or `--v3`, etc.

Suite defaults to `bench_horn`. To run a different suite, set `BENCH`:

```bash
# baseline config, 60s wall timeout, parallel
SKILL=/home/daniel/Projects/aeval/.claude/skills/freqhorn-bench
"$SKILL/run-config.sh" /tmp/baseline.csv 60 "$(nproc)" --v4

# a different suite:
BENCH=/home/daniel/Projects/aeval/bench_horn_multiple \
  "$SKILL/run-config.sh" /tmp/multi.csv 60 "$(nproc)" --v4
```

A full `bench_horn` run at 60s with high parallelism takes a while, so launch
it detached (see Step 3) rather than blocking.

Useful flags (all confirmed via `freqhorn --help`): `--disj` (disjunctive
invariants), `--data N`, `--prop N`, `--all-mbp`, `--stren-mbp`, `--phase-data`,
`--phase-prop`, `--aggp`, `--prune`, `--to <ms>`, `--attempts N`, `--debug 0-5`,
`--eqs-mbp`, `--fwd`, `--re`, `--serialize` (dumps simplified CHCs to
`chc.smt2` and exits). Modes: `--v1 --v2 --v3 --v4`. When in doubt, run
`/home/daniel/Projects/aeval/build/tools/deep/freqhorn --help` rather than
guessing a flag.

## Step 3 - Launch detached and poll the CSV (NOT pgrep)

To run a long suite in the background without holding the foreground:

```bash
setsid "$SKILL/run-config.sh" /tmp/baseline.csv 60 "$(nproc)" --v4 \
  > /tmp/baseline.log 2>&1 </dev/null & disown
```

**Poll for completion by counting CSV lines, never with `pgrep -f run-config.sh`.**
A wait loop like `while pgrep -f run-config.sh; do sleep 5; done` **self-matches**:
the waiter's own command line contains `run-config.sh`, so `pgrep` finds itself
and the loop never exits -> deadlock. Same trap with `pkill -f run-config.sh`
(it can kill the waiter). Count lines instead:

```bash
TOTAL=$(ls /home/daniel/Projects/aeval/bench_horn/*.smt2 | wc -l)
while [ "$(( $(wc -l < /tmp/baseline.csv 2>/dev/null || echo 1) - 1 ))" -lt "$TOTAL" ]; do
  sleep 10
done
echo "done: $(($(wc -l < /tmp/baseline.csv) - 1))/$TOTAL"
```

Note: the script assembles the final CSV at the very end from per-file temp
results, so the live line count under `/tmp/baseline.csv` jumps from 1 (header)
to full only at completion. To watch live progress, instead poll the script's
log (`tail -n2 /tmp/baseline.log`) or, for a finer progress signal, run a
variant that writes incrementally. For correctness checks, the line-count gate
above is sufficient.

To kill stray runner/freqhorn jobs WITHOUT killing yourself, target by PID and
exclude the current shell `$$`:

```bash
# list freqhorn workers (the actual solver, not waiters)
pgrep -x freqhorn
# kill them, never touching $$:
for p in $(pgrep -x freqhorn); do [ "$p" != "$$" ] && kill "$p"; done
```

`pgrep -x freqhorn` matches the binary name exactly and cannot match a bash
waiter loop, so it is safe; the `run-config.sh` name is not.

## Step 4 - Compare two CSVs with the 2x noise re-check

Given two CSVs (e.g. `/tmp/baseline.csv` from master and `/tmp/cand.csv` from
your branch), classify the diff:
- **gain**: `timeout|nosolve -> success`
- **regression (candidate)**: `success -> timeout|nosolve`
- **crash**: anything `-> error_rcN`

Then, for EVERY apparent regression, re-run that single file with BOTH configs
at **2x the original wall timeout**. Because of the RNG flip, a borderline file
that timed out once will often solve when given more time or simply re-run. If
the re-check at 2x solves (or already solved on a re-run), label it **noise**,
not a regression. Only files that still fail at 2x with the candidate flags
while reliably succeeding with the baseline flags are **real** regressions.

```bash
SKILL=/home/daniel/Projects/aeval/.claude/skills/freqhorn-bench
A=/tmp/baseline.csv   # baseline config CSV
B=/tmp/cand.csv       # candidate config CSV
WALL=60               # the wall timeout the CSVs were produced with
A_FLAGS="--v4"        # flags used for A
B_FLAGS="--v4 --disj" # flags used for B
BIN=/home/daniel/Projects/aeval/build/tools/deep/freqhorn
BENCH=/home/daniel/Projects/aeval/bench_horn

issat() { grep -q "Success" <<<"$1" && echo success || echo notsuccess; }

join -t, -1 1 -2 1 \
  <(tail -n+2 "$A" | sort) <(tail -n+2 "$B" | sort) \
  | awk -F, '{print $1","$2","$4}' \
  | while IFS=, read -r file sa sb; do
      if [ "$sa" != success ] && [ "$sb" = success ]; then
        echo "GAIN       $file ($sa -> success)"
      elif [[ "$sb" == error_rc* ]]; then
        echo "CRASH      $file (-> $sb)"
      elif [ "$sa" = success ] && [ "$sb" != success ]; then
        # apparent regression -> re-check at 2x wall timeout
        out=$(timeout $((WALL*2))s "$BIN" $B_FLAGS "$BENCH/$file" 2>&1)
        if [ "$(issat "$out")" = success ]; then
          echo "NOISE      $file (regressed once, solved at 2x; RNG flip)"
        else
          # confirm baseline still solves it at 2x before calling it real
          outA=$(timeout $((WALL*2))s "$BIN" $A_FLAGS "$BENCH/$file" 2>&1)
          if [ "$(issat "$outA")" = success ]; then
            echo "REGRESSION $file (baseline solves @2x, candidate fails @2x)"
          else
            echo "NOISE      $file (baseline also fails @2x; borderline both)"
          fi
        fi
      fi
    done | sort | tee /tmp/freqhorn-compare.txt
```

## Step 5 - Summarize aggregate counts and net change

```bash
echo "=== $A_FLAGS ==="; awk -F, 'NR>1{c[$2]++} END{for(k in c)print "  "k": "c[k]}' "$A"
echo "=== $B_FLAGS ==="; awk -F, 'NR>1{c[$2]++} END{for(k in c)print "  "k": "c[k]}' "$B"
sa=$(awk -F, 'NR>1&&$2=="success"' "$A" | wc -l)
sb=$(awk -F, 'NR>1&&$2=="success"' "$B" | wc -l)
echo "success: $A_FLAGS=$sa  $B_FLAGS=$sb  net=$((sb-sa))"
echo "gains=$(grep -c '^GAIN' /tmp/freqhorn-compare.txt)" \
     "real_regressions=$(grep -c '^REGRESSION' /tmp/freqhorn-compare.txt)" \
     "noise=$(grep -c '^NOISE' /tmp/freqhorn-compare.txt)" \
     "crashes=$(grep -c '^CRASH' /tmp/freqhorn-compare.txt)"
```

Report the net success delta plus the gain / real-regression / noise / crash
counts. A net gain with zero *real* regressions is a clean improvement. Measured
reference points (one session): default `--v4` ~256/352; with bug fixes +
auto-enabled disjunction ~288/352. Treat these as ballpark, not targets.

## Soundness note (when a Success is suspicious)

Every reported `Success` on `--v3/--v4` is gated by `checkAllLemmas()` in
`include/deep/RndLearnerV3.hpp`, which re-checks the candidate against EVERY CHC
via `checkCHC` (SMT-checks `body AND src_inv AND NOT dst_inv'`) and returns true
only when every rule's violation query is definitively UNSAT; on Z3 `unknown`
it conservatively returns `false`. So candidate generation (sampling, data
learning, MBP) is untrusted and cannot manufacture a false Success. If you
suspect a soundness bug, look at the checker and the CHC encoding/preprocessing
(parse, `splitBody`, `eliminateQuantifiers`, `removeITE`, `simplifyArr`), not at
sampling.
