---
name: freqhorn-diagnose
description: Diagnoses why a specific FreqHorn benchmark (or family) times out and proposes concrete levers, by characterizing the CHC shape, identifying the required invariant class, running a flag-experiment matrix, locating the stall with --debug, and inspecting the serialized transition. Use when a .smt2 benchmark hangs, times out, or returns unknown under freqhorn and you need to understand the root difficulty and which flags or code changes would help.
allowed-tools: Read Bash Glob Grep
argument-hint: "[benchmark.smt2]"
---

# FreqHorn: diagnose a timeout

Goal: for one benchmark (or a family), explain *why* FreqHorn fails to find an
invariant in the time budget, and rank concrete fixes. FreqHorn is a CHC
invariant solver (Z3 backend, header-only logic under `include/{ae,deep,sampl,ufo}`,
entry `tools/deep/DeepHorn.cpp`). The default mode is `--v4` (MBP / phase /
disjunctive) — `DeepHorn.cpp` sets `vers4 = true` when no `--vN` flag is given,
even though `--help` text labels v3 the default.

Paths used below:
- solver:   `/home/daniel/Projects/aeval/build/tools/deep/freqhorn`
- cex tool: `/home/daniel/Projects/aeval/build/tools/bnd/expl`
- suite:    `/home/daniel/Projects/aeval/bench_horn` (352 sat .smt2)
- helper:   `characterize.sh` (next to this SKILL.md)

## Step 0 — rebuild first (mandatory)

The committed binary can lag the source. Always rebuild before measuring:

```
cd /home/daniel/Projects/aeval/build && make freqhorn
```

~1-2 min (Z3 already built). gcc deprecation warnings are normal.

## Step 1 — characterize the CHC shape

Run the helper (read-only, never invokes the solver):

```
/home/daniel/Projects/aeval/.claude/skills/freqhorn-diagnose/characterize.sh <file.smt2>
```

It reports: number of relations (`declare-rel`), rules, the `(query ...)`
property, and a theory fingerprint (arrays, mod/div, ite, nonlinearity,
quantifiers). Then read the `.smt2` yourself to confirm:
- single transition system (one `inv` + `fail`) vs multi-loop / general graph
  (>2 relations);
- whether the transition has arrays (`select`/`store`), nonlinear `(* x y)`,
  `mod`/`div`, or `ite`;
- what the query actually asserts (the property to prove safe).

## Step 2 — name the required invariant CLASS

From the shape, hypothesize what an invariant *must* look like — this predicts
which lever matters:
- **Conjunctive** (plain ranges/equalities): default should work; if it times
  out, suspect sampling/data, not expressiveness.
- **Disjunctive / phased** (loop changes behavior at a guard; survives as an
  arithmetic `ite` in the serialized transition — see Step 5): needs `--disj`
  and phase discovery (`--all-mbp`, `--phase-data`, `--phase-prop`).
- **Quantified-array** (init/copy/tiling loops): needs the array seed miner;
  the printed invariant will contain `forall ... (select ...)`.
- **Modular** (`mod`/`div` in the transition): MBP/QE cannot eliminate these —
  see the qeUnsupported note in Step 4.
- **Nonlinear** (`(* x y)` of two variables): hardest; data candidates and
  mutation (`--mut 2`) are the only realistic source.

## Step 3 — run the flag-experiment matrix

Use a SHORT per-run wall timeout (~25s) so you can try many configs. Record the
exact flags, solved-vs-timeout, and seconds for each. A flag only "solves it" if
the substring **`Success`** actually appears in the output.

```bash
F=<file.smt2>
BIN=/home/daniel/Projects/aeval/build/tools/deep/freqhorn
run() { d=$( { /usr/bin/time -f '%e' timeout 25 "$BIN" $1 "$F"; } 2>&1 ); \
  if echo "$d" | grep -q Success; then s=SOLVED; else s=timeout/unknown; fi; \
  t=$(echo "$d" | tail -1); printf '%-32s %-16s %ss\n' "[$1]" "$s" "$t"; }

run ""                                   # default --v4
run "--disj"
run "--data 4"
run "--prop 2"
run "--disj --all-mbp --stren-mbp"
run "--aggp --prune"
run "--to 5000"                          # raise per-Z3-call timeout (default 1000ms)
run "--attempts 8000000"
```

NONDETERMINISM IS REAL: `freqhorn` seeds with `std::srand(std::time(0))`, so a
benchmark near the wall cutoff FLIPS solved/timeout between runs of the SAME
binary. NEVER call a single solve->timeout a regression. Confirm a flip by
re-running at 2x the wall timeout; if it then solves (or was already borderline),
it is noise, not a real difference between flags.

## Step 4 — locate the stall with --debug 3

Briefly (cap at ~8-10s; this is verbose):

```
timeout 10 "$BIN" --debug 3 <file.smt2> 2>&1 \
  | grep -iE 'MBP|path|bootstrap|houdini|sampl|phase|check|learn'
```

Map the last sustained activity to a stall point:
- repeated `MultiHoudini` / `CHC check failed` -> stuck in bootstrapping; the
  candidate pool never closes under the rules (`RndLearnerV3.hpp`,
  `multiHoudini` / `checkCHC`).
- `DATA LEARNING` churning with no new lemmas -> data candidates aren't useful
  (try `--data 4`, `--re`, `--mut 2`).
- few `Generated MBP` / phase lines -> MBP/phase discovery is degenerate
  (`RndLearnerV4.hpp`).
- progress then silence at the end -> the final `checkAllLemmas` (Step "trusted
  perimeter") is timing out on Z3.

KNOWN SIGNAL — MBP degeneracy on mod/div: when the transition contains `mod`
or `div`, MBP/QE bails. `qeUnsupported` in `include/ae/AeValSolver.hpp` returns
true on `containsOp<MOD>` / `containsOp<DIV>`, so QE is skipped and the phase
decision tree collapses. With `--debug 3` you will see the tell-tale line

```
MBPs are organized as a decision tree (with 1 possible path(s))
```

(printed at the `possible path(s)` message in `include/deep/RndLearnerV4.hpp`).
"1 possible path" on a clearly multi-phase loop == QE gave up; disjunctive/phase
machinery has nothing to work with.

## Step 5 — inspect the serialized transition

`--serialize` writes the post-elimination CHCs to `chc.smt2` in the CURRENT
directory and exits (silently). Run from a scratch dir so you don't clobber the
repo:

```
cd /tmp && rm -f chc.smt2 && "$BIN" --serialize <file.smt2> && grep -n 'ite\|mod\|div\|forall' chc.smt2
```

Read `chc.smt2`. This is what the solver actually reasons about after parse,
`splitBody`, `eliminateQuantifiers`, `removeITE`, `simplifyArr`, vacuous-decl
elimination, and arithmetic propagation. Key tells:
- an arithmetic **`ite` that survived `removeITE`** => the loop is genuinely
  phased; a conjunctive invariant cannot exist, so `--disj` is required.
- residual `mod`/`div` => confirms the qeUnsupported path from Step 4.
- `forall ... select` in the simplified body => quantified-array territory.

## Step 6 — output the diagnosis

Produce a concise report:
1. **Shape** — #relations, single-loop vs multi-loop/graph, theories present,
   the property.
2. **Required invariant class** (Step 2) and the evidence (Step 5 serialized
   transition).
3. **Best existing config** — the winning row from the Step 3 matrix, or
   "none solved within 25s" (re-confirmed for nondeterminism).
4. **Stall point** (Step 4) with the source location.
5. **Root difficulty** — one sentence: why the current pipeline can't close it.
6. **Ranked improvement hypotheses**, each with a `file:function` anchor.

## Known timeout families and known levers

Families that commonly diverge in `bench_horn` (glob to see siblings):
- `s_split_*` — phased single loops; need disjunction/phase discovery.
- `array_split_*`, `array_tiling_*` — quantified-array + phase; serialized
  transition keeps an `ite`.
- scaling `sn_*` — size blows up; raise `--to`, `--attempts`.
- `nonlin_*` and modular (`mod`/`div`) benchmarks — QE bails (Step 4).
- UNSAT systems live in `bench_horn_cex/`: freqhorn is *expected* to diverge;
  `expl` finds the counterexample. If a "timeout" is actually UNSAT, that's not
  a solver bug — confirm with `expl`.

Levers proven useful this session, with code anchors:
- **Auto-enable disjunction** for bodies with `ite`/`OR` (the survived-`ite`
  signal in Step 5) — wiring in `tools/deep/DeepHorn.cpp` (`OPT_DISJ`) and the
  V4 phase machinery in `include/deep/RndLearnerV4.hpp`.
- **Collapse enumerated init FACTs** during preprocessing so bootstrapping
  isn't flooded — CHC encoding in `include/deep/RndLearnerV3.hpp` parse/normalize.
- **Treat Z3 `unknown` as retry** rather than giving up in the candidate loop
  (NOT in `checkAllLemmas` — there, conservative `false` on `unknown` is the
  soundness contract; see below).
- **MBP mod/div elimination** — extend or pre-rewrite around `qeUnsupported` in
  `include/ae/AeValSolver.hpp` so phased modular loops get >1 path.

## Soundness perimeter (don't propose unsound "fixes")

Every reported `Success` on --v3/--v4 is gated by `checkAllLemmas()` in
`include/deep/RndLearnerV3.hpp`, which re-checks the invariant against EVERY CHC
via `checkCHC` (SMT-checks `body AND src_inv AND NOT dst_inv'`; sat == rule
violated). It returns true only when every rule's violation query is definitively
UNSAT, and conservatively returns **false** on Z3 `unknown`. `printSolution`
(`include/deep/RndLearner.hpp`) prints exactly those checked `learnedExprs`.
Consequence: candidate generation (sampling, data learning, MBP, simplifier
quirks) is UNTRUSTED and cannot cause a false Success — so an improvement
hypothesis that loosens candidate generation is safe to propose. Only the
checker and the CHC encoding/preprocessing are the trusted perimeter; never
propose making `checkAllLemmas` accept `unknown`.
