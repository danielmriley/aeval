---
name: freqhorn-soundness-audit
description: Audits FreqHorn's soundness by verifying its guess-and-check perimeter — every "Success" must be gated by a full SMT re-check, and every CHC encoding/preprocessing transform must be meaning-preserving. Use when asked to audit soundness, prove FreqHorn cannot report a false "Success", review the checker/perimeter, validate a CHC preprocessing transform, or confirm a candidate-generation change is soundness-safe.
allowed-tools: Read Bash Glob Grep
argument-hint: "[module]"
---

# FreqHorn Soundness Audit

FreqHorn is a CHC (Constrained Horn Clause) invariant solver. It is a
**guess-and-check** system: untrusted machinery *guesses* candidate invariants
(sampling, data learning, MBP, mutation, syntactic seed mining), and a trusted
*checker* re-verifies any candidate solution against every clause with Z3 before
reporting "Success".

The audit is therefore **not** a re-derivation of the whole solver. It is a
perimeter check with exactly two parts:

1. **The Success gates + the checker** — does every "Success" go through a full
   SMT re-verification, and is that checker conservative (unknown ⇒ not proven)?
2. **The trusted perimeter (CHC encoding/preprocessing)** — are the
   meaning-changing transforms applied *before* checking actually
   meaning-preserving? A bug here is the *only* way to get a false "Success",
   because the checker re-checks the already-transformed clauses.

Everything outside that perimeter (how candidates are guessed) cannot cause a
false "Success" — at worst it causes a missed invariant (a completeness/quality
issue). FreqHorn is intentionally **incomplete**: it may diverge or print
`unknown`. Divergence and `unknown` are never soundness bugs. Keep soundness
(never claim a false proof) and completeness (sometimes fail to find a real
proof) strictly separate in the report.

If `$1` (a module name, e.g. `RndLearnerV4`, `Horn`, `ExprSimpl`,
`AeValSolver`) is given, scope the deep audit to that file but still run the
Success-gate enumeration over all of `include/deep`.

## Ground rules

- **Rebuild before measuring.** The committed binary can lag the source:
  `cd /home/daniel/Projects/aeval/build && make freqhorn` (Z3 is prebuilt;
  ~1-2 min; gcc deprecation warnings are normal). Binaries:
  `build/tools/deep/freqhorn` (solver), `build/tools/bnd/expl` (counterexamples).
- **Prefer grep-able anchors over line numbers.** Refactors move lines; the
  function names below are stable.
- **Don't fabricate.** If you cannot confirm a transform preserves meaning,
  label it `UNVERIFIED`, not `SOUND`.
- **Success detection** for any experiment: solver stdout contains the substring
  `Success`. A clean failure prints `unknown`. A wall-timeout prints neither.

## Step 1 — Enumerate every "Success" gate

Run the helper, which greps every `"Success` print in the solver headers and
reports whether a full-verification call dominates it:

```
.claude/skills/freqhorn-soundness-audit/check-success-gates.sh
```

Or by hand:

```
grep -rn '"Success' /home/daniel/Projects/aeval/include/deep/*.hpp
```

Expected gates (confirm each still holds; **flag any new `"Success` that is not
gated**):

- `RndLearnerV3.hpp` and `RndLearnerV4.hpp` — every `outs() << "Success ...`
  is immediately preceded by `if (checkAllLemmas())`. V4 (`class RndLearnerV4 :
  public RndLearnerV3`) inherits V3's `checkAllLemmas`/`checkCHC`, so the V4
  gate *is* the V3 checker. Verify with `grep -n 'checkAllLemmas\|printSolution'
  include/deep/RndLearnerV3.hpp include/deep/RndLearnerV4.hpp`.
- `RndLearner.hpp` (V1) — `success` is set by
  `if (isInductive) success = checkSafety();` after `checkCandidates()`, and the
  `"Success` print plus `printSolution()` are guarded by `if (success)`.
- `RndLearnerV2.hpp` — `success` comes from `houdini(...)` /
  `checkSafetyAndReset(...)`; the print is guarded by `if (success)`.
- `BndExpl.hpp` — these belong to the **`expl` counterexample tool**, not the
  invariant solver. `"Success after complete unrolling"` means the CHC system
  was fully discharged by bounded unrolling (no inductive guess). The helper
  flags them as "ungated" by design; classify them as **out of scope** for the
  invariant-solver soundness claim.

The helper uses a backward text window, so treat its output as evidence to
read, not a verdict. For every site it flags, open the function and confirm a
verification call **dominates the print on every path**.

## Step 2 — Audit the checker

This is the trust anchor. Read `checkAllLemmas` and `checkCHC` in
`include/deep/RndLearnerV3.hpp` (anchor: `grep -n 'bool checkAllLemmas\|tribool
checkCHC' include/deep/RndLearnerV3.hpp`). Confirm all of:

- **`checkCHC` builds the violation query** = `body ∧ src-invariant ∧
  ¬dst-invariant'`. In the code: it asserts `hr.body`, then for non-fact rules
  inserts the source lemmas/annotations rewritten onto `hr.srcVars`, then for
  non-query rules inserts `disjoin(negged, ...)` where `negged` is the *negated*
  destination lemmas rewritten onto `hr.dstVars`. It returns `u.isSat(exprs)`.
  So **`isSat == true` means the rule is VIOLATED** (a model satisfies body ∧
  pre ∧ ¬post). Confirm the sense of the boolean is "violated", not "holds".
- **`checkAllLemmas` returns `true` only if every rule is definitively safe.**
  It loops all `ruleManager.wtoCHCs`; if any `checkCHC` is `true` (violated) it
  returns `false`. On `indeterminate(b)` (Z3 `unknown`) it retries once with an
  escalated timeout (`u.setTimeout(to * 8)`) and, if still violated or still
  indeterminate, returns `false`. **Confirm indeterminate ⇒ `false`** — a
  transient `unknown` must never be read as "proven". This conservatism is the
  whole soundness argument; any change that lets `unknown` fall through to
  `true` is a critical soundness bug.
- **`printSolution` prints the same thing that was checked.** In
  `include/deep/RndLearner.hpp` (anchor: `grep -n 'void printSolution'`),
  confirm it emits `sf.learnedExprs` per declaration — the same `learnedExprs`
  that `checkCHC` reads via `sfs[...].back().learnedExprs`. The trailing
  `assert(hasOnlyVars(res, ruleManager.invVars[rel]))` guards against printing
  stray variables (asserts are ON in default builds — `CMAKE_BUILD_TYPE` is
  empty, no `-DNDEBUG`). Note `printSolution` may *simplify* for display
  (`simplifyArithm`, `removeRedundantConjuncts`); confirm simplification is
  display-only and does not feed back into what was verified.

If all three hold, the gate is sound regardless of how candidates were guessed.

## Step 3 — Audit the trusted perimeter (encoding & preprocessing)

These transforms run **before** the checker, so the checker re-checks their
*output*. A meaning-changing bug here can make a genuinely-unsafe system look
safe ⇒ false "Success". This is the only place soundness bugs live.

### 3a. CHC parse / structure — `include/deep/Horn.hpp`

Read the parse pipeline (anchor: `grep -n 'bool splitBody\|eliminateQuantifiers\|removeITE\|simplifyArr\|eliminateDecls' include/deep/Horn.hpp`):

- **`splitBody`** — separates the rule body into the linear part (`hr.lin`),
  the source/destination relation applications, and local vars. Confirm it
  drops nothing semantically: every conjunct of the original body must land in
  `lin` or be accounted for by a relation application. A dropped constraint
  *weakens* the body, which can falsely make a violation query UNSAT.
- **Body construction under `doElim`** —
  `hr.body = eliminateQuantifiers(conjoin(hr.lin, ...), hr.locVars, ...)`, then
  `removeITE`, then `simplifyArr`, then `shrinkLocVars`. These must be
  equivalent over the non-local (relation) variables. See 3c for how to check.
- **`eliminateDecls` + vacuous-decl elimination** (the `// get rid of vacuous:`
  loop) — removes relations that never appear as any rule's destination, along
  with the rules that only use them as a source. Confirm a removed relation is
  truly unconstrained-as-target (so any rule reading it is vacuously
  discharged); wrongly removing a constraining clause drops a proof obligation.
- **Arithmetic constant propagation** (parse-time; toggled off by
  `--skip-arithm`) and **slicing/minimization** (toggled off by `--skip-elim`)
  — these are the two preprocessing stages with kill switches, which makes them
  directly testable (Step 4).

### 3b. Expression transforms — `include/ae/`

Anchors:
`grep -n 'eliminateQuantifiers' include/ae/AeValSolver.hpp` and
`grep -n 'simplifyArithm\|simplifyArr\|removeITE' include/ae/ExprSimpl.hpp`.

- `eliminateQuantifiers` (AeValSolver.hpp) — must produce a formula equivalent
  to `∃ qVars. fla` over the remaining variables.
- `simplifyArithm` / `simplifyArithmConjunctions` / `simplifyArithmDisjunctions`
  (ExprSimpl.hpp) — arithmetic normalization; must be logically equivalent.
- `simplifyArr`, `removeITE`, `propagateStore` (ExprSimpl.hpp) — array/ITE
  rewrites; must be equivalent.

For each, read it for the kind of bug that *changes meaning*: an algebraic
simplification that is only valid under a side condition that isn't checked, a
`std::map<Expr,...>::operator[]` that default-inserts a NULL `Expr` for a
missing key (use `.find`/`.count`), or a transform that silently drops a
conjunct. (Note: `Expr` is an interned, structurally-identified
`boost::intrusive_ptr`; `operator==` is structural identity.)

### 3c. Differential equivalence checking (higher assurance)

Don't just read — *prove* meaning-preservation on real inputs. FreqHorn can dump
its fully-preprocessed clauses, which lets you diff "what the user wrote" vs.
"what the checker sees":

1. Dump the preprocessed system (this writes `chc.smt2` in the **current
   directory** and exits):

   ```
   cd /tmp && rm -f chc.smt2
   /home/daniel/Projects/aeval/build/tools/deep/freqhorn --serialize <orig>.smt2
   ```

   `chc.smt2` is a self-contained `(set-logic HORN) ... (check-sat)` file — the
   post-`splitBody`/`eliminateQuantifiers`/`removeITE`/`simplifyArr` encoding.

2. **Per-transform body check.** For a single rule body `B` and its transformed
   form `T(B)` (e.g. before/after `removeITE` or `simplifyArr`), build a tiny
   `.smt2` asserting `(and B (not T(B)))` *and* separately `(and (not B) T(B))`
   (i.e. check `B XOR T(B)` is UNSAT) over the rule's variables, and run
   `z3 file.smt2` (z3 is at `/usr/bin/z3` and `build/run/bin/z3`). **`unsat`
   for both directions ⇒ equivalent.** Any `sat` is a meaning-changing
   transform — a soundness defect; capture the model as a witness. Any `unknown`
   ⇒ **`UNVERIFIED`**, never `SOUND`.

3. **Whole-system sanity.** The preprocessed `chc.smt2` should be
   equisatisfiable (as a CHC system) with the original. A cheap check: confirm
   `freqhorn` reaches the same verdict on the original and (when re-runnable) on
   a system you reconstruct from `chc.smt2`; a verdict flip from `unknown`→
   `Success` after preprocessing is a red flag worth a body-level diff.

   Beware nondeterminism (Step 4) when comparing verdicts.

## Step 4 — Nondeterminism discipline (don't misread experiments)

`freqhorn` calls `std::srand(std::time(0))`, so **solve-vs-timeout flips between
runs of the same binary** near the wall-clock cutoff. A single
`Success`→`timeout` flip is **not** a regression and **not** a soundness signal.
Confirm any flip by re-running at **2× the wall timeout**; if it then solves (or
was borderline), it's noise.

What this means for the audit:

- Soundness is about *false* `Success`, never about *missing* `Success`. A
  benchmark that times out or prints `unknown` is irrelevant to soundness.
- To stress the checker, run with kill switches to exercise more of the
  perimeter: `--skip-elim` (no minimization/slicing) and `--skip-arithm` (no
  arithmetic propagation) should never *create* a `Success` that the default
  run rejects on the same file — if disabling a transform changes a `Success`
  into `unknown` that's fine (completeness), but if *enabling* a transform turns
  a real counterexample system into a `Success`, that's a perimeter bug.
- Cross-check expected-UNSAT systems: `bench_horn_cex/` holds systems where the
  solver is *expected to diverge* and `expl` finds a counterexample. The solver
  must **never** print `Success` on those. Any `Success` there is a concrete
  false proof — the highest-severity finding.
- The main satisfiable suite is `bench_horn/` (352 `.smt2`).
- When batch-running, **never poll progress with `pgrep -f <script>`** — the
  waiter's own command line self-matches and deadlocks. Poll the output CSV line
  count instead (`wc -l < results.csv`). Prior-art runners:
  `docs/bv-project/benchmarks/run-config.sh`, `run-baseline.sh`.

## Step 5 — Report

Produce a report with two clearly separated sections.

**A. Success gates + checker**
- A table: every `"Success` site (`file:function` or grep anchor) →
  `GATED by <call>` / `UNGATED — investigated: <conclusion>`.
- Checker findings: `checkCHC` query sense (violated == isSat), `checkAllLemmas`
  conservatism (indeterminate ⇒ false), `printSolution` prints-what-was-checked.
  State PASS/FAIL for each with `file:function` evidence.

**B. Trusted perimeter transforms**
- One row per transform (`splitBody`, body `eliminateQuantifiers`/`removeITE`/
  `simplifyArr`, `eliminateDecls`/vacuous elim, arithmetic propagation,
  `simplifyArithm`*, array rewrites): verdict ∈ {**SOUND**, **UNVERIFIED**,
  **SUSPECT**} with `file:function` evidence and, where used, the differential
  z3 result (both XOR directions `unsat`).

**Non-issues (explicitly do NOT flag as soundness bugs):** candidate generation
— sampling, data learning, MBP, mutation, seed mining, and the `normalizeAtom`
`v*v` simplifier — are *untrusted*; any bug there is masked by the checker and
is a completeness/quality issue at most. Note them only under a separate
"completeness" heading if relevant. Likewise, divergence and `unknown` outputs
are by-design incompleteness, not soundness defects.

End with a one-line bottom line: **can FreqHorn currently emit a false
"Success"?** If every gate is verified and every perimeter transform is SOUND or
UNVERIFIED-but-not-SUSPECT, the answer is no; otherwise name the exact transform
or gate that breaks it.
