---
name: freqhorn-review
description: Adversarial correctness review of C++ changes to the FreqHorn / ufo / Expr codebase, applying this repo's specific Expr/STL/index gotchas and ranking findings by soundness > crash > logic-regression > perf. Use when reviewing a diff, a refactor, or named modules under include/{ae,deep,sampl,ufo} or tools/deep for correctness bugs (not style) — e.g. "review my changes", "did this refactor break anything", "check RndLearnerV3 for bugs".
allowed-tools: Read Bash Glob Grep
argument-hint: "[module-or-file]"
---

# FreqHorn correctness review

You are reviewing C++ in a CHC invariant solver (header-only logic in
`include/{ae,deep,sampl,ufo}`, entry `tools/deep/DeepHorn.cpp`). The goal is
**correctness, not style**. This skill encodes the codebase-specific traps that
produce real bugs here.

Repo root: `/home/daniel/Projects/aeval`. Use absolute paths.

## 1. Scope the review

If given `$1` (a module/file), review that. Otherwise review the working diff.

```bash
cd /home/daniel/Projects/aeval
git diff                       # uncommitted changes
git diff master...HEAD         # whole-branch delta vs master
git diff master...HEAD -- <file>   # one file's refactor delta
```

Refactor regressions are the **single highest risk** on this repo (the active
work is a `*_refactor` branch). Always look at the `master...HEAD` delta for any
touched file, not just the latest commit — a meaning-change can hide several
commits back. When reading a refactor delta, line up the old and new versions of
each moved block and ask: did a condition get inverted, a branch dropped, two
arguments swapped, a `<` become `<=`, an early `return`/`continue` lost, or an
accumulator reset in the wrong scope?

## 2. Prioritise by severity

Report in this order; a low-severity finding never outranks a higher one:

1. **Soundness (false `Success`)** — the worst outcome. The solver is
   guess-and-check: every reported `Success` on `--v3`/`--v4` is gated by
   `checkAllLemmas()` in `include/deep/RndLearnerV3.hpp` (grep the name; it calls
   `checkCHC` which SMT-checks `body && src_inv && !dst_inv'` per rule and treats
   Z3 `unknown` conservatively as "not proven"). `printSolution`
   (`include/deep/RndLearner.hpp`) prints the same `learnedExprs` that were
   checked. **Consequence:** candidate generation (sampling, data learning, MBP,
   simplifier bugs) is UNTRUSTED and cannot by itself cause a false `Success`.
   The trusted perimeter is only: (a) the checker `checkAllLemmas`/`checkCHC`,
   and (b) the CHC encoding/preprocessing in `include/deep/Horn.hpp`
   (`parse`, `splitBody`, `eliminateQuantifiers`/`eliminate*`, `removeITE`,
   `simplifyArr`, vacuous-decl elimination, arithmetic propagation). A change
   that *weakens* a violation query, drops a rule from the check loop, or alters
   encoding meaning is a soundness bug. A bug in untrusted candidate code is at
   most a missed solve, not unsoundness — say so explicitly rather than crying
   wolf. For a deep encoding/checker audit, defer to the sibling skill
   `freqhorn-soundness-audit` if present.
2. **Crash / memory** — OOB index, null `Expr` deref, use-after-move, aborted
   assert. Asserts are ON in default builds (`CMAKE_BUILD_TYPE` is empty, no
   `-DNDEBUG`), so a violated invariant `abort()`s in production.
3. **Logic / refactor regression** — inverted conditions, lost branches, swapped
   args, off-by-one, wrong-scope state.
4. **Performance** — only after the above, and only if concretely material.

## 3. Codebase gotcha checklist

Check every changed line against these. They are the recurring real bugs here.

**Expr is an interned `boost::intrusive_ptr` to an ENode** (`include/ufo/Expr.hpp`):
- `operator==` is pointer/structural identity (the `ExprFactory` interns equal
  nodes); it is NOT a semantic equivalence test. Comparing Exprs for logical
  equivalence with `==` is a bug.
- A default-constructed `Expr` is **NULL**. Passing a NULL Expr into
  `replaceAll`, `isOpX<...>`, `op()`, `arg(i)`, `getTerm<...>` etc. segfaults.
  Any code path that can leave an Expr default-constructed and then uses it is
  suspect.

**`std::map<Expr, ...>::operator[]` default-inserts on a missing key** — it
creates (and mutates the map with) a NULL/zero value when the key is absent.
- `cycles[rel]` / `prefixes[rel]` (`map<Expr, vector<vector<int>>>` in
  `include/deep/Horn.hpp`) on a missing `rel` silently inserts an **empty
  vector**; subsequent `[0]` is OOB. Look for `someMap[expr]` reads where the key
  may be absent — they should be `.find`/`.count` guarded. (Contrast the safe
  pattern in `getCycleForRel`, which guards with `cycles.count(rel)` and returns
  the `empt` sentinel.)
- The default-insert also defeats later `.count()`/iteration assumptions, and a
  default-inserted NULL `Expr` value then gets deref'd downstream.

**`cycles` and `prefixes` are consumed in lockstep but their sizes are NOT
guaranteed equal.** They are `map<Expr, vector<vector<int>>>` (declared in
`include/deep/Horn.hpp`, grep `vector<vector<int>>> cycles, prefixes`) and are
indexed with a shared index across `BndExpl::compactPrefix`,
`Horn::getCycleForRel`, and `Horn::getPrefix` (grep these names). Any access
like `prefixes[rel][i]` paired with `cycles[rel][i]` must be bounds-checked; do
not assume `cycles[rel].size() == prefixes[rel].size()`. The
`assert(!cycles[rel].empty())` / `assert(!prefixes[rel].empty())` in
`Horn::getPrefix` only prove non-empty, not equal length. The correct handling
is in `BndExpl::compactPrefix`, which `.find`s `prefixes[rel]` and clamps the
index to the available entry prefix before reading — match that pattern.

**Conditionally-assigned, unconditionally-used indices.** The `fc_ind` /
`tr_ind` / `pr_ind` pattern in `include/deep/BndExpl.hpp`: these are set inside
`if (r.isFact/isInductive/isQuery)` loops and then used to index
`ruleManager.chcs[...]`. The correct version initialises to `-1` and asserts
`>= 0` before use (see `exploreTraces`); a refactor that drops the `= -1` init or
the guard reintroduces an OOB/garbage-index read. Flag any new index that is
assigned only in a branch and read outside it.

**New or changed `assert`s.** Because asserts fire in production, a too-strong
new invariant turns a survivable state into an `abort()`. Verify each new assert
actually holds on all reachable inputs (especially empty-container and
missing-key cases above).

**Soundness-perimeter edits.** Any change to `splitBody`, `parse`,
`eliminate*`, `removeITE`, `simplifyArr`, or arithmetic propagation in
`include/deep/Horn.hpp` changes what gets checked. Scrutinise for *meaning*
changes (a normalisation that is not equivalence-preserving), not just crashes.

## 4. Adversarial verification (do this before reporting)

Findings that are plausible-but-wrong are worse than no finding. For any
non-trivial review:

- For each candidate finding, do a **second pass that tries to refute it**:
  re-Read the actual code at the cited location (and its callers — `grep` the
  function name for call sites), and confirm the bug is reachable and not already
  guarded upstream. Drop anything you can't substantiate from the code in front
  of you.
- For reviews touching **more than ~5 files or 2+ modules**, spawn parallel
  sub-agent reviewers, one module per agent, each producing findings in the
  output format below. Then run the refutation pass on the merged list yourself
  before reporting. (Per the global directive on swarming for >5 files.)
- Do not trust the committed binary to reflect the source — it can lag. If a
  finding's severity depends on runtime behaviour, **rebuild first**:
  `cd /home/daniel/Projects/aeval/build && make freqhorn` (~1-2 min; gcc
  deprecation warnings are normal).
- If you reproduce a behaviour change by running benchmarks, beware
  **nondeterminism**: `freqhorn` seeds with `std::srand(std::time(0))`, so a
  single `Success`->`timeout` flip near the wall cutoff is NOISE, not a
  regression. Confirm any flip by re-running that one benchmark at 2x the wall
  timeout (`./confirm-flip.sh <file.smt2> <orig_timeout_s> [flags...]`). Never
  poll batch progress with `pgrep -f <scriptname>` (the waiter self-matches and
  deadlocks) — poll the output CSV's line count (`wc -l < results.csv`) instead.

## 5. Output

Produce a ranked list. For each finding:

- **`file:anchor`** — path and a grep-able anchor (function name + nearby
  pattern), not a bare line number (refactors move lines).
- **Category** — soundness / crash-memory / logic-regression / perf.
- **Severity** — high / medium / low.
- **Evidence / trigger** — the exact code and the concrete input or path that
  trips it (e.g. "`rel` absent from `cycles` -> `operator[]` inserts empty
  vector -> `[0]` OOB when called from `<caller>`").
- **Minimal correct fix** — the smallest change that fixes it, and any
  **call-site risk** the fix introduces (other callers depending on the old
  behaviour — `grep` them).
- **Disposition** — `safe to fix immediately` vs `needs design discussion`.

End with a one-line verdict: total findings by severity, and whether the diff is
safe to merge as-is. If you found nothing, say so plainly and name what you
checked — do not invent findings to look thorough.
