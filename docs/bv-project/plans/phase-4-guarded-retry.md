# Phase 4: Guarded Candidate Retry Loop

## Goal

Use rejected-candidate records and interval analysis to retry candidates under guards
that make LIA and BV semantics agree.

## Dependency

This phase depends on:

- Phase 2 rejected-candidate registry
- Phase 3 interval/no-overflow guard construction

## Landed guarded-retry slice

The first Phase 4 implementation adds an opt-in retry mode:

```sh
--bv-overflow-guards=retry
```

Default behavior remains `off`.

In retry mode, `BitHorn` now:

1. waits for normal BV Houdini validation to reject candidates;
2. selects rejected candidates with Phase 3 unsigned `bvadd` no-overflow guards;
3. builds guarded implications of the form `guard => candidate`;
4. validates those guarded candidates with the original BV CHCs;
5. records retry failures separately with source `bv-guarded-retry`;
6. suppresses duplicate guarded retries across solver iterations.

The current slice intentionally uses only no-overflow guards, not the broader
interval-looking comparisons. The Phase 3 interval collector is still diagnostic
and can include comparisons from the candidate itself, so using it directly as a
guard could create tautological retries. Tight interval environments remain
future work.

On the current benchmark set, this mode generates a guarded retry for
`bv_neg_01`, but it does not yet solve any additional benchmark. That is still a
useful landing point because the retry path is now wired, gated, and measurable.

## Landed BV-native bit-mask slice

Analysis of `bv_neg_01`, `bv_cmp_01`, `bv_add_01`, `bv_add_02`, and
`bv_mul_01` showed that some missing proofs are not overflow retries: they
require BV-native structure over `bvand`, `bvor`, `bvsub`, `bvadd`, `bvmul`,
and Boolean carry/equality flags. Since the BV-to-LIA translator currently
abstracts unsupported `bvand`/`bvor` operations to `0`, and arithmetic
abstractions can miss modular BV identities, these candidates must be produced
directly in the BV loop.

The opt-in mode:

```sh
--bv-bitmask-templates=basic
```

adds relation-local templates before BV Houdini validation. The solver tries
these templates before the expensive LIA loop so bitwise benchmarks do not time
out waiting for an arithmetic abstraction that erased the relevant operations.

For triples of BV relation variables without Boolean state flags, it emits
one-hot/prefix-cover candidates of the shape:

```text
(i = all_ones && (a | n) = all_ones)
||
(i != 0 && i <= high_bit && (i & (i - 1)) = 0
        && ((a | n) & (i - 1)) = (i - 1))
```

The mode is default-off and validated by the original BV CHCs. It solves
`bench_horn_bv/bv_neg_01.smt2` in the benchmark suite without changing default
behavior.

For relations with Boolean state flags, the same mode emits prefix-equality
candidates of the shape:

```text
(i = all_ones && flag = (a = b))
||
(i != 0 && i <= high_bit && (i & (i - 1)) = 0
        && flag = ((a & (i - 1)) = (b & (i - 1))))
```

This solves `bench_horn_bv/bv_cmp_01.smt2` in the benchmark suite without
changing default behavior.

For ripple-carry relations with operands `a`, `b`, one-hot index `i`, Boolean
carry/borrow flag, and accumulated result `d`, the same mode emits prefix
arithmetic candidates:

```text
(i = all_ones && d = (a +/- b))
||
(i != 0 && i <= high_bit && (i & (i - 1)) = 0
        && d = ((a +/- b) & (i - 1))
        && flag = carry_or_borrow_for_low_prefix)
```

This solves `bench_horn_bv/bv_add_01.smt2` and
`bench_horn_bv/bv_add_02.smt2` in the benchmark suite without changing default
behavior.

For three-variable repeated-addition multiplication relations, the same mode
emits modular multiplication-accumulator candidates:

```text
c = a * b
```

This solves `bench_horn_bv/bv_mul_01.smt2` in the benchmark suite without
changing default behavior.

## Target behavior

If `Cand(a,b)` fails in BV because `a + b` can wrap, generate a guarded candidate:

```text
Interval_a && Interval_b && no_overflow(a + b) => Cand(a,b)
```

Then validate that guarded candidate against the original BV CHCs. Only keep it if
BV validation succeeds.

## Implementation steps

1. Add retry eligibility checks:
   - failure has a concrete candidate expression
   - failure came from BV validation, not parser/translation error
   - candidate contains arithmetic where LIA/BV mismatch is plausible
   - interval analysis can produce a nontrivial guard
2. Add a guarded-candidate builder:
   - input: `RejectedBvCandidate`
   - input: interval environment
   - output: guarded expression
   - shape: `guard => candidate`
   - simplify `true => candidate` back to `candidate`
   - reject `false => candidate` as useless
3. Add retry scheduling:
   - process records per relation
   - limit retries per original candidate
   - preserve deterministic order
   - avoid retrying the same guarded expression twice
4. Validate guarded candidates:
   - use the existing BV rule checking path
   - do not bypass query checks
   - if the guarded candidate passes, merge it into the relation solution
   - if it fails, record the guarded failure with a retry depth
5. Integrate with solver iterations:
   - after `translateSolutionToBv`
   - before falling back to sampling
   - optionally after sampling failure
6. Add CLI controls:
   - `--bv-overflow-guards=off|retry|always`
   - `off`: current behavior
   - `retry`: guarded retry only after failures
   - `always`: inject interval assumptions as part of Phase 7 integration after validation
7. Add debug output:
   - number of failed candidates considered
   - number skipped with reason
   - number of guarded candidates generated
   - number accepted/rejected
8. Preserve existing priority behavior:
   - if a guarded retry succeeds, update learned/failed priorities consistently
   - if it fails, do not repeatedly penalize the same source candidate

## Methods

- Guard the candidate, not the transition system, until `always` mode is fully
  validated.
- Keep retry depth shallow at first. One guarded retry per failed candidate is enough
  for the first landing.
- Normalize guarded candidates before deduplication.
- Treat UNKNOWN validation as rejection, not success.

## Files likely to change

- `tools/deep/DeepHorn.cpp`
- `include/deep/BitHorn.hpp`
- interval helper files from Phase 3

## Tests and benchmarks

1. A known LIA-valid/BV-invalid candidate is rejected in `off` mode.
2. The same candidate is retried under a guard in `retry` mode.
3. A candidate with no arithmetic overflow risk is not guarded unnecessarily.
4. Duplicate guarded retries are suppressed.
5. UNKNOWN validation does not accept a candidate.

## Acceptance criteria

- Guarded retry is opt-in.
- Accepted guarded candidates are checked by the original BV CHCs.
- Debug output explains why candidates were retried or skipped.
- Existing default behavior remains unchanged until Phase 7.
