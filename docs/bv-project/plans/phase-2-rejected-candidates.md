# Phase 2: Rejected-Candidate Tracking

## Goal

Persist structured information about BV candidates that fail validation so later
phases can retry them with overflow guards instead of losing the reason for failure.

## Current starting points

- `BitHorn::assembleAndCheck`
- `BitHorn::multiHoudini`
- `BitHorn::weakenCandidates`
- `BitHorn::checkSafetyInBV`
- `RndLearnerV4::weaken`
- `SamplFactory::assignPrioritiesForFailed`

## Landed observational slice

The BV `BitHorn` path now records rejected candidates during Houdini-style BV
weakening without changing solver decisions:

- `RejectedBvCandidate` records live in `BitHorn` for now.
- Records are created in `BitHorn::weakenCandidates` when an individual candidate
  fails a BV rule check.
- Each record stores relation, candidate, failing rule body, source relation,
  destination relation, rule kind, result kind, source tag, validation iteration,
  and whether a concrete model is available.
- Duplicate records are suppressed by relation, candidate, failing rule, and source.
- Debug output at level 2 summarizes rejected candidates by relation; level 5 also
  prints individual rejected candidates.
- This is observational only: no candidate is retried or guarded yet.

## Data model

Introduce a small rejected-candidate record, for example:

```cpp
struct RejectedBvCandidate {
  Expr relation;
  Expr candidate;
  Expr failingRuleBody;
  Expr srcRelation;
  Expr dstRelation;
  Expr failureCondition;
  ExprMap counterModel;
  unsigned iteration;
  std::string source; // lia-solution, seed, data, sampling, propagated
};
```

The exact type can live in `BitHorn.hpp` initially. Move it to a dedicated header
only if multiple translation/learning components need it.

## Implementation steps

1. Add a candidate source tag:
   - LIA solution back-translation
   - seed mining
   - data learning
   - BV sampling
   - MBP-guided data learning
   - future propagated candidate
2. Modify `weakenCandidates` to collect failure records before erasing a candidate.
3. Extend rule checking so it can optionally return:
   - SAT/UNSAT/UNKNOWN
   - failing rule pointer
   - model for source, destination, and local variables
   - candidate expression that caused the failure
4. Store records in a per-relation registry:
   - `map<Expr, vector<RejectedBvCandidate>>`
   - preserve insertion order for deterministic debug output
5. Add debug output:
   - number of rejected candidates per relation
   - candidate source
   - failing rule kind: init, transition, query
   - whether a concrete model was captured
6. Add deduplication:
   - same relation
   - same candidate expression after normalization
   - same failing rule
   - same candidate source
7. Keep sampling priorities behavior intact:
   - existing failed-priority updates should still happen
   - rejected-candidate tracking adds data, not a new decision yet
8. Add a query API:
   - all rejected candidates
   - rejected candidates by relation
   - rejected candidates eligible for guarded retry
   - clear records after successful guard retry

## Methods

- Avoid string-only identity for expressions unless no expression comparison exists.
- Capture models only when the underlying solver has a model; do not fabricate values.
- Preserve UNKNOWN as a first-class failure reason because overflow analysis may not
  be safe when the failure is not concrete.
- Do not retry candidates in this phase; only track them.

## Files likely to change

- `include/deep/BitHorn.hpp`
- possibly `include/deep/RndLearnerV4.hpp` if LIA-side failures should be tagged
- possibly `include/ae/SMTUtils.hpp` if model extraction needs a helper

## Tests and benchmarks

1. A candidate that fails initialization is recorded with an init rule.
2. A candidate that fails consecution is recorded with a transition rule.
3. Duplicate failures do not create unbounded duplicate records.
4. Existing solving output is unchanged when debug is disabled.

## Acceptance criteria

- Failed BV candidates are available after a failed validation pass.
- Records identify relation, rule, candidate, and failure result.
- No guarded retries occur until Phase 4.
- Existing BV solving behavior remains unchanged except for gated diagnostics.
