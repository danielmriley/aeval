# BV Project Implementation Plans

These plans are ordered so each phase produces a useful, reviewable increment. A
later phase can start only after the previous phase has landed its data structures,
tests, and user-facing behavior.

Use the BV regression suite in [`../benchmarks/`](../benchmarks/) to check solver
behavior before and after behavior-changing phases.

| Phase | Plan | Outcome |
| --- | --- | --- |
| 0 | [Baseline and invariants](phase-0-baseline.md) | Establish reproducible baselines and define correctness invariants before changing behavior. |
| 1 | [BV serialization](phase-1-serialization.md) | Make BV and translated BV systems exportable to external solvers. |
| 2 | [Rejected candidates](phase-2-rejected-candidates.md) | Preserve structured details for candidates that fail BV validation. |
| 3 | [Interval and overflow analysis](phase-3-interval-overflow.md) | Infer and represent tight guards that make LIA and BV arithmetic agree. |
| 4 | [Guarded retry](phase-4-guarded-retry.md) | Retry failed candidates under interval/no-overflow guards. |
| 5 | [LIA-to-BV VCEX](phase-5-lia-bv-vcex.md) | Translate abstraction counterexamples to BV CCEX and validate them. |
| 6 | [CHC propagation](phase-6-chc-propagation.md) | Propagate guarded candidates across multi-relation CHC graphs. |
| 7 | [Integration](phase-7-integration.md) | Stabilize defaults, evaluation, docs, and release behavior. |

Each phase should land with:

1. Implementation code.
2. Focused benchmarks or regression inputs.
3. CLI/help text updates if behavior is user-facing.
4. Validation through the existing build/test workflow.
5. A short update to `docs/bv-project/roadmap.md` if scope changes.
