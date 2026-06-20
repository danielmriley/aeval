# Phase 7: Integration, Evaluation, and Defaults

## Goal

Stabilize the new BV features, decide defaults, and make the workflow usable for
experiments and future development.

## Implementation steps

1. Review CLI defaults:
   - keep legacy behavior as default until the new modes are reliable
   - decide whether guarded retry should become default for `--v5`
   - keep always-on transition-system interval injection behind a flag unless benchmarks prove it safe
2. Consolidate flags:
   - avoid separate flags for features that are modes of one behavior
   - document interactions among `--v5`, `--lia2bv`, `--prop`, `--ccex`, and SyGuS options
3. Add help text:
   - describe guarded retry mode
   - describe always-on overflow interval mode
   - describe LIA-to-BV CEX validation
   - describe serialization modes
4. Create an evaluation script or documented command matrix:
   - safe BV benchmarks
   - unsafe BV/CCEX benchmarks
   - translated LIA-to-BV cases
   - multi-relation CHC cases
5. Track metrics:
   - candidates learned
   - candidates rejected
   - guarded candidates generated
   - guarded candidates accepted
   - interval sources used
   - CEX validations attempted and accepted
   - solve time per phase
6. Audit error handling:
   - no silent acceptance on UNKNOWN
   - no success-shaped fallback for missing translation maps
   - clear parse/serialization/solver errors
7. Audit output files:
   - generated SyGuS files
   - generated CCEX files
   - serialized CHC files
   - avoid overwriting unless documented or explicitly requested
8. Update docs:
   - `docs/bv-project/roadmap.md`
   - examples in README if user-facing commands change
   - benchmark README files if new benchmarks are added
9. Run full validation:
   - configure/build
   - focused BV regression commands
   - selected LIA regression commands to ensure no LIA FH behavior regressed

## Methods

- Prefer opt-in defaults until every feature has regression coverage.
- When enabling a default, include before/after benchmark evidence.
- Keep metrics parseable so experiment scripts can consume them.
- Maintain backwards compatibility for existing benchmark scripts where possible.

## Acceptance criteria

- User-facing modes are documented and discoverable from `--help`.
- Benchmarks cover success, failure, and unknown outcomes.
- Guarded retry and CEX validation do not produce false successes.
- The roadmap accurately reflects what is implemented and what remains future work.

