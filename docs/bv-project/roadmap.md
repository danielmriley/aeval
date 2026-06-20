# BV FreqHorn Roadmap

This document turns the BV project notes into an implementation roadmap for this
repository. It should be read with the phase plans under `docs/bv-project/plans/`
and the regression set under `docs/bv-project/benchmarks/`.

## Project context

FreqHorn is a CHC solver whose mature path is LIA FreqHorn (`--v4`). The BV path
(`--v5`) is centered around `include/deep/BitHorn.hpp` and works as an
abstraction/refinement loop:

1. Parse BV CHCs with `CHCs`.
2. Translate the BV system to LIA with `Bv2LiaTranslator`.
3. Learn candidates with the LIA FreqHorn machinery.
4. Translate learned candidates back to BV with `Lia2BvTranslator`.
5. Validate the result against the original BV rules.

The current SyGuS counterexample path is implemented mostly in
`tools/deep/DeepHorn.cpp`, `include/deep/Horn.hpp`, and `include/deep/BndExpl.hpp`.
It can emit BV SyGuS files, run CVC5, generate CCEX files, and validate them
inductively.

## Reading the original notes

| Note | Project meaning |
| --- | --- |
| `not CHCs but TR` | The strongest BV SyGuS CEX path is transition-relation-shaped: one init rule, one self-loop transition, and one query. It is not yet a general multi-relation CHC CEX engine. |
| `Serialize BV system to use other solvers` | Make BV and translated BV systems reliably exportable to standard SMT-LIB/Horn formats for external solvers. Existing `serialize` paths are a starting point, not the full product. |
| `Extension to CEX?` | Extend the BV/LIA abstraction loop so it can refine and validate counterexamples, not just safety candidates. |
| `CEX from LIA to BV then check VCEX` | Generate or receive a CEX in the LIA abstraction, translate it to BV/CCEX form, then validate it with the BV CEX validator. Treat "VCEX" as "validated CEX" unless the codebase introduces a dedicated type. |
| `Track cands that are rejected in the previous step` | Keep structured failure records instead of only weakening/dropping bad candidates. |
| `Retry failed cands with overflow guards` | If a LIA-valid candidate fails in BV due to wraparound, retry it guarded by intervals or no-overflow constraints. |
| `Interval_a /\\ Interval_b -> Failed Cand(a,b)` | A rejected candidate can become `guard(a,b) => cand(a,b)`, where `guard` records ranges under which BV and LIA semantics agree. |
| `Try to figure out as tight an interval as possible` | Prefer transition-derived per-variable bounds over coarse full bitwidth bounds. |
| `Flag for adding overflow intervals to the TS all the time` | Add a solver flag that injects interval/no-overflow assumptions proactively during translation/refinement. |
| `Compare LIA FH and BV FH` | Maintain explicit parity tracking so missing BV features do not stay implicit. |
| `What blocks this from moving to CHCs? Needs to support cand propagation.` | General CHC support needs candidates and guarded refinements propagated across relations, not just checked at a single loop head. |

## LIA FH vs BV FH feature matrix

| Feature | LIA FreqHorn (`--v4`) | BV FreqHorn (`--v5` / BV SyGuS path) | Gap to close |
| --- | --- | --- | --- |
| Native logic | Linear integer arithmetic CHCs. | BV CHCs, commonly abstracted to LIA and checked back in BV; opt-in BV-native templates now cover one-hot/prefix-cover, prefix-equality, prefix-arithmetic masks, and multiplication accumulators. | Preserve enough BV semantics during abstraction to explain and repair wraparound and bitwise failures. |
| CHC topology | General CHC graphs with cycle analysis. | BV solver accepts CHCs; SyGuS CEX TR mode assumes init/transition/query shape. | Generalize BV CEX and guarded candidates beyond single-loop TR shape. |
| Seed mining | Mature syntax mining via `SeedMiner`. | Present in BV sampling, but not a complete parity story. | Reuse mined seeds in guarded BV refinement and SyGuS grammar construction. |
| Bootstrapping | Mature Houdini-style filtering. | Runs through LIA translation and back-translation. | Preserve rejected-candidate details from bootstrapping failures. |
| Data learning | Mature behavior/data candidates. | Partial BV support through `DataLearner2`, `Bv2LiaTranslator`, and `Lia2BvTranslator`. | Feed data-learned candidates through the same rejection/guarding pipeline. |
| Candidate propagation | Implemented in LIA V3/V4. | Not fully wired through the BV translated-candidate loop. | Implement relation-aware propagation for guarded BV candidates. |
| MBP and phase features | V4 supports MBP/phase options. | MBP-guided BV data learning and SyGuS grammar seeding exist in pieces. | Make MBP guards first-class interval/refinement sources. |
| Candidate rejection | Failed/deferred candidates affect sampling priorities. | BV candidates are weakened/dropped without persistent failure records. | Add a rejected-candidate registry with countermodels and inferred guards. |
| Serialization | CHC serialization exists. | BV serialization exists but needs external-solver hardening. | Emit deterministic, solver-compatible BV/Horn SMT-LIB. |
| Counterexamples | `expl` handles many CHC CEX cases. | BV CCEX validation and SyGuS CEX synthesis exist. | Add LIA-CEX-to-BV translation and validated CEX flow. |

## Target architecture

The target BV implementation should treat overflow as a refinement boundary:

1. Learn a candidate in LIA.
2. Translate it to BV.
3. Validate against the original BV CHCs.
4. If validation fails, record the failure with a model and rule context.
5. Infer the smallest useful interval or no-overflow guard that explains when the
   candidate is sound.
6. Retry the guarded candidate.
7. Propagate guarded candidates across CHC relations.
8. If the abstraction produces a CEX, translate it to BV/CCEX and validate it.

The implementation should avoid making overflow guards a silent fallback. Every
guarded retry should be traceable to a failed candidate, a rule, and a validation
result.

## Phase overview

1. [Phase 0: Baseline and invariants](plans/phase-0-baseline.md)
2. [Phase 1: BV serialization for external solvers](plans/phase-1-serialization.md)
3. [Phase 2: Rejected-candidate tracking](plans/phase-2-rejected-candidates.md)
4. [Phase 3: Interval and overflow analysis](plans/phase-3-interval-overflow.md)
5. [Phase 4: Guarded candidate retry loop](plans/phase-4-guarded-retry.md)
6. [Phase 5: LIA-to-BV validated counterexamples](plans/phase-5-lia-bv-vcex.md)
7. [Phase 6: CHC candidate propagation](plans/phase-6-chc-propagation.md)
8. [Phase 7: Integration, evaluation, and defaults](plans/phase-7-integration.md)

The small BV regression suite lives in [`benchmarks/`](benchmarks/) and should be
run before and after behavior-changing changes, especially Phase 4 guarded retry.

## Cross-cutting requirements

- Keep the original BV system as the validation authority.
- Make all BV/LIA translation maps explicit at interfaces that consume translated
  candidates or CEXs.
- Do not accept a guarded candidate unless the guarded candidate is checked in BV.
- Keep debug output useful but gated by existing debug levels or new explicit flags.
- Add narrow regression benchmarks for each feature as it lands.
- Preserve current CLI behavior unless a new option explicitly enables a behavior.
