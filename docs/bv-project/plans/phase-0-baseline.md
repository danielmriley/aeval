# Phase 0: Baseline and Invariants

## Goal

Create a stable reference point before changing the BV implementation. This phase
should not alter solver behavior except for diagnostics that are explicitly gated by
debug flags.

## Code areas to inspect

- `tools/deep/DeepHorn.cpp`
- `include/deep/BitHorn.hpp`
- `include/deep/Horn.hpp`
- `include/deep/BndExpl.hpp`
- `include/simpl/Bv2Lia.hpp`
- `include/simpl/Lia2Bv.hpp`
- `include/deep/RndLearnerV3.hpp`
- `include/deep/RndLearnerV4.hpp`
- `include/deep/DataLearner2.hpp`
- `include/sampl/SeedMiner.hpp`

## Implementation steps

1. Inventory current CLI flags:
   - `--v5`
   - `--lia2bv`
   - `--serialize`
   - `--serialize-translation`
   - `--ccex`
   - `--use-ccex-inductive`
   - `--use-ccex-unrolling`
   - `--sygus`
   - `--sygus-tr`
   - `--sygus-full`
   - `--sygus-run`
   - `--sygus-validate`
   - `--sygus-ccex`
   - `--sygus-mbp`
   - `--sygus-invariants`
2. Record which paths are wired and which flags are parsed but unused.
3. Pick a minimum benchmark suite:
   - one safe BV CHC from `bench_horn_bv`
   - one translated BV benchmark from `bench_horn_bv_translated`
   - one BV CEX benchmark from `bench_horn_ccex` or `bench_horn_bv_cex`
   - one VCEX benchmark from `vcex_horn_benchmarks`
4. Capture baseline outputs for:
   - `freqhorn --v5 <safe-bv.smt2>`
   - `freqhorn --v5 --serialize <bv-or-lia.smt2>`
   - `freqhorn --sygus-tr --sygus-run --sygus-validate <bv-cex.smt2>` when CVC5 is available
   - `freqhorn --v5 --ccex <ccex.smt2> <bv-system.smt2>`
5. Define a small set of invariants that future phases must preserve:
   - original BV CHCs are never overwritten by translated LIA CHCs
   - translated candidates are always checked against the original BV rules
   - each relation map must preserve source relation, destination relation, and variable order
   - CEX validation must report false/unknown instead of silently accepting incomplete data
6. Add debug-level diagnostics only where they reveal existing behavior:
   - selected main relation in TR mode
   - BV width detected for each relation
   - number of translated rules and declarations
   - whether candidate propagation is skipped or unavailable

## Methods

- Prefer small helper functions over inline debug logic when a diagnostic is used in
  more than one path.
- Keep diagnostics behind existing `debug` checks unless a new flag is necessary.
- Do not change solver decisions in this phase.

## Acceptance criteria

- The chosen baseline commands are documented in a commit or test note.
- No existing benchmark result changes unless the change is explained as a pre-existing
  bug in diagnostics.
- `--help` output accurately reflects flags that are already available.
- Later phases have a stable list of commands for regression checks.

