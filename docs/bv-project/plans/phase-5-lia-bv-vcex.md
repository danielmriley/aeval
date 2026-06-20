# Phase 5: LIA-to-BV Validated Counterexamples

## Goal

Extend the counterexample flow so a CEX found in the LIA abstraction can be translated
to BV and validated as a CCEX/validated CEX.

## Current starting points

- `BndExpl::validateCEXInductive`
- `BndExpl::validateCEX`
- `CHCs::generateCounterexampleSyGuS`
- `CHCs::generateCounterexampleSyGuSTR`
- `CHCs::generateCCEXFromSynthesis`
- `BitHorn::translateToLia`
- `Lia2BvTranslator`
- `vcex_horn_benchmarks`

## Terminology

Use `CCEX` for the file format already present in the codebase. Treat `VCEX` as the
validated result:

```text
LIA CEX -> translated BV CCEX -> BV validation -> VCEX result
```

Do not introduce a separate VCEX file format unless a concrete downstream consumer
requires it.

## Implementation steps

1. Define accepted LIA CEX sources:
   - BndExpl trace over translated LIA CHCs
   - SyGuS-synthesized closed-form functions over LIA variables
   - external LIA CEX file if serialization enables one
2. Preserve translation maps:
   - BV relation to LIA relation
   - BV variable to LIA variable
   - original BV width per variable
   - signedness assumptions used during translation
3. Add a LIA CEX representation:
   - trace bounds
   - relation
   - value functions or per-step values
   - variable order
   - source metadata
4. Translate LIA CEX values to BV:
   - integer value `n` maps to `n mod 2^w`
   - negative values use two's-complement representation
   - reject values when signedness assumptions make validation ambiguous unless a flag allows wrapping
5. Generate CCEX:
   - reuse `generateCCEXFromSynthesis` where functions already exist
   - add a trace-to-CCEX writer if the LIA CEX is point-based
   - include comments describing LIA source and BV width
6. Validate with original BV CHCs:
   - call `validateCEXInductive` by default
   - optionally call unrolling validation when requested
   - report SAT/UNSAT/UNKNOWN clearly
7. If validation fails:
   - identify whether the failure is init, transition, or property
   - feed the failure back into interval/overflow analysis
   - do not report a LIA CEX as a real BV CEX
8. Add CLI flow:
   - `--lia-cex-to-bv <file>` or equivalent
   - `--validate-lia-cex-as-bv`
   - output path for generated CCEX
9. Add integration with SyGuS:
   - when `--lia2bv` and `--sygus-validate` are both set, make the validation path explicit
   - avoid double translation if the input is already BV

## Methods

- Make original BV CHCs the only source of truth for final CEX validity.
- Do not silently wrap LIA values without recording the width and rule used.
- Use existing CCEX parser/validator before inventing a new validator.
- Keep point-based and closed-form CEX paths separate until they share a stable
  representation.

## Files likely to change

- `tools/deep/DeepHorn.cpp`
- `include/deep/BitHorn.hpp`
- `include/deep/BndExpl.hpp`
- `include/deep/Horn.hpp`
- `include/simpl/Lia2Bv.hpp`

## Tests and benchmarks

1. A LIA CEX that translates to a valid BV CCEX is accepted.
2. A LIA CEX that relies on invalid integer semantics is rejected by BV validation.
3. Negative LIA values translate to expected BV constants.
4. Bounds inferred during validation update the generated CCEX when applicable.
5. Existing BV CCEX validation still works.

## Acceptance criteria

- The tool never reports a LIA CEX as a BV CEX until BV validation succeeds.
- Generated CCEX files can be loaded by the existing validator.
- Validation failures are actionable inputs for overflow refinement.

