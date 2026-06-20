# Phase 1: BV Serialization for External Solvers

## Goal

Make BV and translated BV systems reliably serializable so external solvers can be
used for comparison, debugging, and validation.

## Current starting points

- `CHCs::serialize(bool horn)` in `include/deep/Horn.hpp`
- `CHCs::serializeCHC()`
- `CHCs::serializeHorn()`
- `BitHorn::translateToBv()` in `include/deep/BitHorn.hpp`
- `--serialize` and `--serialize-translation` parsing in `tools/deep/DeepHorn.cpp`

## Landed quick win

`--serialize-translation` now has explicit BV behavior in the `--v5` path:

- BV input serializes the parsed BV CHC system to `chc.smt2`.
- LIA input requires `--lia2bv`, translates the system to BV, and serializes the
  translated BV CHCs to `chc.smt2`.
- LIA input without `--lia2bv` reports a clear error instead of silently continuing.

## Implementation steps

1. Define serialization modes:
   - original CHC serialization
   - BV CHC serialization using `declare-rel` and `rule`
   - translated LIA-to-BV serialization
   - BV-to-LIA abstraction serialization
2. Make `--serialize-translation` do one explicit thing:
   - if input is LIA and `--lia2bv` is set, write the translated BV system
   - if input is BV and a BV-to-LIA export flag is added, write the LIA abstraction
   - otherwise print a clear error instead of silently behaving like `--serialize`
3. Replace hard-coded output names where needed:
   - keep `chc.smt2` as a default for compatibility
   - add optional output path parsing if the project convention supports it
   - never overwrite unrelated files without an explicit output path or documented default
4. Normalize emitted BV expressions:
   - ensure n-ary BV operations are printed in solver-compatible binary form if required
   - print BV constants with width-correct hex or binary
   - declare all local variables used in rule bodies
   - avoid duplicate declarations for the same variable
5. Emit solver metadata:
   - set logic where appropriate
   - include comments with source file, mode, and translation width
   - keep comments optional if an external solver rejects them
6. Add round-trip smoke checks:
   - serialize a BV benchmark
   - load it with Z3 or the existing parser
   - compare number of declarations and rules
   - check that query/fail relation is preserved
7. Add external-solver compatibility checks:
   - Z3 fixedpoint parse
   - CVC5 parse if the serialized output targets CVC5-compatible syntax
   - graceful skip when a solver is not installed

## Methods

- Create a small serialization options struct rather than threading multiple booleans
  through `serialize`.
- Keep relation and variable ordering deterministic by iterating existing vectors
  instead of unordered sets where output order matters.
- Treat serializer failures as real errors with return values, not just debug output.
- Keep the original serializer behavior available until all call sites are migrated.

## Files likely to change

- `tools/deep/DeepHorn.cpp`
- `include/deep/Horn.hpp`
- `include/deep/BitHorn.hpp`
- possibly `include/ae/SMTUtils.hpp` or printer utilities if BV printing needs reuse

## Acceptance criteria

- Every serialization mode has a command-line path.
- Serialized files parse with at least the repository parser or a documented external solver.
- Existing `--serialize` users keep working.
- `--serialize-translation` no longer appears wired but unused.
