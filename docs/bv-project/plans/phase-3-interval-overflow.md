# Phase 3: Interval and Overflow Analysis

## Goal

Infer intervals and no-overflow guards that explain when LIA candidates are sound
under BV semantics.

## Current starting points

- `Bv2LiaTranslator::addBitWidthBounds`
- `BitHorn::translateToLia`
- `BitHorn::generateMbpsBv`
- `BndExpl::extractMBPGuards`
- `Lia2BvTranslator::translateExpr`
- BV expression helpers in `include/ae/ExprSimplBv.hpp`

## Landed observational slice

The first Phase 3 implementation is attached to the Phase 2 rejected-candidate
registry in `BitHorn`.

For every rejected BV candidate, the debug-only record now includes:

1. interval-looking BV comparisons found in the failing rule body and candidate;
2. conservative unsigned no-overflow guard suggestions for binary `bvadd`;
3. per-relation interval/no-overflow guard counts at debug level 2 and full
   guard expressions at debug level 5;
4. no solver behavior changes and no mutation of the original BV CHCs.

The current unsigned `bvadd(a, b)` guard is emitted as:

```text
bvule(a, bvadd(a, b)) /\ bvule(b, bvadd(a, b))
```

This is sufficient as a diagnostic hint for why a LIA addition-shaped candidate
may fail under BV wraparound. Guarded retry and injection into the translated
system remain Phase 4 work.

## Core concepts

### Coarse bitwidth interval

For unsigned width `w`:

```text
0 <= x <= 2^w - 1
```

For signed width `w`:

```text
-2^(w - 1) <= x <= 2^(w - 1) - 1
```

These bounds already exist conceptually in `addBitWidthBounds`, but they are too
coarse to justify many LIA candidates.

### Operation-safe interval

For unsigned `a + b` at width `w`, a sufficient no-overflow guard is:

```text
0 <= a
0 <= b
a <= max
b <= max
a + b <= max
```

For signed addition:

```text
min <= a
min <= b
max >= a
max >= b
min <= a + b
a + b <= max
```

Subtraction and multiplication need analogous conservative guards. Start with
simple sufficient conditions before adding more precise formulas.

## Implementation steps

1. Add an interval representation:
   - variable expression
   - lower bound expression
   - upper bound expression
   - signedness
   - width
   - source: bitwidth, transition guard, MBP, model, learned invariant
2. Add an interval environment:
   - map from relation to variable intervals
   - map from rule to source/destination/local intervals
   - merge operation using intersection
   - pretty-printer for debug output
3. Seed intervals from bitwidths:
   - inspect relation variables
   - determine signedness from signed BV operators when possible
   - fall back to unsigned only when the current translator already does so
4. Extract intervals from transition guards:
   - `bvult x c` -> upper bound
   - `bvule x c` -> upper bound
   - `bvugt x c` -> lower bound
   - `bvuge x c` -> lower bound
   - signed comparisons -> signed lower/upper bounds
   - equality to constant -> exact interval
5. Extract intervals from LIA guards after BV-to-LIA translation:
   - reuse normalized comparisons in LIA form
   - map LIA variables back to BV variables through translator maps
6. Infer operation guards:
   - walk candidate expressions
   - find `BADD`, `BSUB`, `BMUL`, `BNEG`, shifts, extensions
   - produce conservative no-overflow constraints for arithmetic operations
   - skip operations that are bitwise-only and do not need LIA/BV arithmetic agreement
7. Tighten intervals from countermodels:
   - when a candidate fails with concrete model values, derive exclusion or guard hints
   - avoid overfitting to one model by intersecting with transition-derived intervals first
8. Add a flag design:
   - `--bv-overflow-guards=off|retry|always`
   - default `off` until Phase 7
   - `retry` is used by Phase 4
   - `always` injects guards into the translated transition system
9. Add simplification:
   - drop tautological full-range intervals
   - combine duplicate lower/upper bounds
   - reject contradictory intervals before they reach candidate validation

## Methods

- Prefer sound over precise. A conservative guard that loses candidates is acceptable;
  an unsound guard that accepts an invalid BV candidate is not.
- Keep signed and unsigned intervals separate unless an expression proves they agree.
- Do not add interval assumptions to original BV validation. Guards should become part
  of guarded candidates or translated abstraction, not mutate the original system.
- Treat multiplication guards as opt-in or conservative, because precise no-overflow
  multiplication constraints can grow quickly.

## Files likely to change

- `include/deep/BitHorn.hpp`
- `include/simpl/Bv2Lia.hpp`
- `include/simpl/Lia2Bv.hpp`
- `include/ae/ExprSimplBv.hpp`
- possibly a new `include/deep/BvInterval.hpp`

## Tests and benchmarks

1. Extract interval from `bvule x #x0f`.
2. Extract signed interval from `bvsle x #x7f`.
3. Infer no-overflow guard for `bvadd a b`.
4. Do not infer arithmetic guards for `bvand`, `bvor`, `bvxor`.
5. Contradictory intervals are detected and not used.

## Acceptance criteria

- The implementation can produce interval/no-overflow guards without changing solver
  decisions by default.
- Interval output is deterministic and debug-gated.
- Guards are expressible both as LIA constraints and BV candidate guards.
