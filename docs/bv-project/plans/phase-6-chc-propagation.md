# Phase 6: CHC Candidate Propagation

## Goal

Move BV support beyond transition-relation-shaped systems by propagating candidates,
guards, and failure information across multi-relation CHC graphs.

## Current starting points

- `RndLearnerV3::propagate`
- `RndLearnerV3::propagateRec`
- `RndLearnerV4`
- `CHCs::cycles`
- `CHCs::wtoDecls`
- `CHCs::wtoCHCs`
- `BndExpl::compactPrefix`
- `BitHorn::solveLIA`
- `BitHorn::translateSolutionToBv`

## Design requirements

- Propagation must preserve relation-specific variable order.
- Guards must be renamed when they move from one relation to another.
- A candidate that is guarded for one rule may need a different guard for another rule.
- Query/fail relations must not receive invariant candidates.
- Propagation must work for both acyclic prefixes and cycles.

## Implementation steps

1. Define propagated candidate metadata:
   - source relation
   - destination relation
   - source rule
   - candidate expression
   - guard expression
   - translation map used
   - propagation direction: forward, backward, both
2. Reuse LIA propagation where sound:
   - propagate in LIA abstraction first
   - translate propagated candidate and guard back to BV
   - validate against the target BV relation
3. Add BV-specific propagation checks:
   - rename source variables to destination variables
   - preserve primed/unprimed distinction
   - recompute no-overflow guards for the target rule
4. Integrate with rejected-candidate registry:
   - failures during propagation should produce rejected records
   - failure source should be `propagated`
   - retry guarded propagation only after interval analysis succeeds
5. Add guarded propagation:
   - propagate `G => C`, not only `C`
   - strengthen or weaken `G` when crossing rules
   - avoid dropping `G` unless the target rule proves it
6. Handle multiple relations:
   - initialize candidate buckets for every `wtoDecl`
   - skip `failDecl` and `true`
   - support multiple invariant declarations in one BV system
7. Handle multiple cycles:
   - process WTO order
   - use existing cycle information for propagation scheduling
   - prevent infinite propagation loops with visited keys
8. Add CLI controls:
   - reuse existing `--prop <N>` for BV if possible
   - add debug output when BV propagation is skipped
   - document differences from LIA propagation if any
9. Extend SyGuS CEX beyond TR shape:
   - identify relation paths from init to query
   - synthesize per-relation functions or path-specific state functions
   - validate path-level CEX candidates with `BndExpl`

## Methods

- Start with propagation in the safety proof path before generalizing SyGuS CEX.
- Keep propagation opt-in until benchmarks show it is stable.
- Validate every propagated BV candidate at the destination relation.
- Make variable renaming helpers shared and tested; do not duplicate ad hoc string
  comparisons across propagation code.

## Files likely to change

- `include/deep/BitHorn.hpp`
- `include/deep/RndLearnerV3.hpp`
- `include/deep/RndLearnerV4.hpp`
- `include/deep/BndExpl.hpp`
- possibly new helper headers for candidate metadata and relation maps

## Tests and benchmarks

1. Two-relation CHC where a candidate learned at one relation must propagate to another.
2. A propagated candidate that needs a renamed guard.
3. A propagation failure recorded as a rejected propagated candidate.
4. A multi-cycle CHC where visited tracking prevents loops.
5. Existing single-relation TR benchmarks still work.

## Acceptance criteria

- BV `--prop` has a real effect or explicitly reports why it is unavailable.
- Propagated candidates are validated in BV before being accepted.
- Guard metadata survives propagation.
- General CHC support no longer depends on only one self-loop relation.

