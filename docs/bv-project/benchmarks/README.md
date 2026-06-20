# BV Benchmark Set

This is a small regression-oriented benchmark set for tracking BV roadmap
progress. It is not meant to be exhaustive; it keeps a stable mix of solved
examples, hard arithmetic examples, and rejected-candidate/overflow examples so
we can see when an implementation change solves something new.

## Current observation

The Phase 3 interval/overflow work is observational only. It adds debug hints
for rejected candidates, but it does not change solver decisions. The first
Phase 4 guarded-retry slice is opt-in and generates guarded candidates, but it
does not yet solve additional benchmarks in this suite.

The first BV-native template slice is also opt-in. With
`--bv-bitmask-templates=basic`, `bv_neg_01`, `bv_cmp_01`, `bv_add_01`,
`bv_add_02`, and `bv_mul_01` move from `unsolved`/`timeout` to `solved` by
adding one-hot, prefix-cover, prefix-equality, prefix-arithmetic mask, and
modular multiplication-accumulator invariants directly to BV validation before
the expensive LIA loop.

## Benchmark groups

| Benchmark | Group | Current baseline expectation | Why it is included |
| --- | --- | --- | --- |
| `bench_horn_bv/bv_small_01.smt2` | solved-smoke | solved | Fast success path for BV-to-LIA bootstrapping and BV validation. |
| `bench_horn_bv/bv_simp_01.smt2` | solved-smoke | solved | Fast signed/unsigned comparison-shaped invariant. |
| `bench_horn_bv/bv_cmp_01.smt2` | bitmask-win | timeout by default, solved with `--bv-bitmask-templates=basic` | Boolean prefix-equality invariant over masked bits. |
| `bench_horn_bv/bv_add_01.smt2` | bitmask-win | timeout by default, solved with `--bv-bitmask-templates=basic` | Prefix addition invariant over accumulated low bits and carry. |
| `bench_horn_bv/bv_add_02.smt2` | bitmask-win | timeout by default, solved with `--bv-bitmask-templates=basic` | Prefix subtraction invariant over accumulated low bits and borrow. |
| `bench_horn_bv/bv_neg_01.smt2` | bitmask-win | unsolved by default, solved with `--bv-bitmask-templates=basic` | One-hot/prefix-cover bit-mask invariant. |
| `bench_horn_bv/bv_mul_01.smt2` | template-win | unsolved by default, solved with `--bv-bitmask-templates=basic` | Modular multiplication-accumulator invariant for repeated addition. |
| `bench_horn_bv/bv_mod_01.smt2` | arithmetic-hard | unsolved | Modulo case for checking that arithmetic improvements do not regress. |

## Running

From the repository root:

```sh
docs/bv-project/benchmarks/run-bv-suite.sh
```

The runner writes logs outside the repository by default and prints a TSV table:

```text
benchmark	group	expectation	status	exit_code	seconds	guard_hints	log
```

To capture Phase 3 guard diagnostics, run with debug guards enabled:

```sh
BV_BENCH_DEBUG_GUARDS=1 BV_BENCH_TIMEOUT=35 docs/bv-project/benchmarks/run-bv-suite.sh
```

To check opt-in Phase 4 guarded retry:

```sh
BV_BENCH_DEBUG_GUARDS=1 BV_BENCH_TIMEOUT=35 docs/bv-project/benchmarks/run-bv-suite.sh --bv-overflow-guards=retry
```

To check opt-in BV-native bit-mask templates:

```sh
BV_BENCH_TIMEOUT=35 docs/bv-project/benchmarks/run-bv-suite.sh --bv-bitmask-templates=basic
```

Additional command-line arguments are forwarded to `freqhorn` before each
benchmark path.

Useful environment variables:

| Variable | Default | Purpose |
| --- | --- | --- |
| `FREQHORN_BIN` | `build/tools/deep/freqhorn` | Binary to run. |
| `BV_BENCH_TIMEOUT` | `30` | Per-benchmark timeout in seconds. |
| `BV_BENCH_OUT_DIR` | `/tmp/aeval-bv-benchmarks/<timestamp>-<pid>` | Directory for logs. |
| `BV_BENCH_DEBUG_GUARDS` | unset | When set to `1`, runs with `--debug 5` and reports guard hints. |

## Reading results

Any transition from `unsolved` or `timeout` to `solved` is a candidate new win.
For BV-native templates, `bv_neg_01`, `bv_cmp_01`, `bv_add_01`, `bv_add_02`,
and `bv_mul_01` are expected wins. If a solved-smoke or template-win benchmark
regresses to `unsolved` or `timeout`, treat it as a blocking regression.
