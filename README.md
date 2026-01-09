FreqHorn
========

Satisfiability solver for constrained Horn clauses (CHC) based on <a href="https://github.com/Z3Prover/z3">Z3</a> SMT solver. It combines syntax-guided methods to inductive invariant synthesis with data learning and quantified reasoning over arrays. Find more details at <a href="http://www.cs.fsu.edu/~grigory/freqhorn-arrays.pdf">CAV'19</a> and <a href="http://www.cs.fsu.edu/~grigory/multi-freqhorn.pdf">FMCAD'18</a> papers.

Installation
============

Compiles with gcc-7 (on Linux) and clang-1001 (on Mac). Assumes preinstalled <a href="https://gmplib.org/">GMP</a>, and Boost (libboost-system1.74-dev) packages. Additionally, armadillo package to get candidates from behaviors. 

* `cd aeval ; mkdir build ; cd build`
* `cmake ../`
* `make` to build dependencies (Z3)
* `make` (again) to build FreqHorn

The binary of FreqHorn can be found at `build/tools/deep/`.
Run `freqhorn --help` for the usage info.

FreqHorn does not automatically find counterexamples (unless the CHC system can be trivially simplified), but its supplementary tool `expl` tool does. We recommend running `freqhorn` and `expl` concurrently.

The tools print `Success ...` if the system is satisfiable.

SyGuS Counterexample Synthesis
==============================

FreqHorn includes a SyGuS-based counterexample synthesis pipeline for bitvector CHC systems. This feature uses CVC5 to synthesize closed-form functions that represent counterexample traces, then validates them inductively.

### Prerequisites

Requires <a href="https://cvc5.github.io/">CVC5</a> to be installed and available in PATH.

### Usage

```bash
freqhorn --sygus [file] --sygus-run --sygus-validate [options] <input.smt2>
```

### Synthesis Modes

There are two SyGuS generation modes:

- **PBE (Point-Based Enumeration)**: `--sygus` - Collects concrete trace points and synthesizes a function that fits them. Good for discovering complex patterns from examples.

- **TR (Transition Relation)**: `--sygus-tr` - Encodes the init constraint and a universal transition constraint. No unrolling required, works well for any bitwidth including 64-bit systems.

### Options

| Option | Description |
|--------|-------------|
| `--sygus [file]` | Generate SyGuS file using PBE mode (default: `counterexample.sygus`) |
| `--sygus-tr [file]` | Generate SyGuS file using TR mode (no unrolling needed) |
| `--sygus-points <N>` | Number of trace points for PBE mode (default: 16) |
| `--sygus-bitwidth <N>` | Bit-width for the step parameter (default: auto) |
| `--sygus-run` | Run CVC5 on the generated SyGuS file |
| `--sygus-validate` | Synthesize, generate CCEX file, and validate inductively |
| `--sygus-ccex <file>` | Output CCEX file from synthesis |

### Examples

**PBE mode (point-based):**
```bash
freqhorn --sygus --sygus-run --sygus-validate bench_horn_ccex/cex1_zext/bvzext4_cex1.smt2
```

**TR mode (transition relation) - recommended for large bitwidths:**
```bash
freqhorn --sygus-tr --sygus-run --sygus-validate bench_horn_ccex/cex1_zext/bvzext64_cex1.smt2
```

### How It Works

**PBE Mode:**
1. Simulates the transition system for N steps
2. Generates constraints: `(constraint (= (f_x 0) val_0))`, `(constraint (= (f_x 1) val_1))`, ...
3. CVC5 synthesizes a function that fits all points

**TR Mode:**
1. Extracts initial state values
2. Generates two constraints:
   - **C1**: `(constraint (= (f_x 0) init_val))`
   - **C2**: `(constraint (forall ((i BV)) (= (f_x (bvadd i 1)) (bvadd (f_x i) 1))))`
3. CVC5 synthesizes a function that satisfies both constraints

**Validation (both modes):**
- **Init check**: `f(0)` satisfies the initial constraint
- **Transition check**: `f(i) ∧ trans ⟹ f(i+1)` is valid
- **Property check**: `f(N)` reaches the error state

Benchmarks
==========

Collection of the SMT-LIB2 translations of the satisfiable CHC system can be found at `bench_horn` and `bench_horn_multiple`. FreqHorn is expected to eventually discover solutions for the systems. On the other hand, there are several unsatisfiable CHC systems at `bench_horn_cex`, for which `freqhorn` is expected to diverge (but `expl` should find counterexamples).

