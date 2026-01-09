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

### Options

| Option | Description |
|--------|-------------|
| `--sygus [file]` | Generate a SyGuS file for CVC5 counterexample synthesis (default: `counterexample.sygus`) |
| `--sygus-points <N>` | Number of trace points to collect (default: auto, based on state bitwidth) |
| `--sygus-bitwidth <N>` | Bit-width for the step parameter (default: auto, based on state bitwidth) |
| `--sygus-run` | Run CVC5 on the generated SyGuS file and display synthesized functions |
| `--sygus-validate` | Synthesize, generate CCEX file, and validate inductively |
| `--sygus-ccex <file>` | Output CCEX file from synthesis (for manual validation) |

### Examples

**Generate SyGuS file only:**
```bash
freqhorn --sygus output.sygus bench_horn_ccex/cex1_zext/bvzext4_cex1.smt2
```

**Synthesize and display functions:**
```bash
freqhorn --sygus --sygus-run --sygus-points 32 bench_horn_ccex/cex1_zext/bvzext4_cex1.smt2
```

**Full pipeline (synthesize + validate):**
```bash
freqhorn --sygus --sygus-run --sygus-validate --sygus-points 64 --sygus-bitwidth 16 \
    bench_horn_ccex/cex2_zext/bvzext4_cex2.smt2
```

### How It Works

1. **Trace Simulation**: Simulates the CHC transition system for N steps, collecting input-output examples for each state variable
2. **SyGuS Generation**: Creates a SyGuS file with bitvector grammar constraints for CVC5
3. **Synthesis**: CVC5 synthesizes closed-form functions `f(step)` that match the trace data
4. **CCEX Generation**: Converts synthesized functions to a compact counterexample (CCEX) format
5. **Inductive Validation**: Validates the CCEX using 3 checks:
   - **Init**: `f(0)` satisfies the initial constraint
   - **Transition**: `f(i) ∧ trans ⟹ f(i+1)` is valid
   - **Property**: `f(N)` reaches the error state

Benchmarks
==========

Collection of the SMT-LIB2 translations of the satisfiable CHC system can be found at `bench_horn` and `bench_horn_multiple`. FreqHorn is expected to eventually discover solutions for the systems. On the other hand, there are several unsatisfiable CHC systems at `bench_horn_cex`, for which `freqhorn` is expected to diverge (but `expl` should find counterexamples).

