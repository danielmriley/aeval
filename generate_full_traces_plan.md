# Plan for Generating Full Traces using BndExpl

## Overview
This plan outlines the integration of `BndExpl` (Bounded Exploration) into the `freqhorn` workflow to generate high-fidelity, solver-verified concrete counterexample traces. These traces will be exported as SyGuS 2.0 files for synthesis by CVC5.

## 1. Refactor Existing SyGuS Logic
Current SyGuS generation in [include/deep/Horn.hpp](include/deep/Horn.hpp) combines trace simulation and file writing. We will decouple these:

- **Action**: Extract the core SyGuS file-writing logic from `generateCounterexampleSyGuS` into a standalone helper method:
  ```cpp
  bool writeSyGuSFromTrace(
      const std::string& filename, 
      const std::vector<std::map<Expr, Expr>>& trace,
      const ExprVector& state_vars,
      int step_bitwidth);
  ```
- **Benefit**: Allows different trace generation backends (Simulation vs. BndExpl) to use the same validated grammar and formatting templates.

## 2. Enhance BndExpl for Concrete Trace Extraction
`BndExpl` currently finds SAT traces but only exposes the logical SSA form. We need to extract the concrete values from the solver's model.

- **Action**: Add a new method to [include/deep/BndExpl.hpp](include/deep/BndExpl.hpp):
  ```cpp
  bool extractConcreteTrace(
      std::vector<int>& traceIndices, 
      std::vector<std::map<Expr, Expr>>& outTrace);
  ```
- **Implementation Details**:
  1. Call `getSSA(traceIndices, ssa)` to build the bounded formula.
  2. Use `u.isSat(ssa)` to get a model.
  3. Iterate through `bindVars` (populated by `getSSA`) for each step.
  4. For each state variable $v$ at step $i$, call `u.getModel(bindVars[i][v])` to get the concrete bit-vector value.
  5. Store results in the `outTrace` mapping.

## 3. Tool Integration in DeepHorn.cpp
Update the command-line interface to allow users to trigger this high-fidelity mode.

- **Action**: Add a new flag `--sygus-full [filename]`.
- **Action**: Update the main loop to:
  1. Parse the input CHC file.
  2. Instantiate `BndExpl`.
  3. Call `exploreTraces` to find a legitimate counterexample path.
  4. Call the newly created `extractConcreteTrace`.
  5. Call `writeSyGuSFromTrace` to produce the final output.

## 4. Workflow Improvements
- **Accuracy**: Unlike the current simulation-based `--sygus` mode (which might fail to reach the bad state), this approach uses the solver to guarantee the trace actually violates the property.
- **Pattern Synthesis**: Providing CVC5 with a long, solver-verified trace (e.g., $100+$ steps) significantly improves its ability to synthesize correct "phase guards" and complex arithmetic transitions.
- **Validation**: Generated closed-form counterexamples can be validated using the existing `--sygus-validate` machinery, creating a complete end-to-end "Synthesize-and-Verify" loop.

## 5. Next Steps
1. Refactor [include/deep/Horn.hpp](include/deep/Horn.hpp) to expose the SyGuS writer.
2. Implement trace extraction in [include/deep/BndExpl.hpp](include/deep/BndExpl.hpp).
3. Connect the components in [tools/deep/DeepHorn.cpp](tools/deep/DeepHorn.cpp).
