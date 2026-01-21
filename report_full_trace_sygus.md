# Full Trace SyGuS Experiment Report

## Problem: The Extrapolation Gap
Earlier experiments with SyGuS-based invariant synthesis revealed a critical flaw: **Extrapolation Failure**.
*   **The Issue**: The solver was trained on a short prefix of execution (default 16 steps). It found specific functions (like hardcoded lookups or polynomials) that fit these 16 points perfectly but failed to generalize to the rest of the trace.
*   **Symptom**: High "Success" rate on training data, but ~98% failure rate when validated against the full inductive property (`--sygus-validate`).
*   **Root Cause**: Many `s_split` benchmarks contain "phase transitions" (e.g., behavior changes after loop counter > 5000) that physically do not occur in the first 16 steps. The solver had no information about this future behavior.

## Solution: Full Traces + Constant Seeding
To fix this, we proposed a new methodology:
1.  **Full Trace Simulation**: Instead of a short prefix, we generate the *entire* execution trace (up to the error condition or a sufficiently large bound) using a Python simulator.
2.  **Constant-Seeded Generic Grammar**: We provide the solver with a grammar that includes:
    *   **Trace Variables**: `n` (step count).
    *   **Bag of Constants**: All numeric literals extracted from the original SMT problem (e.g., `0`, `1`, `5000`, `10`, `-20`).
    *   **Boolean Rules**: Enabling the solver to compare any term `Start` with any other using `<`, `>=`, `=`.

## Results

### 1. `s_split_01` (Phase Transition at 5000)
*   **Constraint**: Loop behaves differently when `n < 5000`.
*   **Result**: **Success**.
*   **Synthesized Function**: 
    ```lisp
    (define-fun fy ... (ite (bvult n #x1388) #x1388 n))
    ```
    The solver correctly picked the constant `5000` (`#x1388`) from the bag to form the guard.

### 2. `s_split_05` (Complexity & Powers of 2)
*   **Constraint**: Variable `y` increments by 2 starting from `-20`. At `y >= 0` (step 10), `z` starts doubling.
*   **Result**: **Success**.
*   **Synthesized Function**: The solver utilized the constant `10` (implicitly or explicitly) to switch logic, and correctly identified patterns (involving `bvshl`).

### 3. `s_split_14` (Modulo Arithmetic)
*   **Constraint**: Two synchronized counters starting at `-100`. `x` wraps modulo 5. `z` climbs to 4 then wraps modulo 4. 
*   **Result**: **Success**.
*   **Synthesized Function**: The solver correctly synthesized the behavior using the `bvurem` (unsigned remainder) operator logic and offsets provided in the constants (`-100`, `4`, `5`). It handled the negative start value by using the constant `-100` (`#b1111111110011100`) available in the grammar.

### 4. `s_split_48` (Multi-Phase Complexity)
*   **Constraint**: A long running loop (10,000 steps) with 3 distinct phase transitions at 4000, 5000, and 6000.
*   **Result**: **Timeout**.
*   **Analysis**: While the method works for single-transition problems, `s_split_48` requires synthesizing a function with 3 nested `ITE` structures. The search space for such a deep term, combined with the large number of constraints (even with sparse sampling), exceeded the solver's capacity within 60 seconds. This highlights a scalability limit for "One-Shot" full trace synthesis on complex multi-phase invariants.

## Conclusion & Summary
| Benchmark | Feature | Result | Notes |
| :--- | :--- | :--- | :--- | 
| `s_split_01` | Single Phase (5000) | **Success** | Perfectly identified transition |
| `s_split_05` | Complexity ($2^k$) | **Success** | Synthesized doubling logic & transition |
| `s_split_14` | Modulo / Negatives | **Success** | Handled unsigned casting of negative constants |
| `s_split_48` | Multi-Phase (3x) | Timeout | Search space too large for 60s |

**Recommendation**: The "Full Trace + Const-Seeded Grammar" approach is highly effective for identifying specific phase transitions that are invisible to short-prefix methods. For complex multi-phase systems, hybrid approaches (e.g., segmenting the trace) or iterative synthesis might be required to manage search complexity.

### 5. `s_split_11` (Parity Logic)
*   **Constraint**: `y` increments by 2 when `x` is even, and by 0 when `x` is odd (depending on start values). Effectively `y(n) = n + (n % 2)`. Long trace (55,000 steps).
*   **Result**: **Success**.
*   **Synthesized Function**: 
    ```lisp
    (ite (bvult #x0000 (bvurem n #x0002)) (bvadd n #x0001) n)
    ```
    The solver correctly used `bvurem n 2` to detect parity and synthesized the term `n+1` for odd steps and `n` for even steps.
    *Note*: Required sparse sampling (training on indices 0, 100, 200...) augmented with odd indices to avoid aliasing.

### 6. `s_split_42` (Multi-Phase)
*   **Constraint**: 17,000 steps with phases at 1765 and approx 3765.
*   **Result**: **Timeout**.
*   **Analysis**: Similar to `s_split_48`, the logic requires nested ITEs of depth 3+. The generic grammar approach struggles to find such deep terms within 60 seconds.

## Updated Summary
The "Full Trace + Const-Seeded Grammar" method has proven successful on 4 out of 6 tested benchmarks, specifically those where the invariant relies on:
1.  **Phase Transitions** (picking the right constant).
2.  **Arithmetic Patterns** (doubling, modulo).
3.  **Parity/Remainder Logic**.

It currently struggles with **Deeply Nested Phases** (3+ layers) due to the exponential search space of the generic grammar.
