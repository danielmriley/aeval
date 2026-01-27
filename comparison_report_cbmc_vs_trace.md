# CBMC vs Trace Extraction Tool Comparison Report (CORRECTED)

## 1. Executive Summary

This report compares the performance of CBMC (C Bounded Model Checker) against our internal Trace Extraction Tool on the `s_split` benchmark suite (58 C programs).

**Correction Note**: A previous version of this report incorrectly classified "Unwinding Assertion Failures" as successes for CBMC. This version filters those out, providing a strict "target reached" verification.

**Key Findings:**
- **Trace Solution Rate:** The Trace Extraction Tool (at 32-bit width) solved **44/58 (76%)** benchmarks.
- **CBMC Solution Rate:** CBMC (with 20,000 unwind limit) solved **25/58 (43%)** benchmarks.
- **Comparison:** Our tool significantly outperforms CBMC on this suite, solving **19 more benchmarks**.
- **Performance:** For benchmarks solved by both, CBMC remains faster (avg **0.6s**), but its inability to handle deep loops (exceeding the static unwind limit) severely restricts its coverage.

## 2. Methodology

### CBMC Configuration
- **Version:** 6.8.0
- **Unwind Limit:** 20,000 (fixed)
- **Timeout:** 300 seconds
- **Memory Limit:** 8GB
- **Strict Success Criterion:** A benchmark is considered "solved" ONLY if CBMC reports `VERIFICATION FAILED` **AND** the failure is due to a property violation (reachability), **NOT** an unwinding assertion failure.

### Trace Extraction Tool Configuration
- **Bitwidth:** 32-bit
- **Criterion:** A benchmark is considered "solved" if the tool reports `Success` and produces a trace.

## 3. Detailed Results

### 3.1 Overall Success Rates

| Tool | Solved | Success Rate |
| :--- | :---: | :---: |
| **Trace Extraction Tool** | **44** | **76%** |
| **CBMC** | 25 | 43% |

### 3.2 Intersection Analysis

- **Solved by Both (25):** `s_split_01`, `s_split_02`, `s_split_09`, `s_split_10`, `s_split_14`, `s_split_15`, `s_split_18`, `s_split_19`, `s_split_21`, `s_split_29`, `s_split_30`, `s_split_36`, `s_split_37`, `s_split_39`, `s_split_40`, `s_split_41`, `s_split_44`, `s_split_46`, `s_split_48`, `s_split_49`, `s_split_52`, `s_split_53`, `s_split_54`, `s_split_55`, `s_split_57`
- **Solved ONLY by Trace Tool (19):** 
    - *Deep Loops (>20k steps):* `s_split_04`, `s_split_06`, `s_split_08`, `s_split_12`, `s_split_16`, `s_split_20`, `s_split_22`, `s_split_38`, `s_split_42`, `s_split_43`, `s_split_45`, `s_split_50`, `s_split_51`
    - *Timeouts:* `s_split_03`, `s_split_05`, `s_split_07`, `s_split_13`, `s_split_32`, `s_split_56`
- **Solved ONLY by CBMC (0):**
    - There are **ZERO** benchmarks that CBMC solved which our tool failed.
    - Previous candidates (`s_split_11`, `s_split_17`, `s_split_47`) were actually Timeouts or other failures in CBMC.

## 4. Deep Dive: The "Unwinding" Fallacy
Many benchmarks previously thought to be solved by CBMC were actually failures of the unwinding validity.
Example: **`s_split_38`**
- **Trace Tool Trace:** 50,200 steps.
- **CBMC Unwind Limit:** 20,000 steps.
- **CBMC Outcome:** `VERIFICATION FAILED` (Unwinding Assertion).
- **Interpretation:** CBMC successfully proved that the loop runs more than 20,000 times, but it **failed** to check the actual error condition (which happens at step 50,000).

## 5. Conclusion
The Trace Extraction Tool is the clear winner for this benchmark suite.
- **Coverage:** 1.7x better than CBMC (44 vs 25).
- **Depth:** Can handle traces significantly deeper than standard model checking limits (e.g. 50k+ steps).
- **Recommendation:** Do not rely on CBMC alone for deep reachability problems unless the loop bounds are known small.
