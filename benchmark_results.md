# Benchmark Results Summary - SyGuS PBE vs TR Mode

Tests run with 60s timeout, up to 64-bit width.

## Overview
| Mode | Success | Infeasible | Timeout | Fail |
|------|---------|------------|---------|------|
| PBE  | ~85%    | 0%         | ~15%    | 0%   |
| TR   | ~60%    | 1%         | ~35%    | 4%   |

## Detailed Comparison

| Category | Benchmark | PBE Status | TR Status | Notes |
|----------|-----------|------------|-----------|-------|
| Standard | cex1, cex2, etc. | **SUCCESS** (<0.2s) | **SUCCESS** (<0.1s) | Both highly effective on simple counter examples |
| ZExt | cex*_zext* | **SUCCESS** | **SUCCESS** | PBE handles bit-extension well, TR also works but gets slower at high bitwidths (e.g. 64-bit takes ~11s) |
| Alternating | bv*_alt | **SUCCESS** (~1.5s) | **TIMEOUT** (>60s) | PBE learns `ite` pattern easily; TR struggles with quantifier |
| Gray Code | bv*_gray | **SUCCESS** (~0.12s) | **TIMEOUT** (>60s) | PBE finds `i ^ (i >> 1)` instantly; TR times out proving universal validity |
| Polynomial | bv*_poly | **TIMEOUT** | **TIMEOUT** | `x = i^2` hard for both; PBE fails to find pattern from points |
| Saturation | bv*_sat | **SUCCESS** (~0.12s) | **TIMEOUT** (>60s) | PBE finds `min` logic; TR times out |
| Non-Det Branch | nd_branch | **SUCCESS** (varies) | **TIMEOUT** | PBE handles branching traces; TR fails |
| ND CEX1 ZExt | nd_cex1_zext | **TIMEOUT** | **SUCCESS** (<0.05s) | **Winner: TR**. PBE gets stuck (likely overfitting or confusing trace); TR solves standard increment easily |
| ND Mixed | nd_mixed | **SUCCESS** | **SUCCESS** | Both work well |
| ND Reset | nd_reset | **Mixed** (Timeout/Success) | **SUCCESS** (<0.05s) | **Winner: TR**. PBE struggles with reset logic traces; TR handles it easily |

## Key Findings

1. **Complementary Strengths**: 
   - **PBE** is superior for finding "tricky" arithmetic/logical functions (Gray code, Alternating) where the pattern is complex but defined on a simple trace.
   - **TR** is superior for "structural" behaviors (Resets, simple Non-Determinism) where the function is simple but the trace might be confusing or hard to enumerate effectively.

2. **Performance**:
   - PBE is generally constant time (fast) regardless of bitwidth.
   - TR performance degrades with bitwidth (e.g., 64-bit ext took 14s vs 0.05s for 8-bit).

3. **Recommendations**:
   - Use **PBE** as the default mode for fast counterexample discovery.
   - Fallback to **TR** if PBE fails, especially for systems with resets or simple non-determinism.
