#!/usr/bin/env python3
"""
Comparison test script for CEX validation methods.
Runs inductive and unrolling-based validation separately with timeout.
"""

import subprocess
import re
import sys
import os
import time

FREQHORN = "/home/daniel/Projects/aeval/build/tools/deep/freqhorn"
BENCH_DIR = "/home/daniel/Projects/aeval/bench_horn_ccex"
TIMEOUT = 300  # 5 minutes per method

def run_test_method(bitwidth, method):
    """Run test for a given bitwidth with specific method."""
    chc_file = os.path.join(BENCH_DIR, f"bv{bitwidth}_cex1.smt2")
    ccex_file = os.path.join(BENCH_DIR, f"bv{bitwidth}_cex1_ccex.smt2")
    
    if not os.path.exists(chc_file) or not os.path.exists(ccex_file):
        return None, "FILES_MISSING"
    
    if method == "inductive":
        # Inductive only: default is inductive, disable unrolling (which is already off by default)
        cmd = [FREQHORN, "--bv", "--ccex", ccex_file, chc_file]
    else:  # unrolling
        # Unrolling only: enable unrolling, disable inductive
        cmd = [FREQHORN, "--bv", "--ccex", ccex_file, "--use-ccex-unrolling", "--no-ccex-inductive", chc_file]
    
    start_time = time.time()
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT)
        output = result.stdout + result.stderr
        elapsed = time.time() - start_time
    except subprocess.TimeoutExpired:
        return TIMEOUT * 1000, "TIMEOUT"
    
    # Parse timing
    timing = None
    if method == "inductive":
        match = re.search(r'\[Inductive Timing\].*Total: (\d+)ms', output)
        if match:
            timing = int(match.group(1))
    else:
        match = re.search(r'\[Timing\] Parse CEX:.*Total: (\d+)ms', output)
        if match:
            timing = int(match.group(1))
    
    # Check status
    if "Trace too long for unrolling" in output:
        return None, "TOO_LONG"
    elif "CEX VALID" in output:
        return timing, "VALID"
    elif "CEX INVALID" in output:
        return timing, "INVALID"
    else:
        return timing, "UNKNOWN"

def main():
    bitwidths = [4, 8, 16, 32, 64, 128, 256, 512]
    
    print("=" * 90)
    print(f"CEX Validation Comparison Test (Timeout: {TIMEOUT}s per method)")
    print("=" * 90)
    print(f"{'Bitwidth':<10} {'Trace Len':<15} {'Inductive (ms)':<18} {'Unrolling (ms)':<18} {'Faster'}")
    print("-" * 90)
    
    results = []
    
    for bw in bitwidths:
        trace_len = 2**bw + 1
        trace_str = f"{trace_len:,}" if trace_len < 1e12 else f"2^{bw}+1"
        
        print(f"{bw:<10} {trace_str:<15} ", end="", flush=True)
        
        # Run inductive
        ind_time, ind_status = run_test_method(bw, "inductive")
        ind_str = f"{ind_time}" if ind_time is not None else ind_status
        print(f"{ind_str:<18} ", end="", flush=True)
        
        # Run unrolling
        unr_time, unr_status = run_test_method(bw, "unrolling")
        unr_str = f"{unr_time}" if unr_time is not None else unr_status
        
        # Determine which is faster
        faster = "N/A"
        if ind_time is not None and unr_time is not None:
            if ind_time < unr_time:
                faster = "Inductive"
            elif unr_time < ind_time:
                faster = "Unrolling"
            else:
                faster = "Tie"
        elif ind_time is not None:
            faster = "Inductive"
        elif unr_time is not None:
            faster = "Unrolling"
        
        print(f"{unr_str:<18} {faster}")
        
        results.append({
            'bitwidth': bw,
            'trace_len': trace_len,
            'inductive_ms': ind_time,
            'inductive_status': ind_status,
            'unrolling_ms': unr_time,
            'unrolling_status': unr_status,
            'faster': faster
        })
        
        # Stop if both methods fail
        if ind_status in ["TIMEOUT", "FILES_MISSING"] and unr_status in ["TIMEOUT", "TOO_LONG", "FILES_MISSING"]:
            print(f"\nStopping at bv{bw} - both methods cannot complete within timeout.")
            break
    
    print("-" * 90)
    
    # Generate CSV for plotting
    csv_file = os.path.join(BENCH_DIR, "comparison_results.csv")
    with open(csv_file, 'w') as f:
        f.write("bitwidth,trace_len,inductive_ms,inductive_status,unrolling_ms,unrolling_status,faster\n")
        for r in results:
            ind = r['inductive_ms'] if r['inductive_ms'] is not None else ""
            unr = r['unrolling_ms'] if r['unrolling_ms'] is not None else ""
            f.write(f"{r['bitwidth']},{r['trace_len']},{ind},{r['inductive_status']},{unr},{r['unrolling_status']},{r['faster']}\n")
    print(f"\nResults saved to: {csv_file}")
    
    # Print crossover analysis
    print("\n=== Crossover Analysis ===")
    crossover_found = False
    for i, r in enumerate(results):
        if r['inductive_ms'] is not None and r['unrolling_ms'] is not None:
            if r['faster'] == "Inductive" and not crossover_found:
                print(f"Crossover point: bv{r['bitwidth']} - Inductive becomes faster")
                crossover_found = True
            speedup = r['unrolling_ms'] / r['inductive_ms'] if r['inductive_ms'] > 0 else 0
            print(f"  bv{r['bitwidth']}: Inductive={r['inductive_ms']}ms, Unrolling={r['unrolling_ms']}ms, Ratio={speedup:.2f}x")

if __name__ == "__main__":
    main()
