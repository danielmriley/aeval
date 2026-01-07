#!/usr/bin/env python3
import os
import sys
import subprocess
import csv
import re
import time

# Configuration
FREQHORN_PATH = "/home/daniel/Projects/aeval/build/tools/deep/freqhorn"
BENCH_ROOT = "/home/daniel/Projects/aeval/bench_horn_ccex"
OUTPUT_CSV = "benchmark_results.csv"
TIMEOUT_SEC = 60
MAX_BITWIDTH = 128

def get_bitwidth(filename):
    match = re.search(r'bv(\d+)', filename)
    if not match:
        match = re.search(r'bvzext(\d+)', filename)
    if match:
        return int(match.group(1))
    return None

def get_expected_status(path):
    if "invalid" in path:
        return "INVALID"
    return "VALID"

def run_benchmark(chc_path, ccex_path):
    cmd = [FREQHORN_PATH, "--bv", "--ccex", ccex_path, chc_path]
    
    start_time = time.time()
    try:
        result = subprocess.run(
            cmd, 
            capture_output=True, 
            text=True, 
            timeout=TIMEOUT_SEC
        )
        elapsed_ms = int((time.time() - start_time) * 1000)
        output = result.stdout + result.stderr
        
        if "CEX VALID" in output:
            status = "VALID"
        elif "CEX INVALID" in output:
            status = "INVALID"
        else:
            status = "UNKNOWN"
            # Check for specific errors
            if "Error" in output:
                status = "ERROR"
                
        return status, elapsed_ms, output
        
    except subprocess.TimeoutExpired:
        return "TIMEOUT", int(TIMEOUT_SEC * 1000), ""
    except Exception as e:
        return "ERROR", 0, str(e)

def main():
    print(f"Starting benchmark run (Max BW: {MAX_BITWIDTH}, Timeout: {TIMEOUT_SEC}s)...")
    
    results = []
    
    # Walk the directory tree
    for root, dirs, files in os.walk(BENCH_ROOT):
        # Skip __pycache__ and other non-benchmark dirs if necessary
        if "__pycache__" in root:
            continue
            
        # Find all CHC files (files ending in .smt2 but not _ccex.smt2)
        chc_files = [f for f in files if f.endswith(".smt2") and "_ccex.smt2" not in f]
        
        # Sort for consistent output
        chc_files.sort()
        
        for chc_file in chc_files:
            # Construct corresponding CCEX filename
            base_name = chc_file[:-5] # remove .smt2
            ccex_file = f"{base_name}_ccex.smt2"
            
            if ccex_file not in files:
                continue
                
            # Check bitwidth
            bw = get_bitwidth(chc_file)
            if bw is None or bw > MAX_BITWIDTH:
                continue
                
            chc_path = os.path.join(root, chc_file)
            ccex_path = os.path.join(root, ccex_file)
            
            # Determine category relative to BENCH_ROOT
            rel_dir = os.path.relpath(root, BENCH_ROOT)
            if rel_dir == ".":
                category = "root"
            else:
                category = rel_dir
                
            expected = get_expected_status(root)
            
            print(f"Running {category}/{chc_file} (BW={bw})... ", end="", flush=True)
            
            status, time_ms, output = run_benchmark(chc_path, ccex_path)
            
            # Determine pass/fail based on expectation
            # For invalid benchmarks, getting INVALID is a PASS
            # For valid benchmarks, getting VALID is a PASS
            pass_fail = "PASS" if status == expected else "FAIL"
            if status == "TIMEOUT" or status == "ERROR" or status == "UNKNOWN":
                pass_fail = "FAIL"
                
            print(f"{status} ({time_ms}ms) -> {pass_fail}")
            
            results.append({
                "Category": category,
                "Benchmark": base_name,
                "Bitwidth": bw,
                "Expected": expected,
                "Actual": status,
                "Time_ms": time_ms,
                "Result": pass_fail
            })

    # Write CSV
    csv_path = os.path.join(BENCH_ROOT, OUTPUT_CSV)
    with open(csv_path, 'w', newline='') as csvfile:
        fieldnames = ["Category", "Benchmark", "Bitwidth", "Expected", "Actual", "Time_ms", "Result"]
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        
        writer.writeheader()
        for row in results:
            writer.writerow(row)
            
    print(f"\nResults written to {csv_path}")
    
    # Print summary
    total = len(results)
    passed = sum(1 for r in results if r["Result"] == "PASS")
    print(f"Summary: {passed}/{total} passed.")

if __name__ == "__main__":
    main()
