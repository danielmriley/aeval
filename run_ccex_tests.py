import os
import subprocess
import glob
import time
import re
import csv
from pathlib import Path

def run_tests():
    base_dir = "bench_horn_ccex"
    
    # helper to find all ccex files
    ccex_files = []
    for root, dirs, files in os.walk(base_dir):
        for file in files:
            if file.endswith("ccex.smt2"):
                ccex_files.append(os.path.join(root, file))
    
    print(f"Found {len(ccex_files)} ccex files.")
    
    results = []
    
    print(f"{'Benchmark':<40} | {'Status':<15} | {'Time':<6}")
    print("-" * 70)
    
    total_solved = 0
    total_runs = 0
    
    for ccex_path in ccex_files:
        # Determine benchmark path
        # Pattern: name_ccex.smt2 -> name.smt2
        fname_ccex = os.path.basename(ccex_path)
        
        # Filter > 64 bit versions
        match = re.search(r'bv(zext)?(\d+)_', fname_ccex)
        if match and int(match.group(2)) > 64:
            continue

        fname_bench = fname_ccex.replace("_ccex.smt2", ".smt2")
        bench_path = os.path.join(os.path.dirname(ccex_path), fname_bench)
        
        if not os.path.exists(bench_path):
            # print(f"Skipping {fname_ccex}, benchmark {fname_bench} not found")
            continue
            
        total_runs += 1
        
        cmd = [
            "./build/tools/deep/freqhorn",
            "--ccex", ccex_path,
            bench_path
        ]
        
        start_time = time.time()
        status = "UNKNOWN"
        
        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
            duration = time.time() - start_time
            
            output = result.stdout
            
            if "CEX VALID: All" in output:
                 status = "VALID"
                 total_solved += 1
            elif "CEX VALID (Partial):" in output:
                 status = "VALID"
                 total_solved += 1
            elif "Counterexample is NOT inductive" in output:
                 status = "INVALID"
            elif "CEX INVALID" in output:
                 # Check if this benchmark is EXPECTED to be invalid
                 if "invalid" in fname_bench or "fail" in fname_bench:
                     status = "VALID (EXP)"
                     total_solved += 1
                 else:
                     status = "INVALID"
            else:
                 # Check for errors in stderr if status is still UNKNOWN
                 status = "FAIL"

        except subprocess.TimeoutExpired:
            duration = 60.0
            status = "TIMEOUT"
            
        print(f"{fname_bench:<40} | {status:<15} | {duration:.2f}s")
        results.append((fname_bench, status, duration))
        
    print("-" * 70)
    print(f"Total Runs: {total_runs}")
    print(f"Total Solved: {total_solved}")
    print(f"Success Rate: {total_solved/total_runs*100:.1f}%" if total_runs > 0 else "N/A")

    # Write results to CSV
    csv_file = "ccex_validation_results.csv"
    with open(csv_file, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(["Benchmark", "Status", "Time"])
        writer.writerows(results)
    
    print(f"\nResults saved to {csv_file}")

if __name__ == "__main__":
    run_tests()
