
import os
import shutil
import subprocess
import csv
import time

def cleanup_unwanted_bitwidths(root_dir):
    print("Cleaning up 4-bit and 8-bit benchmarks...")
    
    # 1. Remove top-level bv4 and bv8 directories
    for d in ["bv4", "bv8"]:
        dir_path = os.path.join(root_dir, d)
        if os.path.exists(dir_path):
            print(f"Removing directory: {dir_path}")
            shutil.rmtree(dir_path)
            
    # 2. Walk through subdirectories and remove bv4_* and bv8_* files
    count = 0
    for root, dirs, files in os.walk(root_dir):
        for f in files:
            if f.startswith("bv4_") or f.startswith("bv8_"):
                file_path = os.path.join(root, f)
                # print(f"Removing file: {file_path}")
                os.remove(file_path)
                count += 1
    print(f"Removed {count} bv4/bv8 files.")

def run_tests_and_report(bench_dir, result_file):
    timeout = 20
    
    # Collect bv16 benchmarks
    benchmarks = []
    for root, dirs, files in os.walk(bench_dir):
        for f in files:
            if f.startswith("bv16_") and f.endswith(".smt2"):
                benchmarks.append(os.path.join(root, f))
                
    benchmarks.sort()
    
    print(f"Running PBE tests on {len(benchmarks)} bv16 benchmarks with {timeout}s timeout...")
    
    results = []
    
    # Header for screen
    print(f"{'Benchmark':<40} | {'Status':<10} | {'Time':<10}")
    print("-" * 65)
    
    for bench in benchmarks:
        bench_name = os.path.basename(bench)
        # Using PBE mode: --sygus --sygus-run
        cmd = ["./build/tools/deep/freqhorn", "--sygus", "--sygus-run", bench]
        
        start_time = time.time()
        try:
            # Run command
            proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout, text=True)
            elapsed = time.time() - start_time
            output = proc.stdout + proc.stderr
            
            if "Synthesized functions:" in output:
                status = "SUCCESS"
            elif "unsat" in output and "Synthesized functions" not in output:
                 # Standard SMT solvers print unsat for safe
                 # But in SyGuS it prints the function
                 status = "FAIL"
            else:
                 # Maybe crashed or other output
                 # If we see "unknown"
                 status = "FAIL"
                 
        except subprocess.TimeoutExpired:
            elapsed = timeout
            status = "TIMEOUT"
            
        rel_path = os.path.relpath(bench, bench_dir)
        print(f"{rel_path:<40} | {status:<10} | {elapsed:.2f}s")
        
        results.append([bench_name, status, f"{elapsed:.2f}"])
        
    # Write CSV
    with open(result_file, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(['Benchmark', 'Result', 'Time'])
        writer.writerows(results)
        
    print(f"\nResults saved to {result_file}")

def main():
    bench_dir = "bench_horn_split_cex_bv"
    cleanup_unwanted_bitwidths(bench_dir)
    run_tests_and_report(bench_dir, "bv16_results.csv")

if __name__ == "__main__":
    main()
