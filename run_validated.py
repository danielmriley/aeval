
import os
import subprocess
import csv
import time

def run_validated_tests(bench_dir, result_file):
    timeout = 25 # Increased timeout for validation
    
    # Collect bv16 benchmarks
    benchmarks = []
    for root, dirs, files in os.walk(bench_dir):
        for f in files:
            if f.startswith("bv16_") and f.endswith(".smt2"):
                benchmarks.append(os.path.join(root, f))
                
    benchmarks.sort()
    
    print(f"Running VALIDATED PBE tests on {len(benchmarks)} bv16 benchmarks with {timeout}s timeout...")
    
    results = []
    
    # Header for screen
    print(f"{'Benchmark':<40} | {'Status':<15} | {'Time':<10}")
    print("-" * 75)
    
    success_count = 0
    fail_count = 0
    
    for bench in benchmarks:
        bench_name = os.path.basename(bench)
        # Using PBE mode with validation: --sygus --sygus-run --sygus-validate
        cmd = ["./build/tools/deep/freqhorn", "--sygus", "--sygus-run", "--sygus-validate", bench]
        
        start_time = time.time()
        try:
            # Run command
            proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout, text=True)
            elapsed = time.time() - start_time
            output = proc.stdout + proc.stderr
            
            # Criteria for TRUE success:
            # 1. Synthesized functions found
            # 2. Validation confirms INDUCTIVE (checks Init, Trans, Property)
            
            has_fn = "Synthesized functions:" in output
            is_inductive = "Counterexample is INDUCTIVE" in output
            
            if has_fn and is_inductive:
                status = "SUCCESS"
                success_count += 1
            elif has_fn and not is_inductive:
                status = "SPURIOUS"
                fail_count += 1
            elif "unsat" in output:
                status = "FAIL"
                fail_count += 1
            else:
                status = "FAIL"
                fail_count += 1
                 
        except subprocess.TimeoutExpired:
            elapsed = timeout
            status = "TIMEOUT"
            fail_count += 1
            
        rel_path = os.path.relpath(bench, bench_dir)
        print(f"{rel_path:<40} | {status:<15} | {elapsed:.2f}s")
        
        results.append([bench_name, status, f"{elapsed:.2f}"])
        
    # Write CSV
    with open(result_file, 'w', newline='') as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(['Benchmark', 'Result', 'Time'])
        writer.writerows(results)
        
    print(f"\nResults saved to {result_file}")
    print(f"Total Verified Successes: {success_count} / {len(benchmarks)}")

def main():
    bench_dir = "bench_horn_split_cex_bv"
    run_validated_tests(bench_dir, "bv16_validated_results.csv")

if __name__ == "__main__":
    main()
