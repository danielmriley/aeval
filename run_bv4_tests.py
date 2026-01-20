
import os
import subprocess
import time

def main():
    bench_dir = "bench_horn_split_cex_bv"
    timeout = 20
    
    # Collect all bv4 benchmarks
    benchmarks = []
    for root, dirs, files in os.walk(bench_dir):
        for f in files:
            if f.startswith("bv4_") and f.endswith(".smt2"):
                benchmarks.append(os.path.join(root, f))
    
    benchmarks.sort()
    
    print(f"Found {len(benchmarks)} bv4 benchmarks. Running tests with {timeout}s timeout...")
    print(f"{'Benchmark':<40} | {'Status':<10} | {'Time':<10}")
    print("-" * 65)
    
    success_count = 0
    timeout_count = 0
    fail_count = 0
    
    for bench in benchmarks:
        cmd = ["./build/tools/deep/freqhorn", "--sygus-s", "--sygus-run", bench]
        
        start_time = time.time()
        try:
            # Capturing stdout/stderr to check output
            result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout, text=True)
            elapsed = time.time() - start_time
            
            output = result.stdout + result.stderr
            status = "FAIL"
            
            if "Synthesized functions:" in output:
                status = "SUCCESS"
                success_count += 1
            else:
                fail_count += 1
                # Check for known errors in output?
                # print(output) # Optional debug
                
        except subprocess.TimeoutExpired:
            elapsed = timeout
            status = "TIMEOUT"
            timeout_count += 1
            
        rel_path = os.path.relpath(bench, bench_dir)
        print(f"{rel_path:<40} | {status:<10} | {elapsed:.2f}s")
        
    print("-" * 65)
    print(f"Summary: SUCCESS={success_count}, TIMEOUT={timeout_count}, FAIL={fail_count}")

if __name__ == "__main__":
    main()
