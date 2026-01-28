import os
import subprocess
import time
import csv
import resource

def set_memory_limit(limit_gb):
    limit_bytes = int(limit_gb * 1024 * 1024 * 1024)
    try:
        resource.setrlimit(resource.RLIMIT_AS, (limit_bytes, limit_bytes))
    except ValueError as e:
        print(f"Failed to set memory limit: {e}")

def run_tool(cmd, timeout):
    start_time = time.time()
    try:
        result = subprocess.run(
            cmd, 
            stdout=subprocess.PIPE, 
            stderr=subprocess.PIPE, 
            timeout=timeout, 
            text=True
        )
        elapsed = time.time() - start_time
        output = result.stdout + result.stderr
        
        # Check for synthesis success
        if "Synthesized functions:" in output:
            return "SUCCESS", elapsed
        # Check for specific failure modes if needed, but FAIL is default
        return "FAIL", elapsed
            
    except subprocess.TimeoutExpired:
        return "TIMEOUT", timeout
    except Exception as e:
        return f"ERROR", 0.0

def main():
    bench_dir = "bench_horn_split_cex_bv"
    csv_filename = "split_cex_64_results_tr_fixed.csv"
    timeout = 60
    memory_cap_gb = 8.0
    
    set_memory_limit(memory_cap_gb)
    
    # We only care about TR results now
    fieldnames = ["Benchmark", "TR_Status", "TR_Time"]
    
    with open(csv_filename, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
    
    # Collect 64-bit benchmarks
    benchmarks = []
    for root, dirs, files in os.walk(bench_dir):
        for f in files:
            if f.startswith("bv64_") and f.endswith(".smt2"):
                benchmarks.append(os.path.join(root, f))
    
    benchmarks.sort()
    
    print(f"Found {len(benchmarks)} bv64 benchmarks. Running TR fix verification...")
    print(f"{'Benchmark':<50} | {'TR_Status':<10} | {'Time':<8}")
    print("-" * 75)

    for bench_path in benchmarks:
        rel_path = os.path.relpath(bench_path, bench_dir)
        
        # CBS (TR) Run
        # --sygus-tr for Trace Refinement / CBS, --sygus-run to execute
        cmd_tr = ["./build/tools/deep/freqhorn", "--sygus-tr", "--sygus-run", "--sygus-mbp", "--sygus-validate", bench_path]
        tr_status, tr_time = run_tool(cmd_tr, timeout)
        
        print(f"{rel_path:<50} | {tr_status:<10} | {tr_time:<8.2f}")
        
        with open(csv_filename, 'a', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writerow({
                "Benchmark": rel_path,
                "TR_Status": tr_status,
                "TR_Time": f"{tr_time:.2f}"
            })

if __name__ == "__main__":
    main()
