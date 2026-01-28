import os
import subprocess
import time
import csv
import resource
import sys

def set_memory_limit(limit_gb):
    limit_bytes = int(limit_gb * 1024 * 1024 * 1024)
    try:
        # RLIMIT_AS controls the maximum area (in bytes) of the process's address space.
        resource.setrlimit(resource.RLIMIT_AS, (limit_bytes, limit_bytes))
        print(f"Memory limit set to {limit_gb}GB")
    except ValueError as e:
        print(f"Failed to set memory limit to {limit_gb}GB: {e}")

def get_processed_benchmarks(csv_file):
    processed = set()
    if not os.path.exists(csv_file):
        return processed
    
    try:
        with open(csv_file, 'r', newline='') as f:
            reader = csv.DictReader(f)
            for row in reader:
                if row.get("PBE_Status") and row.get("TR_Status"):
                    processed.add(row["Benchmark"])
    except Exception:
        # In case of corrupted file mostly
        pass
    return processed

def run_tool(cmd, timeout):
    start_time = time.time()
    try:
        # We assume resource limits are inherited by subprocesses
        result = subprocess.run(
            cmd, 
            stdout=subprocess.PIPE, 
            stderr=subprocess.PIPE, 
            timeout=timeout, 
            text=True
        )
        elapsed = time.time() - start_time
        output = result.stdout + result.stderr
        
        if "Synthesized functions:" in output:
            return "SUCCESS", elapsed
        else:
            return "FAIL", elapsed
            
    except subprocess.TimeoutExpired:
        return "TIMEOUT", timeout
    except Exception as e:
        return f"ERROR", 0.0

def main():
    bench_dir = "bench_horn_split_cex_bv"
    csv_filename = "split_cex_64_results.csv"
    timeout = 60
    memory_cap_gb = 8.0
    
    # Set memory limit for this process and children
    set_memory_limit(memory_cap_gb)

    # Prepare CSV fieldnames
    fieldnames = ["Benchmark", "PBE_Status", "PBE_Time", "TR_Status", "TR_Time"]
    
    # Init CSV if it doesn't exist
    if not os.path.exists(csv_filename):
        with open(csv_filename, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
    
    processed = get_processed_benchmarks(csv_filename)
    
    # Collect 64-bit benchmarks
    benchmarks = []
    for root, dirs, files in os.walk(bench_dir):
        for f in files:
            if f.startswith("bv64_") and f.endswith(".smt2"):
                benchmarks.append(os.path.join(root, f))
    
    benchmarks.sort()
    
    print(f"Found {len(benchmarks)} bv64 benchmarks.")
    print(f"Already processed: {len(processed)}")
    print(f"{'Benchmark':<50} | {'PBE':<10} | {'TR':<10}")
    print("-" * 76)

    for bench_path in benchmarks:
        rel_path = os.path.relpath(bench_path, bench_dir)
        
        if rel_path in processed:
            continue
            
        # PBE Run
        # --sygus for PBE, --sygus-run to execute
        cmd_pbe = ["./build/tools/deep/freqhorn", "--sygus", "--sygus-run", bench_path]
        pbe_status, pbe_time = run_tool(cmd_pbe, timeout)
        
        # CBS (TR) Run
        # --sygus-tr for Trace Refinement / CBS, --sygus-run to execute
        cmd_tr = ["./build/tools/deep/freqhorn", "--sygus-tr", "--sygus-run", bench_path]
        tr_status, tr_time = run_tool(cmd_tr, timeout)
        
        # Print update
        print(f"{rel_path:<50} | {pbe_status:<10} | {tr_status:<10}")
        
        # Write to CSV immediately
        with open(csv_filename, 'a', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writerow({
                "Benchmark": rel_path,
                "PBE_Status": pbe_status,
                "PBE_Time": f"{pbe_time:.2f}",
                "TR_Status": tr_status,
                "TR_Time": f"{tr_time:.2f}"
            })

if __name__ == "__main__":
    main()
