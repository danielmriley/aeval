import os
import subprocess
import re
import csv
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

# Configuration
FREQ_HORN_BIN = "./build/tools/deep/freqhorn"
BENCH_ROOT = "bench_horn_split_cex_bv"
OUTPUT_CSV = "trace_extraction_results.csv"
MAX_WORKERS = 10
TIMEOUT_SEC = 4200  # 1 hour and 10 minutes
MAX_BOUND = 1000000

def run_benchmark(filepath):
    filename = os.path.basename(filepath)
    # Extract bitwidth and benchmark ID from filename like bv8_s_split_01.smt2
    match = re.match(r"bv(\d+)_s_split_(\d+).smt2", filename)
    if not match:
        return None
    
    bw = int(match.group(1))
    bench_id = match.group(2)
    
    cmd = [
        FREQ_HORN_BIN,
        "--sygus-full",
        "--sygus-full-bound", str(MAX_BOUND),
        filepath
    ]
    
    start_time = time.time()
    try:
        # Run the command with timeout
        result = subprocess.run(
            cmd, 
            stdout=subprocess.PIPE, 
            stderr=subprocess.STDOUT, 
            text=True, 
            timeout=TIMEOUT_SEC
        )
        duration = time.time() - start_time
        stdout = result.stdout
        
        if result.returncode == 0:
            status = "Success"
            # Extract trace length: "  Extracted 123 trace points"
            trace_match = re.search(r"Extracted (\d+) trace points", stdout)
            trace_len = int(trace_match.group(1)) if trace_match else "Unknown"
        else:
            status = "Failed"
            trace_len = 0
            
    except subprocess.TimeoutExpired:
        duration = TIMEOUT_SEC
        status = "Timeout"
        trace_len = 0
    except Exception as e:
        duration = time.time() - start_time
        status = f"Error: {str(e)}"
        trace_len = 0

    return {
        "benchmark": f"s_split_{bench_id}",
        "bitwidth": bw,
        "status": status,
        "trace_length": trace_len,
        "time_s": round(duration, 2)
    }

def main():
    benchmarks = []
    # Collect all 8, 16, 32 bit benchmarks
    for root, dirs, files in os.walk(BENCH_ROOT):
        for f in files:
            if re.match(r"bv(8|16|32)_s_split_\d+\.smt2", f):
                benchmarks.append(os.path.join(root, f))
    
    # Sort benchmarks to run 8 bit first, then 16, then 32
    def sort_key(path):
        filename = os.path.basename(path)
        m = re.match(r"bv(\d+)_s_split_(\d+).smt2", filename)
        return (int(m.group(1)), int(m.group(2)))
    
    benchmarks.sort(key=sort_key)
    
    print(f"Found {len(benchmarks)} benchmarks. Starting experiments with {MAX_WORKERS} workers...")
    
    results = []
    # Initialize CSV file with headers
    with open(OUTPUT_CSV, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=["benchmark", "bitwidth", "status", "trace_length", "time_s"])
        writer.writeheader()

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        future_to_bench = {executor.submit(run_benchmark, b): b for b in benchmarks}
        
        count = 0
        for future in as_completed(future_to_bench):
            res = future.result()
            if res:
                results.append(res)
                # Write to CSV immediately to keep track of progress
                with open(OUTPUT_CSV, "a", newline="") as f:
                    writer = csv.DictWriter(f, fieldnames=res.keys())
                    writer.writerow(res)
                
                count += 1
                print(f"[{count}/{len(benchmarks)}] {res['benchmark']} (bw={res['bitwidth']}): {res['status']} in {res['time_s']}s")

    print(f"\nExperiment complete. Results saved to {OUTPUT_CSV}")

if __name__ == "__main__":
    main()
