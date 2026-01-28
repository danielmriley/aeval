import os
import subprocess
import time
import csv
import resource
import sys

# Configuration
BENCH_DIR = "bench_c_s_split"
OUTPUT_CSV = "cbmc_smart_results.csv"
MEMORY_LIMIT_BYTES = 8 * 1024 * 1024 * 1024  # 8 GB

# Strategies
# (Label, Unwind Limit, Timeout in seconds)
STRATEGY_SHALLOW = ("SHALLOW", 1000, 30)
STRATEGY_DEEP = ("DEEP", 100000, 300)

def set_limits():
    """Set memory limit for the child process."""
    try:
        resource.setrlimit(resource.RLIMIT_AS, (MEMORY_LIMIT_BYTES, MEMORY_LIMIT_BYTES))
    except (ValueError, resource.error) as e:
        print(f"Warning: Failed to set memory limit: {e}")

def run_cbmc(filepath, unwind_limit, timeout_sec):
    """
    Run CBMC on a file with specific parameters.
    Returns: (status_string, elapsed_time)
    Status values: "BUG_FOUND", "SAFE", "TIMEOUT", "ERROR"
    """
    cmd = [
        "cbmc",
        filepath,
        f"--unwind", str(unwind_limit),
        "--trace", # Ask for trace to ensure it's doing work
        "--beautify" # clean output
    ]
    
    start = time.time()
    try:
        # Popen allows us to set preexec_fn for resource limits on the child only
        proc = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            preexec_fn=set_limits
        )
        
        stdout, stderr = proc.communicate(timeout=timeout_sec)
        elapsed = time.time() - start
        
        # Check exit code
        # CBMC Exit Code 10 = Verification Failed (Bug Found)
        # CBMC Exit Code 0 = Verification Successful (Safe within bound)
        if proc.returncode == 10:
            return "BUG_FOUND", elapsed
        elif proc.returncode == 0:
            return "SAFE_WITHIN_BOUND", elapsed
        else:
            # Other errors (compile error, etc)
            return f"ERROR_EXIT_{proc.returncode}", elapsed
            
    except subprocess.TimeoutExpired:
        proc.kill()
        return "TIMEOUT", timeout_sec
    except Exception as e:
        return f"EXCEPTION_{str(e)}", time.time() - start

def main():
    if not os.path.exists(BENCH_DIR):
        print(f"Error: Directory {BENCH_DIR} not found.")
        return

    # Collect benchmarks
    benchmarks = [f for f in os.listdir(BENCH_DIR) if f.endswith(".c")]
    benchmarks.sort()
    
    print(f"Found {len(benchmarks)} benchmarks in {BENCH_DIR}")
    print(f"Memory Limit: {MEMORY_LIMIT_BYTES / (1024**3):.1f} GB")
    print("-" * 80)
    print(f"{'Benchmark':<30} | {'Mode':<10} | {'Status':<20} | {'Time':<8}")
    print("-" * 80)
    
    results = []
    
    for bench in benchmarks:
        filepath = os.path.join(BENCH_DIR, bench)
        
        # --- PHASE 1: SHALLOW CHECK ---
        mode = STRATEGY_SHALLOW[0]
        unwind = STRATEGY_SHALLOW[1]
        timeout = STRATEGY_SHALLOW[2]
        
        status, elapsed = run_cbmc(filepath, unwind, timeout)
        
        # Decision Logic
        final_mode = mode
        final_status = status
        final_time = elapsed
        
        # If we didn't find a bug and didn't timeout/error, try Phase 2 (Deep)
        # We only escalate if Phase 1 was "Safe within bound" or completed quickly without crash
        if status == "SAFE_WITHIN_BOUND":
            # Bug might be deeper
            mode = STRATEGY_DEEP[0]
            unwind = STRATEGY_DEEP[1]
            timeout = STRATEGY_DEEP[2]
            
            # Print intermediate status (optional)
            # print(f"  > Escalating {bench} to DEEP ({unwind} unwind)...")
            
            status_deep, elapsed_deep = run_cbmc(filepath, unwind, timeout)
            
            final_mode = mode
            final_status = status_deep
            final_time = elapsed_deep + elapsed # Total time tracking

        # Print Result
        print(f"{bench:<30} | {final_mode:<10} | {final_status:<20} | {final_time:.2f}s")
        
        results.append({
            "File": bench,
            "Mode": final_mode,
            "Status": final_status,
            "Time": f"{final_time:.2f}"
        })

    # Save CSV
    with open(OUTPUT_CSV, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=["File", "Mode", "Status", "Time"])
        writer.writeheader()
        writer.writerows(results)
    
    print("-" * 80)
    print(f"Results saved to {OUTPUT_CSV}")

if __name__ == "__main__":
    main()
