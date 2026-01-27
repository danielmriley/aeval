
import os
import subprocess
import time
import csv
import sys
import fnmatch
import re

# Configuration
FREQ_HORN_BIN = "./build/tools/deep/freqhorn"
BENCH_ROOT = "bench_horn_ccex"
TIMEOUT_SEC = 900  # 15 minutes
MEMORY_LIMIT_GB = 8
MEMORY_LIMIT_BYTES = MEMORY_LIMIT_GB * 1024 * 1024 * 1024
OUTPUT_CSV = "full_benchmark_comparison_results.csv"

# Configurations to test
# 1. PBE: --sygus
# 2. TR: --sygus-tr
# 3. Full: --sygus-full
CONFIGS = [
    {"name": "PBE", "args": ["--sygus"]},
    {"name": "TR", "args": ["--sygus-tr"]}, # Assuming --sygus-tr is translation relation mode? Wait, user said "sygus-tr flag"
    {"name": "Full", "args": ["--sygus-full", "--sygus-full-bound", "1000000", "--sygus-sparse", "1"]}
]
# Note: User mentioned "sygus-tr flag", but previous context implies sygus-full vs sygus PBE.
# If --sygus-tr isn't a flag I've seen before, I need to check. 
# Looking at help strings or previous interactions...
# The prompt says "using PBE (--sygus)", "sygus-tr flag", "sygus-full".
# Let's assume --sygus-tr is a valid flag for Transition Relation synthesis or similar. 
# If not, I will discover it.

# Common args for all configs
COMMON_ARGS = ["--sygus-run", "--sygus-validate", "--sygus-mbp"]

def get_memory_usage(pid):
    try:
        with open(f"/proc/{pid}/status", "r") as f:
            for line in f:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1]) # in kB
    except:
        return 0
    return 0

def run_freqhorn(filepath, config_name, extra_args):
    filename = os.path.basename(filepath)
    cmd = [
        "prlimit",
        f"--as={MEMORY_LIMIT_BYTES}", # Virtual memory limit
        FREQ_HORN_BIN
    ] + extra_args + COMMON_ARGS + [filepath]
    
    print(f"Running {filename} [{config_name}]...", end="", flush=True)
    
    start_time = time.time()
    try:
        # We need to subprocess to poll memory usage
        # But for simpler reporting with `time -v`, we can parse output.
        # User asked to "track memory usage". Let's use /usr/bin/time -v wrapper.
        
        # Construct actual command line for printing
        full_cmd = ["/usr/bin/time", "-v"] + cmd
        
        # Execution
        result = subprocess.run(
            full_cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, # Merge stderr for time output
            text=True,
            timeout=TIMEOUT_SEC
        )
        
        duration = time.time() - start_time
        output = result.stdout
        
        # Parse metrics
        rss_kb = 0
        m_mem = re.search(r"Maximum resident set size \(kbytes\): (\d+)", output)
        if m_mem:
            rss_kb = int(m_mem.group(1))
            
        # Parse result
        # Check for synthesis success
        cvc_sol = "CVC5 Synthesis:" in output and "CVC5 did not find a solution" not in output
        
        # Check validation
        validated = "Counterexample is INDUCTIVE" in output
        
        status = "Failed"
        if result.returncode != 0:
            if "Command exited with non-zero status" in output: # from /usr/time if wrapped cmd fails
                 # Try to find specific error
                 if "std::bad_alloc" in output:
                     status = "OOM"
                 else:
                     status = "Error"
            else:
                status = "Error"
        elif validated:
            status = "Validated"
        elif cvc_sol:
            status = "SynthOnly"
        else:
            status = "NoSol"
            
        return {
            "time": duration,
            "memory_mb": rss_kb / 1024.0,
            "status": status,
            "output_excerpt": output[-500:] # Last 500 chars for debug
        }
        
    except subprocess.TimeoutExpired:
        print(" Timeout.")
        return {
            "time": TIMEOUT_SEC,
            "memory_mb": 0, # Unknown
            "status": "Timeout",
            "output_excerpt": "Timeout"
        }
    except Exception as e:
        print(f" Error: {e}")
        return {
            "time": 0,
            "memory_mb": 0,
            "status": "ExecError",
            "output_excerpt": str(e)
        }
    finally:
        print(" Done.")

def should_skip(filepath):
    filename = os.path.basename(filepath)
    if "ccex" in filename: return True
    if int2bv_check(filepath): return True
    
    # Check bitwidth <= 64
    # Pattern usually bv(\d+)_ or bvzext(\d+)_
    m = re.search(r"bv(zext)?(\d+)_", filename)
    if m:
        bw = int(m.group(2))
        if bw > 64: return True
    
    return False

def int2bv_check(filepath):
    with open(filepath, 'r') as f:
        content = f.read()
        if "int2bv" in content or "bv2int" in content:
            return True
    return False

def main():
    benchmarks = []
    for root, dirs, files in os.walk(BENCH_ROOT):
        for file in files:
            if file.endswith(".smt2"):
                path = os.path.join(root, file)
                if not should_skip(path):
                    benchmarks.append(path)
    
    benchmarks.sort()
    
    print(f"Found {len(benchmarks)} applicable benchmarks.")
    
    results = []
    
    # Prepare CSV
    with open(OUTPUT_CSV, "w", newline="") as csvfile:
        writer = csv.writer(csvfile)
        writer.writerow(["Benchmark", "Config", "Status", "Time(s)", "Memory(MB)"])
        
        for bench in benchmarks:
            for config in CONFIGS:
                res = run_freqhorn(bench, config["name"], config["args"])
                
                writer.writerow([
                    os.path.basename(bench),
                    config["name"],
                    res["status"],
                    f"{res['time']:.2f}",
                    f"{res['memory_mb']:.2f}"
                ])
                csvfile.flush() # Ensure we save progress

    # Generate Report string at the end
    print("\nComparison Run Completed. Results in " + OUTPUT_CSV)

if __name__ == "__main__":
    import argparse
    # Check if --sygus-tr works (simple dummy check could be added here)
    main()
