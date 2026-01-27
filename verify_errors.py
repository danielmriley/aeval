import os
import subprocess
import time
import csv
import sys
import re

# Configuration
FREQ_HORN_BIN = "./build/tools/deep/freqhorn"
BENCH_ROOT = "bench_horn_ccex"
TIMEOUT_SEC = 900  # 15 minutes
MEMORY_LIMIT_GB = 8
MEMORY_LIMIT_BYTES = MEMORY_LIMIT_GB * 1024 * 1024 * 1024
INPUT_CSV = "full_benchmark_comparison_results.csv"

# Configurations to test
CONFIGS = {
    "PBE": ["--sygus"],
    "TR": ["--sygus-tr"], 
    "Full": ["--sygus-full", "--sygus-full-bound", "1000000", "--sygus-sparse", "1"]
}

# Common args for all configs
COMMON_ARGS = ["--sygus-run", "--sygus-validate", "--sygus-mbp"]

def find_benchmark_path(filename):
    for root, dirs, files in os.walk(BENCH_ROOT):
        if filename in files:
            return os.path.join(root, filename)
    return None

def run_freqhorn(filepath, config_name, extra_args):
    cmd = [
        "prlimit",
        f"--as={MEMORY_LIMIT_BYTES}", # Virtual memory limit
        "/usr/bin/time", "-v",
        FREQ_HORN_BIN
    ] + extra_args + COMMON_ARGS + [filepath]
    
    print(f"Re-running {os.path.basename(filepath)} [{config_name}]...", end="", flush=True)
    
    start_time = time.time()
    try:
        # Execution
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, 
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
        cvc_sol = "CVC5 Synthesis:" in output and "CVC5 did not find a solution" not in output
        validated = "Counterexample is INDUCTIVE" in output
        
        status = "Failed"
        if result.returncode != 0:
            if "Command exited with non-zero status" in output: 
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
            
        print(f" -> {status}")
        return {
            "time": duration,
            "memory_mb": rss_kb / 1024.0,
            "status": status
        }
        
    except subprocess.TimeoutExpired:
        print(" -> Timeout")
        return {
            "time": TIMEOUT_SEC,
            "memory_mb": 0,
            "status": "Timeout"
        }
    except Exception as e:
        print(f" -> ExecError: {e}")
        return {
            "time": 0,
            "memory_mb": 0,
            "status": "ExecError"
        }

def main():
    # Read existing results
    rows = []
    with open(INPUT_CSV, "r") as f:
        reader = csv.DictReader(f)
        fieldnames = reader.fieldnames
        for row in reader:
            rows.append(row)
    
    updates_made = False
    
    for row in rows:
        if row["Status"] == "Error":
            bench_name = row["Benchmark"]
            config_name = row["Config"]
            
            filepath = find_benchmark_path(bench_name)
            if not filepath:
                print(f"Could not find file for {bench_name}")
                continue
                
            if config_name not in CONFIGS:
                print(f"Unknown config {config_name}")
                continue
            
            res = run_freqhorn(filepath, config_name, CONFIGS[config_name])
            
            # Update row
            row["Status"] = res["status"]
            row["Time(s)"] = f"{res['time']:.2f}"
            row["Memory(MB)"] = f"{res['memory_mb']:.2f}"
            updates_made = True

    if updates_made:
        print("Writing updated CSV...")
        with open(INPUT_CSV, "w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(rows)
        print("Done.")
    else:
        print("No updates made.")

if __name__ == "__main__":
    main()
