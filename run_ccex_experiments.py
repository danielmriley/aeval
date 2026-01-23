import os
import subprocess
import glob
import time
import json
import re

def run_experiment():
    base_dir = "bench_horn_ccex"
    
    # gather all smt2 files recursively
    all_files = []
    for root, dirs, files in os.walk(base_dir):
        for file in files:
            if file.endswith(".smt2"):
                all_files.append(os.path.join(root, file))
    
    # Filter files
    benchmarks = []
    for f in all_files:
        fname = os.path.basename(f)
        
        # Exclude if it is a counterexample file
        if "ccex" in fname:
            continue
            
        # Include if 16-bit
        # Look for 'bv16' or 'bvzext16' surrounded by non-digits usually, 
        # but here they are prefixes usually like bv16_...
        # Just checking "bv16" or "bvzext16" should be fine as long as we don't have bv160
        if "bv16" in fname or "bvzext16" in fname:
            benchmarks.append(f)
            
    benchmarks.sort()
    
    print(f"Found {len(benchmarks)} benchmarks.")
    print(f"{'Benchmark':<40} | {'Status':<15} | {'Time (s)':<10} | {'Notes'}")
    print("-" * 90)
    
    results = []

    for fpath in benchmarks:
        fname = os.path.basename(fpath)
        log_file = fpath + ".log"
        
        cmd = [
            "./build/tools/deep/freqhorn",
            "--sygus-full",
            "--sygus-invariants",
            "--sygus-mbp",
            "--sygus-run",
            "--sygus-validate",
            "--sygus-full-bound", "5000",
            fpath
        ]
        
        start_time = time.time()
        status = "UNKNOWN"
        notes = ""
        duration = 0.0
        
        try:
            # Capture output
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
            duration = time.time() - start_time
            output = result.stdout + "\n" + result.stderr
            
            with open(log_file, "w") as f:
                f.write(output)
            
            # Check for synthesis success
            if "Synthesized functions:" in result.stdout:
                if "Counterexample is INDUCTIVE" in result.stdout:
                    status = "VALIDATED"
                    notes = "Sol found & validated"
                else:
                    status = "SYNTH_ONLY"
                    if "Counterexample is NOT inductive" in result.stdout:
                        notes = "Not inductive"
                    else:
                        notes = "Validation unknown"
                    
            elif "CVC5 did not find a solution" in result.stdout:
                status = "NO_SOL"
            elif "Failed to extract concrete trace" in result.stdout:
                status = "NO_TRACE"
            else:
                status = "ERROR"
                notes = "See log"

        except subprocess.TimeoutExpired:
            duration = 120.0
            status = "TIMEOUT"
            notes = "Timed out"
        except Exception as e:
            duration = time.time() - start_time
            status = "ERROR"
            notes = str(e)
            
        # Shorten display name
        display_name = fpath.replace("bench_horn_ccex/", "")
        
        print(f"{display_name:<40} | {status:<15} | {duration:<10.2f} | {notes}")
        results.append({
            "benchmark": fpath,
            "display_name": display_name,
            "status": status,
            "time": duration,
            "notes": notes
        })

    with open("ccex_experiment_results.json", "w") as f:
        json.dump(results, f, indent=2)

if __name__ == "__main__":
    run_experiment()
