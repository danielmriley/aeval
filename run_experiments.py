import os
import subprocess
import re
import glob
import time
import json

def run_experiment():
    base_dir = "/home/daniel/Projects/aeval/bench_horn_split_cex_bv/s_split_01_gen"
    files = glob.glob(os.path.join(base_dir, "*.smt2"))
    
    # Sort files by the number n
    def get_n(fname):
        match = re.search(r'n(\d+).smt2', fname)
        return int(match.group(1)) if match else 0
    
    files.sort(key=get_n)
    
    print(f"{'Benchmark':<20} | {'Status':<10} | {'Time (s)':<10} | {'Notes'}")
    print("-" * 60)
    
    results = []

    for fpath in files:
        fname = os.path.basename(fpath)
        log_file = f"{fname}.log"
        
        cmd = [
            "./build/tools/deep/freqhorn",
            "--sygus-full",
            "--sygus-invariants",
            "--sygus-mbp",          # ensure MBP is on
            "--sygus-run",          # run CVC5
            "--sygus-validate",     # validate result
            "--sygus-full-bound", "5000", # ample trace length
            fpath
        ]
        
        start_time = time.time()
        status = "UNKNOWN"
        notes = ""
        duration = 0.0
        
        try:
            # Capture output
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=180)
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
            duration = 180.0
            status = "TIMEOUT"
            # Try to save partial output if possible, but capture_output doesn't give partial stdout easily 
            # without more complex handling. simpler to just note timeout.
            notes = "Timed out"
        except Exception as e:
            duration = time.time() - start_time
            status = "ERROR"
            notes = str(e)
            
        print(f"{fname:<20} | {status:<10} | {duration:<10.2f} | {notes}")
        results.append({
            "benchmark": fname,
            "status": status,
            "time": duration,
            "notes": notes,
            "n": get_n(fname)
        })

    with open("experiment_results.json", "w") as f:
        json.dump(results, f, indent=2)

if __name__ == "__main__":
    run_experiment()
