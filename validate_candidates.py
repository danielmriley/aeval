import os
import csv
import subprocess
import re
import time

# Configuration
INPUT_CSV = "trace_extraction_results.csv"
BENCH_ROOT = "bench_horn_split_cex_bv"
FREQ_HORN_BIN = "build/tools/deep/freqhorn"
SPARSE_FACTOR = 1
MEM_LIMIT_GB = 4.0

def get_benchmark_path(bench_id, bw):
    return os.path.join(BENCH_ROOT, bench_id, f"bv{bw}_{bench_id}.smt2")

def load_candidates():
    candidates = []
    if not os.path.exists(INPUT_CSV):
        print(f"Error: {INPUT_CSV} not found.")
        return []

    with open(INPUT_CSV, "r") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row["bitwidth"] == "16" and row["status"] == "Success":
                try:
                    t = float(row["time_s"])
                    row["time_s"] = t
                    candidates.append(row)
                except ValueError:
                    continue
    
    # Sort by time (fastest first)
    return sorted(candidates, key=lambda x: x["time_s"])[:10]

def run_analysis(candidate):
    bench_name = candidate["benchmark"]
    bw = candidate["bitwidth"]
    filepath = get_benchmark_path(bench_name, bw)
    
    if not os.path.exists(filepath):
        print(f"  Warning: File not found {filepath}")
        return None

    mem_bytes = int(MEM_LIMIT_GB * 1024 * 1024 * 1024)
    # CMD mirroring the manual execution, ensuring we capture output
    cmd = [
        "prlimit",
        f"--as={mem_bytes}",
        FREQ_HORN_BIN,
        "--sygus-full",
        "--sygus-full-bound", "1000000",
        "--sygus-sparse", str(SPARSE_FACTOR),
        "--sygus-run",
        "--sygus-validate",
        "--sygus-mbp",
        filepath
    ]

    print(f"Analyzing {bench_name} (Prev Time: {candidate['time_s']}s)... ", end="", flush=True)
    start_time = time.time()
    
    try:
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=300 # 5 minutes max for these "easy" ones
        )
        
        # Parse Output
        output = result.stdout
        
        # 1. Extraction Time
        trace_time = 0.0
        m_trace = re.search(r"\[Timing\] Trace Extraction: (\d+)ms", output)
        if m_trace:
            trace_time = int(m_trace.group(1)) / 1000.0
            
        # 2. Synthesis Time
        synth_time = 0.0
        m_synth = re.search(r"\[Timing\] CVC5 Synthesis: (\d+)ms", output)
        if m_synth:
            synth_time = int(m_synth.group(1)) / 1000.0
            
        # 3. Validation Time
        val_time = 0.0
        m_val = re.search(r"\[Timing\] Validation: (\d+)ms", output)
        if m_val:
            val_time = int(m_val.group(1)) / 1000.0

        # 4. Result
        status = "Unknown"
        if "Counterexample is INDUCTIVE" in output:
            status = "SUCCESS (Inductive)"
        elif "Counterexample is NOT inductive" in output:
            status = "FAIL (Not Inductive)"
        elif "CVC5 did not find a solution" in output:
            status = "No Solution"
        elif "Combined candidate is VALID" in output:
             status = "Valid Invariant"
            
        # 5. Extract Function (if success)
        synthesized_func = ""
        if status.startswith("SUCCESS"):
            # Try to grab the function body crudely
            lines = output.splitlines()
            capture = False
            for line in lines:
                if "Generated CCEX file" in line:
                    capture = False
                if capture:
                    synthesized_func += line.strip() + " "
                if "Synthesized functions:" in line:
                    capture = True
        
        print(f"Done. Status: {status}")
        return {
            "benchmark": bench_name,
            "status": status,
            "trace_time": trace_time,
            "synth_time": synth_time,
            "val_time": val_time,
            "function": synthesized_func
        }

    except subprocess.TimeoutExpired:
        print("Timeout.")
        return {"benchmark": bench_name, "status": "Timeout"}
    except Exception as e:
        print(f"Error: {e}")
        return None

def main():
    print("--- Finding Validatable Candidates (BW16, Shortest Time) ---")
    candidates = load_candidates()
    
    results = []
    for cand in candidates:
        res = run_analysis(cand)
        if res:
            results.append(res)
            
    print("\n\n--- Summary ---")
    print(f"{'Benchmark':<15} | {'Status':<20} | {'Trace(s)':<8} | {'Synth(s)':<8} | {'Val(s)':<8}")
    print("-" * 75)
    for r in results:
        if r.get("status") == "Timeout":
             print(f"{r['benchmark']:<15} | {'Timeout':<20} | {'-':<8} | {'-':<8} | {'-':<8}")
        else:
            print(f"{r['benchmark']:<15} | {r['status']:<20} | {r['trace_time']:<8.2f} | {r['synth_time']:<8.2f} | {r['val_time']:<8.2f}")

    # Print successful functions
    successes = [r for r in results if "SUCCESS" in r.get("status", "")]
    if successes:
        print("\n--- Successful Synthesized Functions ---")
        for s in successes:
            print(f"\nBenchmark: {s['benchmark']}")
            print(f"Function: {s['function']}")

if __name__ == "__main__":
    main()
