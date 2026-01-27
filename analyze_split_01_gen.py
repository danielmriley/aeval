import os
import subprocess
import re
import time
import glob

# Configuration
BENCH_DIR = "bench_horn_split_cex_bv/s_split_01_gen"
FREQ_HORN_BIN = "build/tools/deep/freqhorn"
SPARSE_FACTOR = 1
MEM_LIMIT_GB = 8.0

def run_analysis(filepath):
    filename = os.path.basename(filepath)
    mem_bytes = int(MEM_LIMIT_GB * 1024 * 1024 * 1024)
    
    cmd = [
        # "prlimit",
        # f"--as={mem_bytes}",
        FREQ_HORN_BIN,
        "--sygus-full",
        "--sygus-full-bound", "1000000",
        "--sygus-sparse", str(SPARSE_FACTOR),
        "--sygus-run",
        "--sygus-validate",
        "--sygus-mbp",
        filepath
    ]
    
    start_time = time.time()
    try:
        # Increase timeout just in case
        result = subprocess.run(
            cmd, 
            stdout=subprocess.PIPE, 
            stderr=subprocess.STDOUT, 
            text=True, 
            timeout=300
        )
        duration = time.time() - start_time
        output = result.stdout
        
        # Parse Exact Trace Length
        length = 0
        m_len = re.search(r"Extracted (\d+) trace points", output)
        if m_len:
            length = int(m_len.group(1))

        # Parse Timings
        timings = {}
        for stage in ["Trace Extraction", "SyGuS Gen", "CVC5 Synthesis", "Validation"]:
            m = re.search(fr"\[Timing\] {stage}: (\d+)ms", output)
            timings[stage] = int(m.group(1))/1000.0 if m else 0.0

        # Parse Validation Result
        if "Counterexample is INDUCTIVE" in output:
            val_status = "Pass"
        elif "Counterexample is NOT inductive" in output:
            val_status = "Fail"
        elif "CVC5 did not find a solution" in output:
            val_status = "No Sol"
        else:
            val_status = "Error"
            
        return {
            "filename": filename,
            "length": length,
            "trace_s": timings.get('Trace Extraction', 0),
            "synth_s": timings.get('CVC5 Synthesis', 0),
            "val_s": timings.get('Validation', 0),
            "status": val_status
        }
        
    except subprocess.TimeoutExpired:
        return {
            "filename": filename,
            "length": -1,
            "trace_s": 0,
            "synth_s": 0,
            "val_s": 0,
            "status": "Timeout"
        }

def main():
    print(f"Analyzing files in {BENCH_DIR}...")
    files = glob.glob(os.path.join(BENCH_DIR, "*.smt2"))
    
    # Sort by N number
    try:
        files.sort(key=lambda f: int(re.search(r"_n(\d+)\.smt2", f).group(1)))
    except:
        files.sort()
        
    print(f"{'Benchmark':<20} | {'Len':<8} | {'Trace(s)':<8} | {'Synth(s)':<8} | {'Val(s)':<8} | {'Result':<10}")
    print("-" * 75)
    
    for f in files:
        res = run_analysis(f)
        print(f"{res['filename']:<20} | {res['length']:<8} | {res['trace_s']:<8.2f} | {res['synth_s']:<8.2f} | {res['val_s']:<8.2f} | {res['status']:<10}")

if __name__ == "__main__":
    main()
