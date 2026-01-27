import os
import subprocess
import re
import csv
import time

# Configuration
FREQ_HORN_BIN = "./build/tools/deep/freqhorn"
BENCH_ROOT = "bench_horn_split_cex_bv"
INPUT_CSV = "trace_extraction_results.csv"
OUTPUT_TEX = "latex/top_traces_report.tex"
SPARSE_FACTOR = 1    # Full resolution (no missed values)
MEM_LIMIT_GB = 4.0

def get_benchmark_path(bench_id, bw):
    return os.path.join(BENCH_ROOT, bench_id, f"bv{bw}_{bench_id}.smt2")

def run_detailed_analysis(filepath):
    filename = os.path.basename(filepath)
    mem_bytes = int(MEM_LIMIT_GB * 1024 * 1024 * 1024)
    
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
        # "--sygus-invariants", # Removed as requested
        filepath
    ]
    
    print(f"  Analyzing {filename}...", end="", flush=True)
    start_time = time.time()
    
    try:
        # Increase overall tool timeout
        result = subprocess.run(
            cmd, 
            stdout=subprocess.PIPE, 
            stderr=subprocess.STDOUT, 
            text=True, 
            timeout=900 # Increased to 15 minutes
        )
        duration = time.time() - start_time
        
        # Parse exact length
        exact_len_match = re.search(r"Found satisfiable trace of length (\d+)", result.stdout)
        exact_len = int(exact_len_match.group(1)) if exact_len_match else None
        
        if exact_len is None:
            sparse_match = re.search(r"Extracted (\d+) trace points", result.stdout)
            if sparse_match:
                exact_len = int(sparse_match.group(1)) * SPARSE_FACTOR
                print(" (Approx)", end="")
        
        # Parse Timings
        timings = {}
        for stage in ["Trace Extraction", "SyGuS Gen", "CVC5 Synthesis", "Validation"]:
            m = re.search(fr"\[Timing\] {stage}: (\d+)ms", result.stdout)
            timings[stage] = int(m.group(1))/1000.0 if m else 0.0

        # Parse Validation Result
        if "Counterexample is INDUCTIVE" in result.stdout:
            val_status = "Pass"
        elif "Counterexample is NOT inductive" in result.stdout:
            val_status = "Fail"
        elif "CVC5 did not find a solution" in result.stdout:
            val_status = "No Sol"
        else:
            val_status = "Error"
            
        print(f" Done. Len: {exact_len}, Trace: {timings.get('Trace Extraction', 0):.2f}s, Synth: {timings.get('CVC5 Synthesis', 0):.2f}s, Val: {val_status}")
        
        return {
            "benchmark": filename,
            "exact_length": exact_len,
            "duration": duration,
            "timings": timings,
            "val_status": val_status,
            "cmd": " ".join(cmd)
        }
        
    except subprocess.TimeoutExpired:
        print(" Timeout.")
        return None
    except Exception as e:
        print(f" Error: {e}")
        return None

def generate_latex(top_results):
    latex_content = r"""\documentclass{article}
\usepackage{booktabs}
\usepackage{geometry}
\geometry{a4paper, margin=1in}

\title{Comprehensive Analysis of Longest Traces: Extraction, Synthesis, and Validation}
\author{Automated Analysis Report}
\date{\today}

\begin{document}

\maketitle

\section{Overview}
This section presents a comprehensive evaluation of the 10 longest execution traces extracted by the tool. For each benchmark, we performed:
\begin{enumerate}
    \item \textbf{Full Trace Extraction}: Extracting the concrete path to the violation.
    \item \textbf{SyGuS Synthesis}: Generating a SyGuS problem using the trace, seeded with constants and MBP guards, and solving it with CVC5.
    \item \textbf{Inductive Validation}: Checking if the synthesized function is a valid inductive invariant for the system.
\end{enumerate}

\section{Granular Performance Data}
Table~\ref{tab:top_traces} details the exact trace length and the time spent in each phase.
\begin{itemize}
    \item \textbf{Trace}: Time to extract the concrete trace.
    \item \textbf{Synth}: Time for CVC5 to synthesize a candidate function.
    \item \textbf{Val}: Time to validate the candidate inductively.
\end{itemize}

\begin{table}[h]
\centering
\begin{tabular}{@{}l c r r r r c@{}}
\toprule
Benchmark & BW & Length & Trace(s) & Synth(s) & Val(s) & Result \\
\midrule
"""
    
    sorted_results = sorted(top_results, key=lambda x: x['exact_length'] if x['exact_length'] else 0, reverse=True)
    
    for res in sorted_results:
        # clean filename
        simple_name = res['benchmark'].replace('.smt2', '')
        # extract s_split_XX
        # check if it matches bvXX_s_split_XX
        m = re.match(r"bv(\d+)_(s_split_\d+)", simple_name)
        if m:
            bench_name = m.group(2)
        else:
            bench_name = simple_name
            
        bench_escaped = bench_name.replace('_', r'\_')
        length_str = f"{res['exact_length']:,}" if res['exact_length'] else "N/A"
        
        t_trace = f"{res['timings'].get('Trace Extraction', 0):.2f}"
        t_synth = f"{res['timings'].get('CVC5 Synthesis', 0):.2f}"
        t_val = f"{res['timings'].get('Validation', 0):.2f}"
        
        # Formatting result
        res_str = res['val_status']
        if res['val_status'] == "Pass":
            res_str = r"\textbf{Pass}"
        elif res['val_status'] == "Fail":
            res_str = r"\textit{Fail}"
        
        latex_content += f"{bench_escaped} & {res['bitwidth']} & {length_str} & {t_trace} & {t_synth} & {t_val} & {res_str} \\\\\n"

    latex_content += r"""\bottomrule
\end{tabular}
\caption{Performance breakdown of longest extracted traces.}
\label{tab:top_traces}
\end{table}

\end{document}
"""
    
    os.makedirs(os.path.dirname(OUTPUT_TEX), exist_ok=True)
    with open(OUTPUT_TEX, "w") as f:
        f.write(latex_content)
    print(f"\nReport generated at {OUTPUT_TEX}")

def main():
    if not os.path.exists(INPUT_CSV):
        print("Error: Input CSV not found.")
        return

    print("Reading results...")
    candidates = []
    # Deduplicate: if s_split_06 appears in 16 and 32 bit, keep both? Yes.
    
    with open(INPUT_CSV, "r") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row['status'] == 'Success':
                try:
                    candidates.append({
                        "benchmark": row['benchmark'],
                        "bitwidth": int(row['bitwidth']),
                        "trace_length": int(row['trace_length'])
                    })
                except ValueError:
                    continue
    
    candidates.sort(key=lambda x: x['trace_length'], reverse=True)
    # Take top 15
    target_candidates = candidates[:15]
    
    print(f"Identified top 15 longest traces (re-analyzing with SyGuS + Validation):")
    
    detailed_results = []
    for c in target_candidates:
        path = get_benchmark_path(c['benchmark'], c['bitwidth'])
        if not os.path.exists(path):
            print(f"Warning: File not found {path}")
            continue
            
        res = run_detailed_analysis(path)
        if res:
            res['benchmark'] = os.path.basename(path) # Ensure full filename is kept
            res['bitwidth'] = c['bitwidth']
            detailed_results.append(res)
            
    generate_latex(detailed_results)

if __name__ == "__main__":
    main()
