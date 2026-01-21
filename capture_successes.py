
import os
import csv
import subprocess

def main():
    results_file = "bv16_results.csv"
    bench_root = "bench_horn_split_cex_bv"
    output_file = "success_dump.txt"
    
    successes = []
    with open(results_file, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row['Result'] == 'SUCCESS':
                bench_name = row['Benchmark'] # bv16_s_split_03.smt2
                # Need to find full path.
                # Structure: bench_horn_split_cex_bv/s_split_03/bv16_s_split_03.smt2
                # Extract ID
                clean_name = bench_name.replace("bv16_", "").replace(".smt2", "")
                successes.append((clean_name, bench_name))
                
    successes.sort()
    
    with open(output_file, 'w') as out:
        out.write(f"Analyzing {len(successes)} successful benchmarks\n")
        out.write("="*60 + "\n\n")
        
        for (bench_id, filename) in successes:
            full_path = os.path.join(bench_root, bench_id, filename)
            
            out.write(f"=== {bench_id} ===\n")
            out.write(f"Path: {full_path}\n")
            
            cmd = ["./build/tools/deep/freqhorn", "--sygus", "--sygus-run", full_path]
            try:
                # Add timeout slightly higher to be safe
                proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=25, text=True)
                output = proc.stdout + proc.stderr
                
                # Extract just the function definition(s)
                # Look for (define-fun ...)
                lines = output.splitlines()
                fun_lines = []
                capturing = False
                for line in lines:
                    if "(define-fun" in line:
                        capturing = True
                    if capturing:
                        fun_lines.append(line)
                        if line.strip().endswith(")"): # Simple heuristic for one-liners or end of block?
                            # SyGuS output is properly parenthesized.
                            pass
                            
                # Just dumping the raw output section containing synthesized functions
                if "Synthesized functions:" in output:
                    start_idx = output.find("Synthesized functions:")
                    relevant_output = output[start_idx:]
                    out.write(relevant_output + "\n")
                else:
                    out.write("No 'Synthesized functions:' marker found in output.\n")
                    if proc.returncode != 0:
                        out.write(f"Process failed with code {proc.returncode}\n")
                        
            except subprocess.TimeoutExpired:
                out.write("Timeout during re-run analysis.\n")
            except Exception as e:
                out.write(f"Error: {e}\n")
                
            out.write("\n" + "-"*40 + "\n\n")

if __name__ == "__main__":
    main()
