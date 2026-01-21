
import os
import subprocess
import csv

def main():
    success_file = "bv16_results.csv"  # Was generated earlier
    bench_root = "bench_horn_split_cex_bv"
    
    # Reload successes
    targets = []
    with open(success_file, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row['Result'] == 'SUCCESS':
                targets.append((row['Benchmark'], os.path.join(bench_root, row['Benchmark'].replace("bv16_", "").replace(".smt2", ""), row['Benchmark'])))

    print(f"Checking {len(targets)} successful benchmarks for simulation hit vs extrapolation...")
    
    extrapolated_cases = []
    
    for (name, path) in targets:
        cmd = ["./build/tools/deep/freqhorn", "--sygus", "--sygus-run", path]
        try:
            # Short timeout as these are successes
            res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20, text=True)
            output = res.stdout
            
            sim_hit = "Bad state reached" in output
            sygus_hit = "Synthesized functions" in output
            
            if sygus_hit and not sim_hit:
                print(f"[EXTRAPOLATION] {name}: Synthesized function but Simulator didn't hit Error within N steps.")
                extrapolated_cases.append(name)
            elif sygus_hit and sim_hit:
                # print(f"[VERIFIED] {name}: Simulator hit Error.")
                pass
            else:
                print(f"[ERROR] {name}: Failed to reproduce success?")
                
        except Exception as e:
            print(f"Error running {name}: {e}")
            
    print("-" * 40)
    if extrapolated_cases:
        print(f"Found {len(extrapolated_cases)} cases relying on extrapolation:")
        for c in extrapolated_cases:
            print(f" - {c}")
    else:
        print("All successes were found by the concrete simulator (Step < 16). No extrapolation gap exists in this set.")

if __name__ == "__main__":
    main()
