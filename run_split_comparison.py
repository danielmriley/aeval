
import os
import subprocess
import time
import csv

def main():
    bench_dir = "bench_horn_split_cex_bv"
    timeout = 60
    
    # Collect all benchmarks for 16, 32, 64 bits
    benchmarks = []
    for root, dirs, files in os.walk(bench_dir):
        for f in files:
            if (f.startswith("bv16_") or f.startswith("bv32_") or f.startswith("bv64_")) and f.endswith(".smt2"):
                benchmarks.append(os.path.join(root, f))
    
    benchmarks.sort()
    
    results = []
    
    print(f"Found {len(benchmarks)} benchmarks. Running comparison tests (PBE vs TR) with {timeout}s timeout...")
    print(f"{'Benchmark':<50} | {'PBE':<10} | {'Time':<8} | {'TR':<10} | {'Time':<8}")
    print("-" * 100)
    
    for bench in benchmarks:
        rel_path = os.path.relpath(bench, bench_dir)
        row = {"Benchmark": rel_path}
        
        # 1. Run PBE
        cmd_pbe = ["./build/tools/deep/freqhorn", "--sygus", "--sygus-run", bench]
        start_time = time.time()
        pbe_status = "FAIL"
        pbe_time = 0.0
        try:
            res_pbe = subprocess.run(cmd_pbe, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout, text=True)
            elapsed = time.time() - start_time
            output = res_pbe.stdout + res_pbe.stderr
            if "Synthesized functions:" in output:
                pbe_status = "SUCCESS"
            pbe_time = elapsed
        except subprocess.TimeoutExpired:
            pbe_status = "TIMEOUT"
            pbe_time = timeout
            
        row["PBE_Status"] = pbe_status
        row["PBE_Time"] = f"{pbe_time:.2f}"
        
        # 2. Run TR
        cmd_tr = ["./build/tools/deep/freqhorn", "--sygus-tr", "--sygus-run", bench]
        start_time = time.time()
        tr_status = "FAIL"
        tr_time = 0.0
        try:
            res_tr = subprocess.run(cmd_tr, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout, text=True)
            elapsed = time.time() - start_time
            output = res_tr.stdout + res_tr.stderr
            if "Synthesized functions:" in output:
                tr_status = "SUCCESS"
            tr_time = elapsed
        except subprocess.TimeoutExpired:
            tr_status = "TIMEOUT"
            tr_time = timeout
            
        row["TR_Status"] = tr_status
        row["TR_Time"] = f"{tr_time:.2f}"
        
        results.append(row)
        print(f"{rel_path:<50} | {pbe_status:<10} | {pbe_time:<8.2f} | {tr_status:<10} | {tr_time:<8.2f}")

    # Write CSV
    with open("split_cex_results.csv", "w", newline='') as csvfile:
        fieldnames = ["Benchmark", "PBE_Status", "PBE_Time", "TR_Status", "TR_Time"]
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        writer.writeheader()
        for r in results:
            writer.writerow(r)

if __name__ == "__main__":
    main()
