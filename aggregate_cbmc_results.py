import csv
import os

# Input files
RESULTS_20K = "build/Testing/results/cbmc_benchmark_results_20k.csv"
RESULTS_SMART = "cbmc_smart_results.csv"
OUTPUT_FILE = "cbmc_aggregated_results.csv"

def load_20k_results(filepath):
    data = {}
    try:
        with open(filepath, 'r') as f:
            reader = csv.DictReader(f)
            for row in reader:
                filename = row['file']
                status = row['status']
                time_s = float(row['time_seconds'])
                trace_len = row['trace_length']
                
                # Normalize status
                final_status = "TIMEOUT"
                if status == "VERIFICATION_FAILED":
                    final_status = "SUCCESS"
                elif status == "VERIFICATION_SUCCESSFUL": # Should not happen for these bugs
                    final_status = "SAFE" 
                
                data[filename] = {
                    "source": "20k_Run",
                    "status": final_status,
                    "time": time_s,
                    "details": f"len={trace_len}"
                }
    except FileNotFoundError:
        print(f"Warning: {filepath} not found.")
    return data

def load_smart_results(filepath):
    data = {}
    try:
        with open(filepath, 'r') as f:
            reader = csv.DictReader(f)
            for row in reader:
                filename = row['File']
                status = row['Status']
                time_s = float(row['Time'])
                mode = row['Mode']
                
                # Normalize status
                final_status = "TIMEOUT"
                if status == "BUG_FOUND":
                    final_status = "SUCCESS"
                elif status == "SAFE_WITHIN_BOUND":
                    final_status = "SAFE"
                
                data[filename] = {
                    "source": f"Smart_{mode}",
                    "status": final_status,
                    "time": time_s,
                    "details": f"Mode={mode}"
                }
    except FileNotFoundError:
        print(f"Warning: {filepath} not found.")
    return data

def main():
    res_20k = load_20k_results(RESULTS_20K)
    res_smart = load_smart_results(RESULTS_SMART)
    
    # Get all unique filenames
    all_files = sorted(list(set(res_20k.keys()) | set(res_smart.keys())))
    
    aggregated = []
    
    # Statistics
    total_benchmarks = 0
    total_success = 0
    improved_by_smart = 0
    
    for f in all_files:
        r1 = res_20k.get(f, {"status": "MISSING", "time": 0, "source": "N/A"})
        r2 = res_smart.get(f, {"status": "MISSING", "time": 0, "source": "N/A"})
        
        total_benchmarks += 1
        
        # Decision Logic: Prefer SUCCESS
        best = r1
        
        # If Smart is Success, it usually wins unless 20k was also Success and faster?
        # Actually usually if Smart found it, it used a specialized strategy. Not always faster.
        # But if 20k failed and Smart succeeded, Smart wins.
        
        if r2["status"] == "SUCCESS":
            if r1["status"] != "SUCCESS":
                best = r2
                improved_by_smart += 1
            else:
                # Both succeeded. Pick faster?
                if r2["time"] < r1["time"]:
                    best = r2
                else:
                    best = r1
        elif r1["status"] == "SUCCESS":
            best = r1 # Smart failed, 20k succeeded
        else:
            # Both failed. 
            best = r2 # Default to the smart run info as it's more recent
            
        if best["status"] == "SUCCESS":
            total_success += 1
            
        aggregated.append({
            "File": f,
            "Parameters": r1["status"], # 20k Status
            "Smart": r2["status"], # Smart Status
            "Final_Status": best["status"],
            "Time": f"{best['time']:.2f}",
            "Source": best["source"]
        })

    # Write CSV
    with open(OUTPUT_FILE, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=["File", "Parameters", "Smart", "Final_Status", "Time", "Source"])
        writer.writeheader()
        writer.writerows(aggregated)
        
    print(f"Aggregated results saved to {OUTPUT_FILE}")
    print("-" * 60)
    print(f"Total Benchmarks: {total_benchmarks}")
    print(f"Total Success:    {total_success}")
    print(f"Success Rate:     {(total_success/total_benchmarks)*100:.1f}%")
    print(f"New Solved by Smart Strategy: {improved_by_smart}")
    print("-" * 60)
    
    # List still failing
    print("Remaining Failures:")
    for row in aggregated:
        if row["Final_Status"] != "SUCCESS":
             print(f"- {row['File']} (20k: {row['Parameters']}, Smart: {row['Smart']})")

if __name__ == "__main__":
    main()
