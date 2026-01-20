import os
import subprocess
import time
import re
import sys

def get_bitwidth(filename):
    # Try to extract bitwidth from filename (e.g., bv32_...)
    match = re.search(r'bv(\d+)', filename)
    if match:
        return int(match.group(1))
    # Check for bvzextPREFIX
    match = re.search(r'bvzext(\d+)', filename)
    if match:
        return int(match.group(1))
    return 0 # Unknown, include by default? Or maybe assume small?

def run_test(cmd, timeout=60):
    start_time = time.time()
    try:
        # Use stdbuf to unbuffer output if possible, but python subprocess captures it anyway
        process = subprocess.Popen(
            cmd, 
            shell=True, 
            stdout=subprocess.PIPE, 
            stderr=subprocess.STDOUT, 
            universal_newlines=True,
            preexec_fn=os.setsid # To allow killing the whole group on timeout
        )
        
        # We can't easily use the 'timeout' command in the shell string AND get the return code 
        # distinct from the tool's return code reliably across all systems, 
        # so we'll implement timeout in python.
        
        try:
            stdout, _ = process.communicate(timeout=timeout)
            return_code = process.returncode
            duration = time.time() - start_time
        except subprocess.TimeoutExpired:
            os.killpg(os.getpgid(process.pid), 15) # SIGTERM
            stdout, _ = process.communicate()
            return_code = 124 # mimic timeout command
            duration = timeout
            
    except Exception as e:
        return "ERROR", 0, str(e)
    
    # Analyze output
    if "Synthesized functions:" in stdout:
        return "SUCCESS", duration, stdout
    elif "INFEASIBLE" in stdout or "unsat" in stdout.lower(): # CVC5 might say unsat
        return "INFEASIBLE", duration, stdout
    elif return_code == 124: # Timeout
        return "TIMEOUT", duration, stdout
    elif "CVC5 exited with status" in stdout:
        # Check if CVC5 timed out or failed
        if "31744" in stdout or "124" in stdout: # 124<<8 = 31744
            return "TIMEOUT", duration, stdout
        return "FAIL", duration, stdout
    else:
        return "FAIL", duration, stdout

def main():
    root_dir = "bench_horn_ccex"
    executable = "./build/tools/deep/freqhorn"
    
    files = []
    print(f"Scanning {root_dir}...")
    
    for dirpath, dirnames, filenames in os.walk(root_dir):
        for f in filenames:
            if not f.endswith(".smt2"):
                continue
            if "_ccex.smt2" in f:
                continue
            
            # Filter by bitwidth
            bw = get_bitwidth(f)
            if bw > 64:
                continue
                
            full_path = os.path.join(dirpath, f)
            files.append(full_path)
    
    files.sort()
    print(f"Found {len(files)} benchmarks <= 64 bits.")
    
    results = []
    
    print(f"{'Benchmark':<40} | {'PBE Status':<10} | {'PBE Time':<8} | {'TR Status':<10} | {'TR Time':<8}")
    print("-" * 90)
    
    stats = {
        "PBE": {"SUCCESS": 0, "INFEASIBLE": 0, "TIMEOUT": 0, "FAIL": 0, "ERROR": 0},
        "TR": {"SUCCESS": 0, "INFEASIBLE": 0, "TIMEOUT": 0, "FAIL": 0, "ERROR": 0}
    }
    
    for f in files:
        basename = os.path.basename(f)
        parent = os.path.basename(os.path.dirname(f))
        display_name = f"{parent}/{basename}"
        
        # Print start marker
        # print(f"Processing {display_name}...", end="\r") 
        
        # Run PBE
        cmd_pbe = f"{executable} --sygus --sygus-run {f}"
        status_pbe, time_pbe, _ = run_test(cmd_pbe, timeout=70) # Give slightly more than 60s
        stats["PBE"][status_pbe] += 1
        
        # Run TR
        cmd_tr = f"{executable} --sygus-tr --sygus-run {f}"
        status_tr, time_tr, _ = run_test(cmd_tr, timeout=70) # Give slightly more than 60s
        stats["TR"][status_tr] += 1
        
        print(f"{display_name:<40} | {status_pbe:<10} | {time_pbe:>8.2f} | {status_tr:<10} | {time_tr:>8.2f}")
        sys.stdout.flush()
        
        results.append({
            "file": f,
            "pbe_status": status_pbe,
            "pbe_time": time_pbe,
            "tr_status": status_tr,
            "tr_time": time_tr
        })
        
    print("-" * 90)
    print("Summary:")
    print(f"{'Mode':<10} | {'SUCCESS':<8} | {'INFEASIBLE':<10} | {'TIMEOUT':<8} | {'FAIL':<8}")
    print("-" * 50)
    for mode in ["PBE", "TR"]:
        s = stats[mode]
        print(f"{mode:<10} | {s['SUCCESS']:<8} | {s['INFEASIBLE']:<10} | {s['TIMEOUT']:<8} | {s['FAIL']:<8}")

if __name__ == "__main__":
    main()
