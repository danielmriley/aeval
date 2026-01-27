#!/usr/bin/env python3
"""
Run CBMC on all s_split C benchmarks with memory and time protections.
Collects timing information and unrolling information.
"""

import os
import subprocess
import time
import csv
from pathlib import Path

# Configuration
BENCH_DIR = "bench_c_s_split"
TIMEOUT_SECONDS = 300  # 5 minutes per benchmark
MEMORY_LIMIT_MB = 8192  # 8GB memory limit
UNWIND_VALUES = [1000000]  # Increased unwind limit to 1 million

def run_cbmc_with_limits(file_path, unwind, timeout=TIMEOUT_SECONDS, mem_limit_mb=MEMORY_LIMIT_MB):
    """
    Run CBMC with memory and time limits.
    Returns: (status, time_taken, output, error)
    """
    cmd = [
        'bash', '-c',
        f'ulimit -v {mem_limit_mb * 1024} && ulimit -m {mem_limit_mb * 1024} && '
        f'cbmc {file_path} --unwind {unwind} --unwinding-assertions --trace'
    ]
    
    start_time = time.time()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=os.path.dirname(os.path.abspath(__file__))
        )
        elapsed = time.time() - start_time
        
        # Determine status
        if result.returncode == 0:
            status = "SUCCESS"
        elif result.returncode == 10:
            status = "VERIFICATION_FAILED"
        elif result.returncode == 6:
            status = "PARSE_ERROR"
        else:
            status = f"ERROR_CODE_{result.returncode}"
        
        return status, elapsed, result.stdout, result.stderr
        
    except subprocess.TimeoutExpired:
        elapsed = time.time() - start_time
        return "TIMEOUT", elapsed, "", "Timeout expired"
    except MemoryError:
        elapsed = time.time() - start_time
        return "MEMORY_ERROR", elapsed, "", "Memory limit exceeded"
    except Exception as e:
        elapsed = time.time() - start_time
        return "EXCEPTION", elapsed, "", str(e)

def parse_cbmc_output(output):
    """
    Parse CBMC output to extract useful information.
    Returns: dict with parsed info
    """
    info = {
        'assertions_total': 0,
        'assertions_success': 0,
        'assertions_failed': 0,
        'unwinding_failed': False,
        'iterations': 0,
        'counterexample_found': False,
        'trace_length': 0
    }
    
    lines = output.split('\n')
    for line in lines:
        if 'unwinding assertion' in line and 'FAILURE' in line:
            info['unwinding_failed'] = True
        if 'assertion' in line and 'SUCCESS' in line:
            info['assertions_success'] += 1
            info['assertions_total'] += 1
        if 'assertion' in line and 'FAILURE' in line:
            info['assertions_failed'] += 1
            info['assertions_total'] += 1
        if 'of' in line and 'failed' in line and 'iterations' in line:
            # Parse "** X of Y failed (Z iterations)"
            parts = line.split()
            for i, part in enumerate(parts):
                if part == 'iterations)':
                    try:
                        info['iterations'] = int(parts[i-1].strip('('))
                    except:
                        pass
        if 'VERIFICATION FAILED' in line:
            info['counterexample_found'] = True
        
        # Count trace states
        if line.startswith('State ') and 'file' in line:
            info['trace_length'] += 1
    
    return info

def main():
    bench_path = Path(BENCH_DIR)
    if not bench_path.exists():
        print(f"Error: {BENCH_DIR} does not exist")
        return
    
    c_files = sorted(bench_path.glob("s_split_*_c.c"))
    print(f"Found {len(c_files)} C files to test")
    
    output_file = "cbmc_benchmark_results.csv"
    processed_benchmarks = set()

    # Check for existing results to resume
    if os.path.exists(output_file):
        print(f"Checking existing results in {output_file}...")
        try:
            with open(output_file, 'r') as f:
                reader = csv.DictReader(f)
                for row in reader:
                    # Check if this row matches our current configuration
                    if int(row.get('unwind', 0)) == UNWIND_VALUES[0]: # Check if it is the 1M run
                         processed_benchmarks.add(row['benchmark'])
        except Exception as e:
            print(f"Warning: Could not read existing results: {e}")
            
    print(f"Resuming... {len(processed_benchmarks)} benchmarks already processed.")
    
    # Define fieldnames
    sample_result = {
        'benchmark': '', 'file': '', 'unwind': 0, 'status': '', 'time_seconds': 0,
        'unwinding_failed': False, 'iterations': 0, 'counterexample_found': False,
        'trace_length': 0, 'assertions_total': 0, 'assertions_success': 0, 'assertions_failed': 0
    }
    fieldnames = list(sample_result.keys())

    # Create file and write header if it doesn't exist
    if not os.path.exists(output_file):
         with open(output_file, 'w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()

    for c_file in c_files:
        benchmark_name = c_file.stem
        
        if benchmark_name in processed_benchmarks:
            print(f"Skipping {benchmark_name} (already done)")
            continue

        print(f"\n{'='*60}")
        print(f"Testing: {benchmark_name}")
        print(f"{'='*60}")
        
        # Try progressive unwind values until we get a result or hit limits
        for unwind in UNWIND_VALUES:
            print(f"  Unwind={unwind}... ", end='', flush=True)
            
            status, elapsed, stdout, stderr = run_cbmc_with_limits(
                str(c_file), 
                unwind,
                timeout=TIMEOUT_SECONDS,
                mem_limit_mb=MEMORY_LIMIT_MB
            )
            
            print(f"{status} ({elapsed:.2f}s)")
            
            # Parse output
            parsed = parse_cbmc_output(stdout)
            
            result = {
                'benchmark': benchmark_name,
                'file': c_file.name,
                'unwind': unwind,
                'status': status,
                'time_seconds': round(elapsed, 3),
                'unwinding_failed': parsed['unwinding_failed'],
                'iterations': parsed['iterations'],
                'counterexample_found': parsed['counterexample_found'],
                'trace_length': parsed['trace_length'],
                'assertions_total': parsed['assertions_total'],
                'assertions_success': parsed['assertions_success'],
                'assertions_failed': parsed['assertions_failed']
            }
            
            # Append result immediately
            with open(output_file, 'a', newline='') as f:
                writer = csv.DictWriter(f, fieldnames=fieldnames)
                writer.writerow(result)
            
            # Print trace length found
            if result['trace_length'] > 0:
                print(f"    ✓ Trace found: length {result['trace_length']}")
            
            break

    print(f"\n{'='*60}")
    print(f"All benchmarks processed. Results saved to {output_file}")
    print(f"{'='*60}")

if __name__ == "__main__":
    main()
