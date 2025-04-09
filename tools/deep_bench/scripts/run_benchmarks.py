#!/usr/bin/env python3

import argparse
import concurrent.futures
import csv
import datetime
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path
from tqdm import tqdm

class BenchmarkResult:
    def __init__(self, filename, status, runtime, result="", error=""):
        self.filename = filename
        self.status = status
        self.runtime = runtime
        self.result = result
        self.error = error

def parse_args():
    parser = argparse.ArgumentParser(description='Run FreqHorn benchmarks')
    parser.add_argument('--config', 
                      help='JSON config file with multiple test configurations')
    parser.add_argument('--test',
                      help='Name of specific test configuration to run from config file')
    parser.add_argument('--tool', default='./tools/deep/freqhorn',
                      help='Path to the FreqHorn executable (default if not in config)')
    parser.add_argument('--benchmarks', default='../bench_horn_bv_translated/',
                      help='Benchmark directory (default if not in config)')
    parser.add_argument('--timeout', type=int, default=2,
                      help='Timeout in seconds (default if not in config)')
    parser.add_argument('--flags', default='--bv',
                      help='Additional flags (default if not in config)') 
    parser.add_argument('--pattern', default='*.smt2',
                      help='File pattern to match benchmarks')
    parser.add_argument('--tag', default='',
                      help='Additional tag for output files')
    return parser.parse_args()

def load_configs(config_file, default_args):
    if not config_file:
        # Use command line args as single config
        return [{
            'name': default_args.tag or 'default',
            'tool': default_args.tool,
            'benchmarks': default_args.benchmarks,
            'timeout': default_args.timeout,
            'flags': default_args.flags,
            'pattern': default_args.pattern
        }]
    
    with open(config_file) as f:
        all_configs = json.load(f)['configs']
    
    # If test name specified, filter configs
    if default_args.test:
        all_configs = [c for c in all_configs if c['name'] == default_args.test]
        if not all_configs:
            raise ValueError(f"Test configuration '{default_args.test}' not found in config file")
    
    # Fill in defaults for any missing values
    for config in all_configs:
        config.setdefault('tool', default_args.tool)
        config.setdefault('benchmarks', default_args.benchmarks)
        config.setdefault('timeout', default_args.timeout)
        config.setdefault('flags', default_args.flags)
        config.setdefault('pattern', default_args.pattern)
    
    return all_configs

def setup_output_dirs(timestamp):
    base_dir = Path('Testing')
    
    dirs = {
        'results': base_dir / 'results',
        'output': base_dir / 'output' / f'output_{timestamp}',
        'stderr': base_dir / 'stderr_output'
    }
    
    for d in dirs.values():
        d.mkdir(parents=True, exist_ok=True)
        
    return dirs

def run_benchmark(args):
    tool, bench_file, timeout, tool_flags = args
    output_file = f"output_{os.path.basename(bench_file)}"
    err_file = f"stderr_{os.path.basename(bench_file)}"
    
    try:
        start_time = time.time()
        cmd = [tool] + tool_flags.split() + [str(bench_file)]
        
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        runtime = time.time() - start_time
        
        # Analyze output
        output = proc.stdout
        if "Success!" in output:
            status = "Success!"
            result = "\n".join(output.split("Success!")[1].strip().split("\n")[-10:])
        elif "unknown" in output:
            status = "unknown"
            result = ""
        elif "unsupported" in output:
            status = "unsupported"
            result = ""
        else:
            status = "Error"
            result = "\n".join(re.findall(r"ERROR.*(?:\n.*){0,9}", output)[-10:])
            
        return BenchmarkResult(bench_file, status, runtime, result, proc.stderr)
        
    except subprocess.TimeoutExpired:
        return BenchmarkResult(bench_file, "Timeout", timeout)
    except Exception as e:
        return BenchmarkResult(bench_file, "Crash", 0, error=str(e))

def run_config(config, dirs, timestamp):
    bench_dir = Path(config['benchmarks'])
    bench_files = list(bench_dir.glob(config['pattern']))
    
    if not bench_files:
        print(f"No benchmark files found for config '{config['name']}'")
        return []
    
    print(f"\nRunning configuration '{config['name']}' on {len(bench_files)} benchmarks...")
    
    run_args = [(config['tool'], f, config['timeout'], config['flags']) 
                for f in bench_files]
    
    results = []
    with concurrent.futures.ProcessPoolExecutor() as executor:
        for result in tqdm(executor.map(run_benchmark, run_args),
                          total=len(bench_files), unit="test"):
            results.append(result)
            
            # Save detailed output
            output_path = dirs['output'] / config['name']
            output_path.mkdir(exist_ok=True)
            
            with open(output_path / f"output_{os.path.basename(result.filename)}", 'w') as f:
                f.write(f"Status: {result.status}\n")
                f.write(f"Runtime: {result.runtime:.2f}s\n\n")
                f.write(f"Result:\n{result.result}\n\n")
                f.write(f"Errors:\n{result.error}")
    
    return results

def write_comparative_results(all_results, dirs, timestamp):
    results_file = dirs['results'] / f'results_{timestamp}.csv'
    
    with open(results_file, 'w', newline='') as f:
        writer = csv.writer(f)
        
        # Write header with configuration names
        header = ["Benchmark"]
        for config_name in all_results.keys():
            header.extend([f"{config_name} Status", f"{config_name} Time"])
        writer.writerow(header)
        
        # Get unified set of benchmarks
        all_benchmarks = set()
        for results in all_results.values():
            all_benchmarks.update(os.path.basename(r.filename) for r in results)
        
        # Write results for each benchmark
        for bench in sorted(all_benchmarks):
            row = [bench]
            for config_name, results in all_results.items():
                result = next((r for r in results 
                             if os.path.basename(r.filename) == bench), None)
                if result:
                    row.extend([result.status, f"{result.runtime:.2f}"])
                else:
                    row.extend(["N/A", "N/A"])
            writer.writerow(row)
        
        # Write statistics for each configuration
        writer.writerow([])
        writer.writerow(["Statistics"])
        
        stat_rows = {
            "Total": lambda rs: len(rs),
            "Successful": lambda rs: sum(1 for r in rs if r.status == "Success!"),
            "Timeouts": lambda rs: sum(1 for r in rs if r.status == "Timeout"),
            "Crashes": lambda rs: sum(1 for r in rs if r.status == "Crash"),
            "Avg Runtime": lambda rs: f"{sum(r.runtime for r in rs)/len(rs):.2f}s"
        }
        
        for stat_name, stat_func in stat_rows.items():
            row = [stat_name]
            for results in all_results.values():
                row.extend([stat_func(results), ""])
            writer.writerow(row)

def main():
    args = parse_args()
    timestamp = datetime.datetime.now().strftime('%m-%d-%Y_%H-%M-%S')
    
    # Load test configurations
    configs = load_configs(args.config, args)
    
    # Setup output directories
    dirs = setup_output_dirs(timestamp)
    
    # Run all configurations in parallel
    all_results = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(configs)) as executor:
        future_to_config = {
            executor.submit(run_config, config, dirs, timestamp): config
            for config in configs
        }
        
        for future in concurrent.futures.as_completed(future_to_config):
            config = future_to_config[future]
            try:
                results = future.result()
                all_results[config['name']] = results
            except Exception as e:
                print(f"Config '{config['name']}' failed: {e}")
    
    # Write comparative results
    write_comparative_results(all_results, dirs, timestamp)
    
    print(f"\nResults saved to {dirs['results']}")
    print(f"Detailed outputs saved to {dirs['output']}")
    
    return 0

if __name__ == "__main__":
    sys.exit(main())
