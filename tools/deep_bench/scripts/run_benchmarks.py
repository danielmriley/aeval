#!/usr/bin/env python3

import argparse
import concurrent.futures
import csv
import datetime
import json
import multiprocessing
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
                        action='append',
                        help='Name of specific test configuration(s) to run from config file')
    parser.add_argument('--tool', default='./tools/deep/freqhorn',
                        help='Path to the FreqHorn executable (default if not in config)')
    parser.add_argument('--benchmarks', default='../bench_horn_bv_translated/',
                        help='Benchmark directory (default if not in config)')
    parser.add_argument('--timeout', type=int, default=2,
                        help='Timeout in seconds (default if not in config)')
    parser.add_argument('--flags', default='',
                        help='Additional flags (default if not in config)') 
    parser.add_argument('--pattern', default='*.smt2',
                        help='File pattern to match benchmarks')
    parser.add_argument('--tag', default='',
                        help='Additional tag for output files')
    return parser.parse_args()

def load_configs(config_file, default_args):
    if not config_file:
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
    
    if default_args.test:
        specified_tests = set(default_args.test)
        all_configs = [c for c in all_configs if c['name'] in specified_tests]
        if not all_configs:
            raise ValueError(f"None of the specified test configurations {list(specified_tests)} found in config file")
        found_tests = {c['name'] for c in all_configs}
        missing_tests = specified_tests - found_tests
        if missing_tests:
             print(f"Warning: The following specified test configurations were not found: {list(missing_tests)}")

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
    result = BenchmarkResult(bench_file, "Unknown", 0)
    tool_name = os.path.basename(tool) 
    result.tool_info = {
        'tool': tool,
        'flags': tool_flags,
        'benchmarks': str(Path(bench_file).parent)
    }
    
    try:
        start_time = time.time()
        cmd_flags = tool_flags.split() if tool_flags else []
        cmd = [tool] + cmd_flags + [str(bench_file)]
        
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        runtime = time.time() - start_time
        
        output = proc.stdout
        
        if tool_name == "z3":
            if "unsat" in output:
                result.status = "Success"
                result.result = "unsat"
            elif "sat" in output:
                result.status = "Error"
                result.result = "sat"
            elif "unknown" in output:
                 result.status = "unknown"
                 result.result = "unknown"
            else:
                result.status = "Error" 
                result.result = output[-500:] 
                result.error = proc.stderr[-500:] if proc.stderr else ""
        else:
            if not output:
                result.status = "No Output"
                result.result = ""
            elif "Success" in output:
                result.status = "Success"
                parts = output.split("Success", 1)
                result.result = "\n".join(parts[1].strip().split("\n")[-10:]) if len(parts) > 1 else ""
            elif "unknown" in output:
                result.status = "unknown"
                result.result = ""
            elif "unsupported" in output:
                result.status = "unsupported"
                result.result = ""
            else:
                error_lines = re.findall(r"ERROR.*(?:\n.*){0,9}", output)
                if error_lines:
                    result.status = "Error"
                    result.result = "\n".join(error_lines[-1].split('\n')[:10]) 
                else:
                    result.status = "Unknown Status" 
                    result.result = output[-500:] 
        result.runtime = runtime
        result.error = proc.stderr 
        return result
        
    except subprocess.TimeoutExpired:
        result.status = "Timeout"
        result.runtime = timeout
        return result
    except Exception as e:
        result.status = "Crash"
        result.runtime = 0
        result.error = str(e)
        return result

def run_config(config, dirs, timestamp, position, progress_dict, message_list):
    bench_dir = Path(config['benchmarks'])
    bench_files = list(bench_dir.glob(config['pattern'])) 
    
    if not bench_files:
        message_list.append(f"No benchmark files found for config '{config['name']}' in {bench_dir} matching '{config['pattern']}'")
        return config['name'], []
    
    run_args = [(config['tool'], f, config['timeout'], config['flags']) 
                for f in bench_files]
    
    results = []
    config_name = config['name']
    progress_dict[config_name] = 0  # Initialize progress
    
    message_list.append(f"Starting configuration '{config_name}' ({len(bench_files)} benchmarks)...")
    
    for i, args in enumerate(run_args):
        try:
            result = run_benchmark(args)
            results.append(result)
            
            output_path = dirs['output'] / config_name
            output_path.mkdir(parents=True, exist_ok=True)
            
            with open(output_path / f"output_{os.path.basename(result.filename)}", 'w') as f:
                f.write(f"Status: {result.status}\n")
                f.write(f"Runtime: {result.runtime:.2f}s\n\n")
                f.write(f"Result:\n{result.result}\n\n")
                f.write(f"Errors:\n{result.error}")
            
            # Update progress
            progress_dict[config_name] = i + 1
        except Exception as exc:
            bench_file = args[1]
            message_list.append(f"Benchmark {os.path.basename(bench_file)} generated an exception: {exc}")
            results.append(BenchmarkResult(bench_file, "Executor Crash", 0, error=str(exc)))
            progress_dict[config_name] = i + 1  # Still increment progress on failure

    return config_name, results

def write_comparative_results(all_results, dirs, timestamp):
    results_file = dirs['results'] / f'results_{timestamp}.csv'
    
    configs_by_benchdir = {}
    for config_name, results in all_results.items():
        if not results:
            continue
        bench_dir = results[0].tool_info['benchmarks']
        if bench_dir not in configs_by_benchdir:
            configs_by_benchdir[bench_dir] = {}
        configs_by_benchdir[bench_dir][config_name] = results

    with open(results_file, 'w', newline='') as f:
        writer = csv.writer(f)
        
        for bench_dir, grouped_configs in configs_by_benchdir.items():
            writer.writerow([])
            writer.writerow([f"Benchmark Directory: {bench_dir}"])
            writer.writerow([])
            
            writer.writerow(["Configuration"] + list(grouped_configs.keys()))
            writer.writerow(["Tool"] + [results[0].tool_info['tool'] for results in grouped_configs.values()])
            writer.writerow(["Flags"] + [results[0].tool_info['flags'] for results in grouped_configs.values()])
            writer.writerow([])
            
            all_benchmarks = set()
            for results in grouped_configs.values():
                all_benchmarks.update(os.path.basename(r.filename) for r in results)
            
            header = ["Benchmark"]
            for config_name in grouped_configs.keys():
                header.extend([f"{config_name} Status", f"{config_name} Time"])
            writer.writerow(header)
            
            for bench in sorted(all_benchmarks):
                row = [bench]
                for results in grouped_configs.values():
                    result = next((r for r in results if os.path.basename(r.filename) == bench), None)
                    if result:
                        row.extend([result.status, f"{result.runtime:.2f}"])
                    else:
                        row.extend(["N/A", "N/A"])
                writer.writerow(row)
            
            writer.writerow([])
            writer.writerow(["Statistics"])
            
            stats_rows = {
                "Total Benchmarks": lambda rs: len(rs),
                "Successful": lambda rs: sum(1 for r in rs if r.status == "Success"),
                "Timeouts": lambda rs: sum(1 for r in rs if r.status == "Timeout"), 
                "Crashes": lambda rs: sum(1 for r in rs if r.status == "Crash"),
                "Avg Runtime": lambda rs: f"{sum(r.runtime for r in rs)/len(rs):.2f}s"
            }
            
            for stat_name, stat_func in stats_rows.items():
                row = [stat_name]
                for results in grouped_configs.values():
                    row.append(stat_func(results))
                writer.writerow(row)
            
            writer.writerow([])
            writer.writerow(["=" * 50])

def main():
    args = parse_args()
    timestamp = datetime.datetime.now().strftime('%m-%d-%Y_%H-%M-%S')
    
    try:
        configs = load_configs(args.config, args)
    except (FileNotFoundError, ValueError, json.JSONDecodeError) as e:
        print(f"Error loading configuration: {e}")
        return 1
        
    dirs = setup_output_dirs(timestamp)
    
    all_results = {}
    
    max_workers = max(1, os.cpu_count() - 2 if os.cpu_count() else 1) 
    print(f"Running up to {max_workers} configurations in parallel.")
    print()

    # Set up multiprocessing manager for shared progress and messages
    manager = multiprocessing.Manager()
    progress_dict = manager.dict()  # Tracks completed benchmarks per config
    message_list = manager.list()   # Collects messages from workers
    
    # Submit all configurations to the executor
    with concurrent.futures.ProcessPoolExecutor(max_workers=max_workers) as executor:
        future_to_config = {
            executor.submit(run_config, config, dirs, timestamp, idx + 1, progress_dict, message_list): config['name']
            for idx, config in enumerate(configs)
        }
        
        # Initialize progress bars in the main process
        bars = {
            config['name']: tqdm(
                total=len(list(Path(config['benchmarks']).glob(config['pattern']))),
                desc=f"Config {config['name']:<10}",
                unit="test",
                position=idx + 1,
                leave=True
            )
            for idx, config in enumerate(configs)
        }
        overall_bar = tqdm(
            total=len(configs),
            desc="Overall Progress",
            unit="config",
            position=0,
            leave=True
        )
        
        # Process messages and update progress bars
        completed_configs = 0
        while completed_configs < len(configs):
            # Display new messages
            while message_list:
                print(message_list.pop(0))
            
            # Update each configuration's progress bar
            for config_name, bar in bars.items():
                current_progress = progress_dict.get(config_name, 0)
                bar.n = current_progress
                bar.refresh()
            
            # Check completed futures and update overall progress
            done, _ = concurrent.futures.wait(future_to_config, timeout=0.1, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                config_name = future_to_config[future]
                try:
                    returned_name, results_list = future.result()
                    if returned_name == config_name:
                        all_results[config_name] = results_list
                    else:
                        print(f"Warning: Mismatched config name returned. Expected '{config_name}', got '{returned_name}'. Storing under expected name.")
                        all_results[config_name] = results_list
                    completed_configs += 1
                    overall_bar.n = completed_configs
                    overall_bar.refresh()
                    bars[config_name].close()  # Close the bar for this config
                except Exception as exc:
                    print(f"Configuration '{config_name}' generated an exception during execution: {exc}")
                    all_results[config_name] = []
                    completed_configs += 1
                    overall_bar.n = completed_configs
                    overall_bar.refresh()
                    bars[config_name].close()
            
            time.sleep(0.1)  # Small delay to prevent overwhelming the terminal
        
        # Ensure all bars are closed
        for bar in bars.values():
            bar.close()
        overall_bar.close()

    print()
    if not all_results or all(not res for res in all_results.values()):
        print("No benchmark results were collected.")
    else:
        try:
            write_comparative_results(all_results, dirs, timestamp)
            print(f"Results saved to {dirs['results']}")
        except Exception as e:
            print(f"Error writing results file: {e}")
    
    print(f"Detailed outputs saved to {dirs['output']}")
    
    return 0

if __name__ == "__main__":
    sys.exit(main())