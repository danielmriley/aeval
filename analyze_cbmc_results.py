import csv

def analyze_cbmc_results(csv_file):
    with open(csv_file, 'r') as f:
        reader = csv.DictReader(f)
        results = list(reader)

    total = len(results)
    solved_correctly = 0
    unwinding_failures = 0
    timeouts = 0
    other_failures = 0

    solved_list = []
    unwinding_list = []

    for row in results:
        bench_name = row['benchmark']
        # Remove _c suffix for matching
        if bench_name.endswith('_c'):
            bench_name = bench_name[:-2]

        is_unwinding_failed = row['unwinding_failed'] == 'True'
        is_verified_failed = row['status'] == 'VERIFICATION_FAILED'
        
        # Check assertions_failed count. If > 0 and NOT just unwinding failure.
        # But wait, run_cbmc_benchmarks.py logic is:
        # if 'assertion' in line and 'FAILURE' in line: info['assertions_failed'] += 1
        # if 'VERIFICATION FAILED' in line: info['counterexample_found'] = True
        
        # If Unwinding assertion fails, it adds to assertions_failed count often (labeled as assertion loop X).
        # We rely on 'unwinding_failed' flag extracted by the parser.

        if is_verified_failed:
            if is_unwinding_failed:
                unwinding_failures += 1
                unwinding_list.append(bench_name)
            else:
                solved_correctly += 1
                solved_list.append(bench_name)
        elif row['status'] == 'TIMEOUT':
            timeouts += 1
        else:
            other_failures += 1

    print(f"Total Benchmarks: {total}")
    print(f"Correctly Solved (Target Reached): {solved_correctly} ({solved_correctly/total*100:.1f}%)")
    print(f"Unwinding Assertion Failures: {unwinding_failures} ({unwinding_failures/total*100:.1f}%)")
    print(f"Timeouts: {timeouts}")
    print(f"Other Failures: {other_failures}")
    
    print("\nVerified Solved Benchmarks:")
    print(", ".join(sorted(solved_list)))

    print("\nUnwinding Failed Benchmarks (Previously misclassified):")
    print(", ".join(sorted(unwinding_list)))

if __name__ == "__main__":
    analyze_cbmc_results("cbmc_benchmark_results.csv")
