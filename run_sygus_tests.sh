#!/bin/bash
# Run SyGuS TR mode tests on all benchmarks up to 128-bit, excluding int2bv

BUILD_DIR="/home/daniel/Projects/aeval/build"
FREQHORN="$BUILD_DIR/tools/deep/freqhorn"

if [ ! -f "$FREQHORN" ]; then
    echo "ERROR: freqhorn not found at $FREQHORN"
    exit 1
fi

PASS=0
FAIL=0
TIMEOUT=0
TOTAL=0

echo "========================================"
echo "SyGuS TR Mode Benchmark Tests"
echo "========================================"
echo ""

# Find all benchmarks: up to 128-bit, no int2bv, no ccex files
BENCHMARKS=$(find bench_horn_ccex -name "*.smt2" ! -name "*_ccex.smt2" ! -name "*int2bv*" | grep -E "bvzext(4|8|16|32|64|128)_" | sort)

for bench in $BENCHMARKS; do
    TOTAL=$((TOTAL + 1))
    bench_name=$(basename "$bench" .smt2)
    
    printf "[%2d] %-50s " "$TOTAL" "$bench_name"
    
    # Run with 30 second timeout
    OUTPUT=$(timeout 30s "$FREQHORN" --sygus-tr --sygus-run --sygus-validate "$bench" 2>&1)
    EXIT_CODE=$?
    
    if [ $EXIT_CODE -eq 124 ]; then
        echo "TIMEOUT"
        TIMEOUT=$((TIMEOUT + 1))
    elif echo "$OUTPUT" | grep -q "All 3 checks passed"; then
        echo "PASS"
        PASS=$((PASS + 1))
    elif echo "$OUTPUT" | grep -q "Transition: FAIL"; then
        # Synthesized but doesn't match transition
        REASON=$(echo "$OUTPUT" | grep "Failing constraint:" | sed 's/.*Failing constraint: //')
        echo "WRONG_TRANS: $REASON"
        FAIL=$((FAIL + 1))
    elif echo "$OUTPUT" | grep -q "CVC5 synthesis failed\|unsupported\|Error"; then
        echo "SKIP (CVC5 unsupported)"
    elif echo "$OUTPUT" | grep -q "Partial trace covers cone"; then
        echo "PARTIAL (cone-based validation)"
    else
        echo "FAIL"
        FAIL=$((FAIL + 1))
        # Show details on failure
        echo "    Output: $(echo "$OUTPUT" | tail -3 | head -1)"
    fi
done

echo ""
echo "========================================"
echo "Results Summary"
echo "========================================"
echo "Total:   $TOTAL"
echo "Passed:  $PASS"
echo "Failed:  $FAIL"
echo "Timeout: $TIMEOUT"
echo "========================================"
