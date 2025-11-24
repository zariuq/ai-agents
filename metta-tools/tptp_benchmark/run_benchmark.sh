#!/bin/bash
# Run E Prover and Vampire on all 42 TPTP problems and generate results.md

BENCHMARK_DIR="/home/zar/claude/mizar-rs/metta-tools/tptp_benchmark"
EPROVER="/home/zar/claude/eprover/PROVER/eprover"
VAMPIRE="/home/zar/claude/vampire/build/bin/vampire"
TIMEOUT=10  # seconds per problem
OUTPUT_FILE="$BENCHMARK_DIR/results.md"

echo "TPTP FOF Benchmark Results - E Prover vs Vampire"
echo "================================================="
echo ""
echo "Running both provers on 42 problems..."
echo ""

# Check if provers exist
if [ ! -f "$EPROVER" ]; then
    echo "Error: E Prover not found at $EPROVER"
    exit 1
fi

if [ ! -f "$VAMPIRE" ]; then
    echo "Error: Vampire not found at $VAMPIRE"
    echo "Waiting for build to complete..."
    exit 1
fi

# Create results file
cat > "$OUTPUT_FILE" << 'HEADER'
# TPTP FOF Benchmark Results - E Prover vs Vampire

**Date:** $(date '+%Y-%m-%d %H:%M:%S')
**Benchmark:** 42 Official TPTP FOF Problems
**Timeout:** 10 seconds per problem

## Summary Statistics

| Prover | Proved | Timeout | Unknown | Total |
|--------|--------|---------|---------|-------|
| E Prover | TBD | TBD | TBD | 42 |
| Vampire | TBD | TBD | TBD | 42 |

## Problem-by-Problem Results

HEADER

cd "$BENCHMARK_DIR"

# Counters
e_proved=0
e_timeout=0
e_unknown=0
v_proved=0
v_timeout=0
v_unknown=0

echo "" >> "$OUTPUT_FILE"
echo "| Problem | Status | E Prover | E Time | Vampire | V Time |" >> "$OUTPUT_FILE"
echo "|---------|--------|----------|--------|---------|--------|" >> "$OUTPUT_FILE"

for problem in tptp_*.p; do
    # Get official status
    status=$(grep "% Status" "$problem" | awk '{print $4}')

    echo "Testing: $problem ($status)"

    # Run E Prover
    e_start=$(date +%s.%N)
    e_output=$(timeout $TIMEOUT "$EPROVER" --auto "$problem" 2>&1)
    e_end=$(date +%s.%N)
    e_time=$(echo "$e_end - $e_start" | bc)

    if echo "$e_output" | grep -q "Proof found"; then
        e_result="✅ Proof"
        ((e_proved++))
    elif echo "$e_output" | grep -q "Completion found"; then
        e_result="✅ Complete"
        ((e_proved++))
    elif [ $? -eq 124 ]; then
        e_result="⏱️ Timeout"
        ((e_timeout++))
    else
        e_result="❓ Unknown"
        ((e_unknown++))
    fi

    # Run Vampire
    v_start=$(date +%s.%N)
    v_output=$(timeout $TIMEOUT "$VAMPIRE" "$problem" 2>&1)
    v_end=$(date +%s.%N)
    v_time=$(echo "$v_end - $v_start" | bc)

    if echo "$v_output" | grep -q "Refutation found"; then
        v_result="✅ Proof"
        ((v_proved++))
    elif echo "$v_output" | grep -q "Satisfiable"; then
        v_result="✅ SAT"
        ((v_proved++))
    elif [ $? -eq 124 ]; then
        v_result="⏱️ Timeout"
        ((v_timeout++))
    else
        v_result="❓ Unknown"
        ((v_unknown++))
    fi

    # Format times
    e_time_formatted=$(printf "%.2fs" $e_time)
    v_time_formatted=$(printf "%.2fs" $v_time)

    # Write to results file
    echo "| $problem | $status | $e_result | $e_time_formatted | $v_result | $v_time_formatted |" >> "$OUTPUT_FILE"
done

# Update summary statistics
sed -i "s/| E Prover | TBD | TBD | TBD | 42 |/| E Prover | $e_proved | $e_timeout | $e_unknown | 42 |/" "$OUTPUT_FILE"
sed -i "s/| Vampire | TBD | TBD | TBD | 42 |/| Vampire | $v_proved | $v_timeout | $v_unknown | 42 |/" "$OUTPUT_FILE"

echo ""
echo "Results written to: $OUTPUT_FILE"
echo ""
echo "Summary:"
echo "  E Prover: $e_proved proved, $e_timeout timeout, $e_unknown unknown"
echo "  Vampire:  $v_proved proved, $v_timeout timeout, $v_unknown unknown"
echo ""

# Add analysis section
cat >> "$OUTPUT_FILE" << 'ANALYSIS'

## Analysis

### Theorem Problems (Expected: Proof)
Problems with Status=Theorem should be proven by refutation provers.

### CounterSatisfiable Problems (Expected: Timeout/Unknown)
Problems with Status=CounterSatisfiable should NOT be proven (would indicate unsoundness).

### ContradictoryAxioms Problems (Expected: Proof)
Problems with Status=ContradictoryAxioms should be proven inconsistent.

## Notes

- ✅ Proof/Complete/SAT: Prover successfully completed
- ⏱️ Timeout: Exceeded 10-second limit
- ❓ Unknown: Prover returned unknown result

## Vampire Build Info

```
$(cat /home/zar/claude/vampire/build/bin/vampire --version 2>&1 | head -5)
```

## E Prover Build Info

```
$($EPROVER --version 2>&1 | head -5)
```

ANALYSIS

echo "✅ Benchmark run complete!"
