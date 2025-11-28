#!/bin/bash
# Run E Prover on all 42 TPTP problems (quick version while Vampire builds)

BENCHMARK_DIR="/home/zar/claude/mizar-rs/metta-tools/tptp_benchmark"
EPROVER="/home/zar/claude/eprover/PROVER/eprover"
TIMEOUT=10  # seconds per problem
OUTPUT_FILE="$BENCHMARK_DIR/results.md"

cd "$BENCHMARK_DIR"

echo "TPTP FOF Benchmark Results - E Prover"
echo "====================================="
echo ""

# Counters
e_proved=0
e_timeout=0
e_unknown=0

# Create results file
cat > "$OUTPUT_FILE" << 'HEADER'
# TPTP FOF Benchmark Results - E Prover

**Date:** $(date '+%Y-%m-%d %H:%M:%S')
**Benchmark:** 42 Official TPTP FOF Problems
**Timeout:** 10 seconds per problem

## Summary Statistics

| Prover | Proved | Timeout | Unknown | Total |
|--------|--------|---------|---------|-------|

HEADER

date '+**Date:** %Y-%m-%d %H:%M:%S' >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"

echo "## Problem-by-Problem Results" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"
echo "| Problem | Status | E Prover | E Time (s) | E SZS |" >> "$OUTPUT_FILE"
echo "|---------|--------|----------|------------|-------|" >> "$OUTPUT_FILE"

for problem in tptp_*.p; do
    # Get official status
    status=$(grep "% Status" "$problem" | awk '{print $4}')

    echo "Testing: $problem ($status)"

    # Run E Prover
    e_start=$(date +%s.%N)
    e_output=$(timeout $TIMEOUT "$EPROVER" --auto "$problem" 2>&1)
    e_exit=$?
    e_end=$(date +%s.%N)
    e_time=$(echo "$e_end - $e_start" | bc -l)

    # Extract SZS status
    e_szs=$(echo "$e_output" | grep "% SZS status" | awk '{print $4}')
    if [ -z "$e_szs" ]; then
        e_szs="Unknown"
    fi

    if echo "$e_output" | grep -q "Proof found"; then
        e_result="✅ Proof"
        ((e_proved++))
    elif echo "$e_output" | grep -q "Completion found"; then
        e_result="✅ Complete"
        ((e_proved++))
    elif [ $e_exit -eq 124 ]; then
        e_result="⏱️ Timeout"
        e_szs="Timeout"
        ((e_timeout++))
    else
        e_result="❓ Unknown"
        ((e_unknown++))
    fi

    # Format time
    e_time_formatted=$(printf "%.3f" $e_time)

    # Write to results file
    echo "| $problem | $status | $e_result | $e_time_formatted | $e_szs |" >> "$OUTPUT_FILE"
done

echo "" >> "$OUTPUT_FILE"
echo "## Summary" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"
echo "| Metric | Count |" >> "$OUTPUT_FILE"
echo "|--------|-------|" >> "$OUTPUT_FILE"
echo "| Proved | $e_proved |" >> "$OUTPUT_FILE"
echo "| Timeout | $e_timeout |" >> "$OUTPUT_FILE"
echo "| Unknown | $e_unknown |" >> "$OUTPUT_FILE"
echo "| **Total** | **42** |" >> "$OUTPUT_FILE"

echo ""  >> "$OUTPUT_FILE"
echo "## Analysis by Status" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"

# Count by official status
cat > /tmp/status_analysis.sh << 'ANALYZE'
#!/bin/bash
cd /home/zar/claude/mizar-rs/metta-tools/tptp_benchmark

theorem_total=0
theorem_proved=0
cs_total=0
cs_proved=0
ca_total=0
ca_proved=0

for prob in tptp_*.p; do
    status=$(grep "% Status" "$prob" | awk '{print $4}')
    grep "| $prob |" results.md > /tmp/line.txt

    if [ "$status" = "Theorem" ]; then
        ((theorem_total++))
        if grep -q "✅" /tmp/line.txt; then
            ((theorem_proved++))
        fi
    elif [ "$status" = "CounterSatisfiable" ]; then
        ((cs_total++))
        if grep -q "✅" /tmp/line.txt; then
            ((cs_proved++))
        fi
    elif [ "$status" = "ContradictoryAxioms" ]; then
        ((ca_total++))
        if grep -q "✅" /tmp/line.txt; then
            ((ca_proved++))
        fi
    fi
done

echo "| Official Status | Total | E Proved | Expected Outcome |"
echo "|----------------|-------|----------|------------------|"
echo "| Theorem | $theorem_total | $theorem_proved | Should prove all |"
echo "| CounterSatisfiable | $cs_total | $cs_proved | Should NOT prove (timeout/unknown) |"
echo "| ContradictoryAxioms | $ca_total | $ca_proved | Should prove inconsistency |"
ANALYZE

chmod +x /tmp/status_analysis.sh
/tmp/status_analysis.sh >> "$OUTPUT_FILE"

cat >> "$OUTPUT_FILE" << 'FOOTER'

## Notes

- ✅ Proof/Complete: E Prover successfully completed
- ⏱️ Timeout: Exceeded 10-second limit
- ❓ Unknown: E Prover returned unknown result

### Expected Behavior

**Theorem problems**: Should be proven by refutation (proving Axioms ∧ ¬Conjecture is UNSAT)

**CounterSatisfiable problems**: Should NOT be proven (would indicate unsoundness if proven!)
- E should timeout or return "unknown"
- These have countermodels where Axioms ∧ ¬Conjecture is SAT

**ContradictoryAxioms problems**: Should prove inconsistency (axioms are self-contradictory)

## E Prover Info

```
FOOTER

$EPROVER --version >> "$OUTPUT_FILE"

echo '```' >> "$OUTPUT_FILE"

echo ""
echo "Results written to: $OUTPUT_FILE"
echo ""
echo "E Prover Summary:"
echo "  Proved:  $e_proved / 42"
echo "  Timeout: $e_timeout / 42"
echo "  Unknown: $e_unknown / 42"
echo ""
echo "✅ Benchmark run complete!"
