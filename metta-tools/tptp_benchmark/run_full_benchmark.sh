#!/bin/bash
# Run E Prover and Vampire on all 42 TPTP problems and generate results.md

BENCHMARK_DIR="/home/zar/claude/mizar-rs/metta-tools/tptp_benchmark"
EPROVER="/home/zar/claude/eprover/PROVER/eprover"
VAMPIRE="/home/zar/claude/vampire/build/vampire"
TIMEOUT=10  # seconds per problem
OUTPUT_FILE="$BENCHMARK_DIR/results.md"

cd "$BENCHMARK_DIR"

echo "TPTP FOF Benchmark Results - E Prover vs Vampire"
echo "================================================="
echo ""
echo "Running both provers on 42 problems..."
echo ""

# Counters
e_proved=0
e_timeout=0
e_unknown=0
v_proved=0
v_timeout=0
v_unknown=0

# Create results file
cat > "$OUTPUT_FILE" << 'HEADER'
# TPTP FOF Benchmark Results - E Prover vs Vampire

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
echo "| Problem | Status | E Prover | E Time (s) | E SZS | Vampire | V Time (s) | V SZS |" >> "$OUTPUT_FILE"
echo "|---------|--------|----------|------------|-------|---------|------------|-------|" >> "$OUTPUT_FILE"

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
    e_time_formatted=$(printf "%.3f" $e_time 2>/dev/null || echo "$e_time")

    # Run Vampire
    v_start=$(date +%s.%N)
    v_output=$(timeout $TIMEOUT "$VAMPIRE" "$problem" 2>&1)
    v_exit=$?
    v_end=$(date +%s.%N)
    v_time=$(echo "$v_end - $v_start" | bc -l)

    # Extract SZS status
    v_szs=$(echo "$v_output" | grep "% SZS status" | awk '{print $4}')
    if [ -z "$v_szs" ]; then
        v_szs="Unknown"
    fi

    if echo "$v_output" | grep -q "Refutation found"; then
        v_result="✅ Refutation"
        ((v_proved++))
    elif echo "$v_output" | grep -q "Satisfiable"; then
        v_result="✅ SAT"
        ((v_proved++))
    elif [ $v_exit -eq 124 ]; then
        v_result="⏱️ Timeout"
        v_szs="Timeout"
        ((v_timeout++))
    else
        v_result="❓ Unknown"
        ((v_unknown++))
    fi

    # Format time
    v_time_formatted=$(printf "%.3f" $v_time 2>/dev/null || echo "$v_time")

    # Write to results file
    echo "| $problem | $status | $e_result | $e_time_formatted | $e_szs | $v_result | $v_time_formatted | $v_szs |" >> "$OUTPUT_FILE"
done

echo "" >> "$OUTPUT_FILE"
echo "| E Prover | $e_proved | $e_timeout | $e_unknown | 42 |" >> "$OUTPUT_FILE"
echo "| Vampire | $v_proved | $v_timeout | $v_unknown | 42 |" >> "$OUTPUT_FILE"

echo "" >> "$OUTPUT_FILE"
echo "## Summary" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"
echo "### E Prover Results" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"
echo "| Metric | Count | Percentage |" >> "$OUTPUT_FILE"
echo "|--------|-------|------------|" >> "$OUTPUT_FILE"
echo "| Proved | $e_proved | $(echo "scale=1; $e_proved * 100 / 42" | bc)% |" >> "$OUTPUT_FILE"
echo "| Timeout | $e_timeout | $(echo "scale=1; $e_timeout * 100 / 42" | bc)% |" >> "$OUTPUT_FILE"
echo "| Unknown | $e_unknown | $(echo "scale=1; $e_unknown * 100 / 42" | bc)% |" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"
echo "### Vampire Results" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"
echo "| Metric | Count | Percentage |" >> "$OUTPUT_FILE"
echo "|--------|-------|------------|" >> "$OUTPUT_FILE"
echo "| Proved | $v_proved | $(echo "scale=1; $v_proved * 100 / 42" | bc)% |" >> "$OUTPUT_FILE"
echo "| Timeout | $v_timeout | $(echo "scale=1; $v_timeout * 100 / 42" | bc)% |" >> "$OUTPUT_FILE"
echo "| Unknown | $v_unknown | $(echo "scale=1; $v_unknown * 100 / 42" | bc)% |" >> "$OUTPUT_FILE"

echo ""  >> "$OUTPUT_FILE"
echo "## Analysis by Status" >> "$OUTPUT_FILE"
echo "" >> "$OUTPUT_FILE"

# Count by official status
cat > /tmp/status_analysis.sh << 'ANALYZE'
#!/bin/bash
cd /home/zar/claude/mizar-rs/metta-tools/tptp_benchmark

theorem_total=0
theorem_e_proved=0
theorem_v_proved=0
cs_total=0
cs_e_proved=0
cs_v_proved=0
ca_total=0
ca_e_proved=0
ca_v_proved=0

for prob in tptp_*.p; do
    status=$(grep "% Status" "$prob" | awk '{print $4}')
    grep "| $prob |" results.md > /tmp/line.txt

    # Extract E Prover result (column 4) and Vampire result (column 7)
    e_col=$(awk -F'|' '{print $4}' /tmp/line.txt)
    v_col=$(awk -F'|' '{print $7}' /tmp/line.txt)

    if [ "$status" = "Theorem" ]; then
        ((theorem_total++))
        if echo "$e_col" | grep -q "✅"; then
            ((theorem_e_proved++))
        fi
        if echo "$v_col" | grep -q "✅"; then
            ((theorem_v_proved++))
        fi
    elif [ "$status" = "CounterSatisfiable" ]; then
        ((cs_total++))
        # For CounterSatisfiable, E returning ❓ is correct (not a proof)
        # Vampire returning ✅ SAT is correct (found countermodel)
        if echo "$e_col" | grep -q "✅"; then
            ((cs_e_proved++))
        fi
        if echo "$v_col" | grep -q "✅"; then
            ((cs_v_proved++))
        fi
    elif [ "$status" = "ContradictoryAxioms" ]; then
        ((ca_total++))
        if echo "$e_col" | grep -q "✅"; then
            ((ca_e_proved++))
        fi
        if echo "$v_col" | grep -q "✅"; then
            ((ca_v_proved++))
        fi
    fi
done

echo "| Official Status | Total | E Proved | V Proved | Expected Outcome |"
echo "|----------------|-------|----------|----------|------------------|"
echo "| Theorem | $theorem_total | $theorem_e_proved | $theorem_v_proved | Should prove all |"
echo "| CounterSatisfiable | $cs_total | $cs_e_proved | $cs_v_proved | Should NOT prove (timeout/unknown) |"
echo "| ContradictoryAxioms | $ca_total | $ca_e_proved | $ca_v_proved | Should prove inconsistency |"
ANALYZE

chmod +x /tmp/status_analysis.sh
/tmp/status_analysis.sh >> "$OUTPUT_FILE"

cat >> "$OUTPUT_FILE" << 'FOOTER'

## Prover Comparison

### Vampire (Primary Baseline)
**Capabilities**: Saturation + SAT solver integration + finite model building
- ✅ Proves theorems via refutation (UNSAT of Axioms ∧ ¬Conjecture)
- ✅ Finds countermodels for CounterSatisfiable problems (SAT)
- ✅ Proves inconsistency for ContradictoryAxioms
- **Use as**: Main baseline for mixed UNSAT/SAT benchmarks and PeTTaRes comparison

### E Prover (Complementary Baseline)
**Capabilities**: Pure superposition-based refutation prover
- ✅ Proves theorems via refutation (UNSAT)
- ❓ Returns "Unknown" on CounterSatisfiable (correct - cannot prove non-theorems)
- ✅ Proves inconsistency for ContradictoryAxioms
- **Use as**: Secondary baseline for pure theorem-proving and HO/THF problems

## Legend

- ✅ Proof/Complete/Refutation/SAT: Prover successfully completed
- ⏱️ Timeout: Exceeded 10-second limit
- ❓ Unknown: Prover returned unknown result (correct for non-theorems)

### Expected Behavior by Problem Type

**Theorem (36 problems)**: Should be proven by refutation
- Target: Axioms ∧ ¬Conjecture is UNSAT
- Expected: Both provers return ✅

**CounterSatisfiable (4 problems)**: Has countermodels, should NOT be proven as theorems
- Target: Axioms ∧ ¬Conjecture is SAT
- Expected: Vampire ✅ SAT (finds model), E ❓ Unknown (correct - refutation fails)
- **Soundness check**: If E proves these, it's UNSOUND!

**ContradictoryAxioms (2 problems)**: Axioms are self-contradictory
- Target: Axioms alone are UNSAT
- Expected: Both provers return ✅

## Prover Information

### Vampire (Primary Baseline)
```
FOOTER

$VAMPIRE --version >> "$OUTPUT_FILE"

cat >> "$OUTPUT_FILE" << 'MIDDLE'
```

### E Prover (Complementary Baseline)
```
MIDDLE

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
echo "Vampire Summary:"
echo "  Proved:  $v_proved / 42"
echo "  Timeout: $v_timeout / 42"
echo "  Unknown: $v_unknown / 42"
echo ""
echo "✅ Benchmark run complete!"
