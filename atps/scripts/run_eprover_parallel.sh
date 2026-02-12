#!/bin/bash
# Run E prover on premise selections with GNU parallel
# Usage: run_eprover_parallel.sh <selections.json> <problems_dir> <output_dir> <jobs> [timeout]
#
# Skips problems that already have a .out file in output_dir.

set -euo pipefail

SELECTIONS="$1"
PROBLEMS_DIR="$2"
OUTPUT_DIR="$3"
JOBS="${4:-3}"
TIMEOUT="${5:-5}"

EPROVER="/home/zar/claude/atps/eprover-standard/PROVER/eprover"

mkdir -p "$OUTPUT_DIR"

# Generate list of problems to run (skip already done)
python3 -c "
import json, sys
from pathlib import Path
sels = json.load(open('$SELECTIONS'))
out_dir = Path('$OUTPUT_DIR')
for pname in sorted(sels):
    if sels[pname] and not (out_dir / f'{pname}.out').exists():
        print(pname)
" > /tmp/eprover_todo_$$.txt

TOTAL=$(wc -l < /tmp/eprover_todo_$$.txt)
DONE=$(ls "$OUTPUT_DIR"/*.out 2>/dev/null | wc -l)
echo "Problems: $TOTAL todo, $DONE already done, jobs=$JOBS, timeout=${TIMEOUT}s"

# Create filtered problem and run E
run_one() {
    local PNAME="$1"
    local PFILE="$PROBLEMS_DIR/$PNAME"
    local OUTFILE="$OUTPUT_DIR/${PNAME}.out"
    local TMPFILE=$(mktemp /tmp/eprover_filtered_XXXXXX.p)

    # Create filtered problem using Python
    python3 -c "
import json, re, sys
sels = json.load(open('$SELECTIONS'))
selected = set(sels.get('$PNAME', []))
formula_re = re.compile(r'^(fof|cnf)\(([^,]+),\s*([^,]+),')
with open('$PFILE') as f, open('$TMPFILE', 'w') as out:
    for line in f:
        s = line.strip()
        if not s or s.startswith('%'):
            out.write(line); continue
        m = formula_re.match(s)
        if not m:
            out.write(line); continue
        role = m.group(3).strip()
        if role in ('axiom','hypothesis','definition'):
            if m.group(2).strip() in selected:
                out.write(line)
        else:
            out.write(line)
"

    # Run E prover
    timeout $((TIMEOUT + 10)) nice -n 19 "$EPROVER" \
        --free-numbers --auto-schedule -p --cpu-limit="$TIMEOUT" \
        "$TMPFILE" > "$OUTFILE" 2>&1 || true

    rm -f "$TMPFILE"

    # Check result
    if grep -q "Proof found\|SZS status Theorem" "$OUTFILE" 2>/dev/null; then
        echo "PROVED $PNAME"
    fi
}
export -f run_one
export PROBLEMS_DIR OUTPUT_DIR SELECTIONS EPROVER TIMEOUT

cat /tmp/eprover_todo_$$.txt | nice -n 19 parallel -j "$JOBS" run_one {}

# Count results
SOLVED=$(grep -l "Proof found\|SZS status Theorem" "$OUTPUT_DIR"/*.out 2>/dev/null | wc -l)
TOTAL_DONE=$(ls "$OUTPUT_DIR"/*.out 2>/dev/null | wc -l)
echo ""
echo "FINAL: $SOLVED/$TOTAL_DONE solved (timeout=${TIMEOUT}s)"

rm -f /tmp/eprover_todo_$$.txt
