#!/bin/bash
# Extract 42 TPTP FOF problems for benchmark

cd /home/zar/claude/hyperon/TPTP

# Easy Theorem problems (20)
EASY_THEOREM="
SYN046+1
SYN047+1
SYN048+1
SYN049+1
SYN050+1
SYN051+1
SYN052+1
SYN053+1
SYN054+1
SYN055+1
SYN056+1
SYN057+1
SYN058+1
SYN059+1
SYN060+1
SYN061+1
SYN062+1
SYN063+1
SYN064+1
SYN065+1
"

# Medium/Hard Theorem problems (10)
HARD_THEOREM="
PUZ031+1
PUZ047+1
SYN066+1
SYN067+1
SYN068+1
SYN069+1
SYN070+1
SYN071+1
SYN072+1
SYN073+1
"

# Non-Theorem problems (12) - these need status verification
OTHER="
SYN315+1
SYN316+1
SYN317+1
SYN318+1
SYN319+1
SYN320+1
SYN321+1
SYN322+1
SYN323+1
SYN324+1
SYN325+1
SYN326+1
"

echo "Extracting 42 problems from TPTP archive..."

# Extract all in one tar command for efficiency
EXTRACT_LIST=""

for prob in $EASY_THEOREM $HARD_THEOREM $OTHER; do
    domain=$(echo $prob | sed 's/[0-9].*//')
    EXTRACT_LIST="$EXTRACT_LIST TPTP-v9.2.1/Problems/$domain/$prob.p"
done

echo "Running tar extraction (this may take a moment)..."
tar -xzf TPTP-v9.2.1.tgz $EXTRACT_LIST

echo "✅ Extraction complete!"
echo "Extracted $(echo $EXTRACT_LIST | wc -w) problems"

# Copy to benchmark directory with sequential naming
OUTPUT_DIR="/home/zar/claude/mizar-rs/metta-tools/tptp_benchmark"
mkdir -p "$OUTPUT_DIR"

counter=1

echo ""
echo "Copying problems to benchmark directory..."

for prob in $EASY_THEOREM; do
    domain=$(echo $prob | sed 's/[0-9].*//')
    src="TPTP-v9.2.1/Problems/$domain/$prob.p"
    if [ -f "$src" ]; then
        dest="$OUTPUT_DIR/tptp_$(printf '%03d' $counter)_theorem.p"
        cp "$src" "$dest"
        echo "  $counter. $prob → $(basename $dest)"
        counter=$((counter + 1))
    fi
done

for prob in $HARD_THEOREM; do
    domain=$(echo $prob | sed 's/[0-9].*//')
    src="TPTP-v9.2.1/Problems/$domain/$prob.p"
    if [ -f "$src" ]; then
        dest="$OUTPUT_DIR/tptp_$(printf '%03d' $counter)_theorem.p"
        cp "$src" "$dest"
        echo "  $counter. $prob → $(basename $dest)"
        counter=$((counter + 1))
    fi
done

for prob in $OTHER; do
    domain=$(echo $prob | sed 's/[0-9].*//')
    src="TPTP-v9.2.1/Problems/$domain/$prob.p"
    if [ -f "$src" ]; then
        dest="$OUTPUT_DIR/tptp_$(printf '%03d' $counter)_unknown.p"
        cp "$src" "$dest"
        echo "  $counter. $prob → $(basename $dest) [status TBD]"
        counter=$((counter + 1))
    fi
done

echo ""
echo "✅ Benchmark suite created in $OUTPUT_DIR"
echo "   Total problems: $((counter - 1))"
echo ""
echo "Next steps:"
echo "  1. Verify status annotations"
echo "  2. Run E prover verification"
echo "  3. Convert to MeTTa format"
