#!/bin/bash
# Verification script for Ramsey R(3,6)=18 Phase 1

MEGALODON=/home/zar/claude/megalodon/bin/megalodon

echo "=== Ramsey R(3,6)=18 Phase 1 Verification ==="
echo ""
echo "Files in workspace:"
ls -lh preamble.mgs r36_definitions.mg
echo ""

echo "Testing compilation..."
$MEGALODON -I preamble.mgs r36_definitions.mg
EXIT_CODE=$?
echo ""

if [ $EXIT_CODE -eq 0 ]; then
    echo "✅ SUCCESS: r36_definitions.mg compiles"
    echo ""
    echo "Definitions included:"
    grep "^Definition" r36_definitions.mg | sed 's/:.*$//' | sed 's/^/  - /'
    echo ""
    echo "Phase 1 Status: COMPLETE ✅"
    echo "Next: Phase 2 - R(3,4)=9 (see README.md)"
else
    echo "❌ FAILED: Compilation error (exit code $EXIT_CODE)"
fi
