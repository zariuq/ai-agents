#!/bin/bash
cd /home/zar/claude/mizar-rs/metta-tools/tptp_benchmark

echo "TPTP FOF Benchmark - Status Summary"
echo "===================================="
echo ""

for f in *.p; do
    status=$(grep "% Status" "$f" | awk '{print $4}')
    echo "$f: $status"
done | tee /tmp/status_list.txt

echo ""
echo "Counts by status:"
cat /tmp/status_list.txt | awk '{print $2}' | sort | uniq -c
