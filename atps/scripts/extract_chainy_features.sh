#!/bin/bash
set -euo pipefail
cd /home/zar/claude/atps/datasets/extended_mptp5k
mkdir -p features_chainy

ENIGMA="/home/zar/claude/atps/oldzar/eprover/SIMPLE_APPS/enigmatic-features"
FEATURES='C(l,p,x,s,r,v,h,c,d,a):G:T:P'

echo "Extracting chainy features for $(ls chainy/train/ | wc -l) problems..."

ls chainy/train/ | nice -n 19 parallel -j 8 \
  "$ENIGMA --free-numbers --features='$FEATURES' -p chainy/train/{} chainy/train/{} > features_chainy/{}.vec 2>/dev/null"

echo "DONE: $(ls features_chainy/*.vec 2>/dev/null | wc -l) vec files created"
