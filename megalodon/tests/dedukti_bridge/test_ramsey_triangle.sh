#!/usr/bin/env bash
set -euo pipefail

# Paths
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
VAMPIRE="$ROOT/../vampire/build/vampire"
DEDUKIT="$ROOT/../tools/dedukti.py"
PREAMBLE_EGAL="$ROOT/examples/egal/PfgEJun2022Preamble.mgs"
NEQ_LEMMAS="$ROOT/ramsey36/neq_lemmas_pure.mgs"
DK_PRELUDE="$ROOT/tests/dedukti_bridge/dk_prelude.mg"
TPTP="$ROOT/ramsey36/adj17_triangle_free.tptp"

TMPDK="/tmp/test_triangle.dk"
TMPMG="/tmp/test_triangle.mg"
TMPALL="/tmp/test_triangle_combined.mg"

echo "== Vampire -> Dedukti =="
"$VAMPIRE" -p dedukti --proof_extra full -t 60 "$TPTP" > "$TMPDK"

echo "== Dedukit -> Megalodon =="
python3 "$DEDUKIT" "$TMPDK" > "$TMPMG"

cat "$DK_PRELUDE" "$TMPMG" > "$TMPALL"

echo "== Megalodon check =="
cd "$ROOT"
./bin/megalodon -I "$PREAMBLE_EGAL" -I "$NEQ_LEMMAS" "$TMPALL"

echo "SUCCESS: adj17_triangle_free round-trip passed."
