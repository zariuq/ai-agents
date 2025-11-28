#!/usr/bin/env bash
set -euo pipefail

# WARNING: This problem is large; adjust timeout if needed.

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
VAMPIRE="$ROOT/../vampire/build/vampire"
DEDUKIT="$ROOT/../tools/dedukti.py"
PREAMBLE_MIZAR="$ROOT/examples/mizar/PfgMizarNov2020Preamble.mgs"
NEQ_LEMMAS="$ROOT/ramsey36/neq_lemmas_pure.mgs"
DK_PRELUDE="$ROOT/tests/dedukti_bridge/dk_prelude.mg"
TPTP="$ROOT/ramsey36/adj17_no6indep.tptp"

TMPDK="$(mktemp /tmp/adj17_no6indep.XXXXXX.dk)"
TMPMG="$(mktemp /tmp/adj17_no6indep_from_dk.XXXXXX.mg)"
TMPALL="$(mktemp /tmp/adj17_no6indep_combined.XXXXXX.mg)"

echo "== Vampire -> Dedukti (this may take time) =="
"$VAMPIRE" -p dedukti --proof_extra full -t 300 "$TPTP" > "$TMPDK"

echo "== Dedukit -> Megalodon =="
python3 "$DEDUKIT" "$TMPDK" > "$TMPMG"

cat "$DK_PRELUDE" "$TMPMG" > "$TMPALL"

echo "== Megalodon check =="
cd "$ROOT"
./bin/megalodon -mizar -I "$PREAMBLE_MIZAR" -I "$NEQ_LEMMAS" "$TMPALL"

echo "SUCCESS: adj17_no6indep round-trip passed."
