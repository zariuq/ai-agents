#!/usr/bin/env bash
set -euo pipefail

# Round-2 model generation only (NO E runs).
# Uses pooled train dependency events from:
#   - bushy_train_deps.jsonl
#   - chainy_train_deps.jsonl
#   - all proofs_*_train_5s directories

ROOT="/home/zar/claude/atps"
DATA="$ROOT/datasets/extended_mptp5k"
MODELS="$DATA/models"
DEPS="$DATA/deps"

mkdir -p "$MODELS" "$DEPS"

POOLED_DEPS="$DEPS/pooled_train_deps_allruns.jsonl"
POOLED_META="$DEPS/pooled_train_deps_allruns_meta.json"

NB_TABLES="$MODELS/mash_nb_tables_round2_pooled.pkl"
NB_META="$MODELS/mash_nb_tables_round2_pooled_meta.json"
KNN_TABLES="$MODELS/mash_knn_tables_round2_pooled.pkl"
KNN_META="$MODELS/mash_knn_tables_round2_pooled_meta.json"

echo "[1/3] Build pooled deps..."
ulimit -Sv 6291456
nice -n 19 python3 "$ROOT/scripts/build_pooled_train_deps.py" \
  --base-deps-files \
    "$DEPS/bushy_train_deps.jsonl" \
    "$DEPS/chainy_train_deps.jsonl" \
  --proof-dirs \
    "$DATA/proofs_mash_nb_top512_train_5s" \
    "$DATA/proofs_mash_knn_top512_train_5s" \
    "$DATA/proofs_pln_enhanced_top256_train_5s" \
    "$DATA/proofs_pln_normal_nb_top256_train_5s" \
    "$DATA/proofs_pln_knn_nb_top256_train_5s" \
  --problems-dir "$DATA/chainy/train" \
  --output "$POOLED_DEPS" \
  --meta-output "$POOLED_META"

echo "[2/3] Build MaSh NB tables from pooled deps..."
ulimit -Sv 6291456
nice -n 19 python3 "$ROOT/scripts/mash_nb_build_tables.py" \
  --deps-files \
    "$DEPS/bushy_train_deps.jsonl" \
    "$DEPS/chainy_train_deps.jsonl" \
    "$POOLED_DEPS" \
  --out-tables "$NB_TABLES" \
  --out-meta "$NB_META"

echo "[3/3] Build MaSh kNN tables from pooled deps..."
ulimit -Sv 6291456
nice -n 19 python3 "$ROOT/scripts/mash_knn_build_tables.py" \
  --deps-files \
    "$DEPS/bushy_train_deps.jsonl" \
    "$DEPS/chainy_train_deps.jsonl" \
    "$POOLED_DEPS" \
  --out-tables "$KNN_TABLES" \
  --out-meta "$KNN_META"

echo "Done."
echo "  pooled deps: $POOLED_DEPS"
echo "  NB tables:   $NB_TABLES"
echo "  kNN tables:  $KNN_TABLES"
