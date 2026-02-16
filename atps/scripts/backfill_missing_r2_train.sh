#!/usr/bin/env bash
set -euo pipefail

# Backfill missing R2 train artifacts for:
#   - pln_nb (top512 selection, derive top256, E-5s train)
#   - pln_knn_prior_nb_opt_mash (top512 selection, derive top256, E-5s train)
#
# Usage:
#   bash scripts/backfill_missing_r2_train.sh
#
# This script is restart-safe:
#   - skips selection if output JSON already exists
#   - skips E runs if results JSON already exists

ROOT="/home/zar/claude/atps"
DATA="$ROOT/datasets/extended_mptp5k"
BASE="$DATA/baselines"
TRAIN_PROBLEMS="$DATA/chainy/train"
NB_TABLES="$DATA/models/mash_nb_tables_round2_pooled.pkl"
POOLED_DEPS="$DATA/deps/pooled_train_deps_allruns.jsonl"
PLN_NB_TAG="pln_nb_round2_pooled"
PLN_KNN_PRIOR_TAG="pln_knn_prior_nb_opt_mash_round2_pooled"
PETTA_PARALLEL_BATCHES="${PETTA_PARALLEL_BATCHES:-2}"

log() { echo "[$(date -u +%Y-%m-%dT%H:%M:%SZ)] $*"; }

derive_top256_from_top512() {
  local top512="$1"
  local top256="$2"
  if [[ -f "$top256" ]]; then
    log "exists: $top256 (skip derive)"
    return 0
  fi
  if [[ ! -f "$top512" ]]; then
    log "missing source for derive: $top512"
    return 1
  fi
  log "derive top256 from $top512 -> $top256"
  python3 - <<'PY' "$top512" "$top256"
import json,sys
src,dst=sys.argv[1],sys.argv[2]
with open(src) as f:
    data=json.load(f)
out={k:v[:256] for k,v in data.items()}
with open(dst,"w") as f:
    json.dump(out,f)
print(f"wrote {dst} problems={len(out)}")
PY
}

run_e_train_if_missing() {
  local model_tag="$1"
  local k="$2"
  local sel="$BASE/selections_${model_tag}_top${k}_train.json"
  local proofs="$DATA/proofs_${model_tag}_top${k}_train_5s"
  local res="$BASE/results_${model_tag}_top${k}_train_5s.json"

  if [[ -f "$res" ]]; then
    log "exists: $res (skip E run)"
    return 0
  fi
  if [[ ! -f "$sel" ]]; then
    log "missing selections: $sel"
    return 1
  fi
  if [[ -d "$proofs" ]] && compgen -G "$proofs/*.out" > /dev/null; then
    log "proof dir already has .out and no result JSON: $proofs"
    log "refusing overwrite; remove or move directory first"
    return 1
  fi

  log "E5s train: model=$model_tag top$k"
  cd "$ROOT"
  ulimit -v 6291456
  nice -n 19 python3 scripts/run_eprover.py \
    --problems-dir "$TRAIN_PROBLEMS" \
    --selections "$sel" \
    --output-dir "$proofs" \
    --timeout 5 \
    --jobs 8 \
    --save-results "$res"
}

wait_for_live_pln_nb_top512() {
  # If a live top512 train run is in progress, wait for it to finish to avoid duplicate work.
  while pgrep -f "select_pln_nb.py --split train --top-k 512" > /dev/null; do
    log "waiting for active pln_nb top512 train run to finish..."
    sleep 60
  done
}

main() {
  mkdir -p "$BASE"
  cd "$ROOT"

  [[ -f "$NB_TABLES" ]] || { log "missing NB tables: $NB_TABLES"; exit 1; }
  [[ -f "$POOLED_DEPS" ]] || { log "missing pooled deps: $POOLED_DEPS"; exit 1; }

  wait_for_live_pln_nb_top512

  # 1) pln_nb top512 selection (round2 pooled, if missing)
  if [[ ! -f "$BASE/selections_${PLN_NB_TAG}_top512_train.json" ]]; then
    log "run selection: ${PLN_NB_TAG} top512 train"
    ulimit -v 6291456
    nice -n 19 python3 scripts/select_pln_nb.py \
      --split train \
      --top-k 512 \
      --nb-tables "$NB_TABLES" \
      --prefilter-k 512 \
      --petta-batch-size 32 \
      --petta-job-batch-size 20 \
      --petta-parallel-batches "$PETTA_PARALLEL_BATCHES" \
      --output "$BASE/selections_${PLN_NB_TAG}_top512_train.json"
  else
    log "exists: $BASE/selections_${PLN_NB_TAG}_top512_train.json (skip selection)"
  fi

  # 2) derive pln_nb top256
  derive_top256_from_top512 \
    "$BASE/selections_${PLN_NB_TAG}_top512_train.json" \
    "$BASE/selections_${PLN_NB_TAG}_top256_train.json"

  # 3) pln_knn_prior_nb_opt_mash top512 selection (round2 pooled, if missing)
  if [[ ! -f "$BASE/selections_${PLN_KNN_PRIOR_TAG}_top512_train.json" ]]; then
    log "run selection: ${PLN_KNN_PRIOR_TAG} top512 train"
    ulimit -v 6291456
    nice -n 19 python3 scripts/select_pln_knn_prior_nb_opt.py \
      --split train \
      --merge-nb \
      --top-k 512 \
      --nb-tables "$NB_TABLES" \
      --deps-file "$POOLED_DEPS" \
      --petta-batch-size 20 \
      --petta-parallel-batches "$PETTA_PARALLEL_BATCHES" \
      --petta-timeout 300 \
      --output "$BASE/selections_${PLN_KNN_PRIOR_TAG}_top512_train.json"
  else
    log "exists: $BASE/selections_${PLN_KNN_PRIOR_TAG}_top512_train.json (skip selection)"
  fi

  # 4) derive pln_knn_prior_nb_opt_mash top256
  derive_top256_from_top512 \
    "$BASE/selections_${PLN_KNN_PRIOR_TAG}_top512_train.json" \
    "$BASE/selections_${PLN_KNN_PRIOR_TAG}_top256_train.json"

  # 5) E-5s train routes for missing result targets
  run_e_train_if_missing "$PLN_NB_TAG" "256"
  run_e_train_if_missing "$PLN_NB_TAG" "512"
  run_e_train_if_missing "$PLN_KNN_PRIOR_TAG" "256"
  run_e_train_if_missing "$PLN_KNN_PRIOR_TAG" "512"

  log "backfill complete"
}

main "$@"
