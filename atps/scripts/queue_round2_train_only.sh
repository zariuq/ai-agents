#!/usr/bin/env bash
set -euo pipefail

# Round-2 train-only queue:
# - Generate top512 selections for all agreed selectors on train split.
# - Derive top256 selections by truncation.
# - No E proving in this script.

ROOT="/home/zar/claude/atps"
DATA="$ROOT/datasets/extended_mptp5k"
BASE="$DATA/baselines"
NB_TABLES="$DATA/models/mash_nb_tables_round2_pooled.pkl"
KNN_TABLES="$DATA/models/mash_knn_tables_round2_pooled.pkl"
POOLED_DEPS="$DATA/deps/pooled_train_deps_allruns.jsonl"
PETTA_PARALLEL_BATCHES="${PETTA_PARALLEL_BATCHES:-2}"

log() { echo "[$(date -u +%Y-%m-%dT%H:%M:%SZ)] $*"; }

require_file() {
  local p="$1"
  [[ -f "$p" ]] || { log "missing required file: $p"; exit 1; }
}

derive_top256() {
  local top512="$1"
  local top256="$2"
  if [[ -f "$top256" ]]; then
    log "exists: $top256 (skip derive)"
    return 0
  fi
  [[ -f "$top512" ]] || { log "cannot derive; missing $top512"; exit 1; }
  log "derive top256: $top512 -> $top256"
  python3 - <<'PY' "$top512" "$top256"
import json, sys
src, dst = sys.argv[1], sys.argv[2]
with open(src) as f:
    data = json.load(f)
out = {k: v[:256] for k, v in data.items()}
with open(dst, "w") as f:
    json.dump(out, f)
print(f"wrote {dst} problems={len(out)}")
PY
}

run_selection_top512_if_missing() {
  local tag="$1"; shift
  local sel512="$BASE/selections_${tag}_top512_train.json"
  local sel256="$BASE/selections_${tag}_top256_train.json"
  if [[ -f "$sel512" ]]; then
    log "exists: $sel512 (skip selection)"
  else
    log "run selection top512: $tag"
    cd "$ROOT"
    ulimit -v 6291456
    nice -n 19 "$@" --output "$sel512"
  fi
  derive_top256 "$sel512" "$sel256"
}

main() {
  mkdir -p "$BASE"

  require_file "$NB_TABLES"
  require_file "$KNN_TABLES"
  require_file "$POOLED_DEPS"

  log "Round-2 train-only queue start"
  log "NB tables: $NB_TABLES"
  log "kNN tables: $KNN_TABLES"
  log "Pooled deps: $POOLED_DEPS"
  log "PeTTa parallel batches: $PETTA_PARALLEL_BATCHES"

  # Baselines
  run_selection_top512_if_missing "mash_nb_round2_pooled" \
    python3 scripts/select_mash_nb.py \
      --split train \
      --top-k 512 \
      --tables "$NB_TABLES"

  run_selection_top512_if_missing "mash_knn_round2_pooled" \
    python3 scripts/select_mash_knn.py \
      --split train \
      --top-k 512 \
      --tables "$KNN_TABLES"

  # Core PLN selectors
  run_selection_top512_if_missing "pln_nb_round2_pooled" \
    python3 scripts/select_pln_nb.py \
      --split train \
      --top-k 512 \
      --prefilter-k 512 \
      --petta-batch-size 32 \
      --petta-job-batch-size 20 \
      --petta-parallel-batches "$PETTA_PARALLEL_BATCHES" \
      --nb-tables "$NB_TABLES"

  run_selection_top512_if_missing "pln_normal_nb_round2_pooled" \
    python3 scripts/select_pln_normal_nb.py \
      --split train \
      --top-k 512 \
      --prefilter-k 512 \
      --petta-batch-size 32 \
      --petta-job-batch-size 20 \
      --petta-parallel-batches "$PETTA_PARALLEL_BATCHES" \
      --nb-batch-size 32 \
      --nb-tables "$NB_TABLES"

  run_selection_top512_if_missing "pln_enhanced_round2_pooled" \
    python3 scripts/select_pln_enhanced.py \
      --split train \
      --top-k 512 \
      --prefilter-k 512 \
      --petta-batch-size 32 \
      --petta-job-batch-size 20 \
      --petta-parallel-batches "$PETTA_PARALLEL_BATCHES" \
      --nb-tables "$NB_TABLES" \
      --deps-file "$POOLED_DEPS"

  run_selection_top512_if_missing "pln_knn_prior_nb_opt_mash_round2_pooled" \
    python3 scripts/select_pln_knn_prior_nb_opt.py \
      --split train \
      --merge-nb \
      --top-k 512 \
      --petta-batch-size 20 \
      --petta-parallel-batches "$PETTA_PARALLEL_BATCHES" \
      --petta-timeout 300 \
      --nb-tables "$NB_TABLES" \
      --deps-file "$POOLED_DEPS"

  # Mixture-local PLN selector (non-alias staged model)
  run_selection_top512_if_missing "pln_mixture_local_nb_round2_pooled" \
    python3 scripts/select_pln_mixture_local_nb.py \
      --split train \
      --top-k 512 \
      --prefilter-k 1536 \
      --max-neighbors 256 \
      --bin-edges 4,16,64,256 \
      --bin-lambdas 1,1,1,1 \
      --local-total-scale 1.0 \
      --neg-weight 0.08 \
      --nb-tables "$NB_TABLES" \
      --deps-file "$POOLED_DEPS"

  log "Round-2 train-only queue complete"
}

main "$@"
