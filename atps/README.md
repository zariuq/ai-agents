# PLN Premise Selection for Automated Theorem Proving

Premise selection experiments using Probabilistic Logic Networks (PLN) on the extended MPTP 5k dataset. PLN selectors run inference in PeTTa (Prolog-based MeTTa) and are driven by Python scripts that handle data preparation and E prover evaluation.

## Results (extended MPTP 5k, 800 val, top-256, E 5s)

| Selector | Solved/800 | Notes |
|----------|-----------|-------|
| MaSh NB | 283 (35.4%) | Blanchette et al. 2016 reimpl |
| PLN-NB | 281 (35.1%) | IDF-weighted NB in PLN |
| PLN-Normal-NB | 279 (34.9%) | xiPLN continuous Normal-Normal conjugate |
| Chainy baseline | 278 (34.8%) | No selection |
| PLN-kNN+NB | 276 (34.5%) | kNN + NB merged via pln-revision |
| PLN-Enhanced | 276 (34.5%) | NB + co-occurrence boost |
| PLN-Rule | 275 (34.4%) | Modus ponens + revision |
| PLN-kNN | 272 (34.0%) | All-PLN kNN (atomspace overlap) |
| MaSh kNN | 272 (34.0%) | Blanchette et al. 2016 reimpl |

## PLN Selectors

| Selector | MeTTa | Python Driver | PLN Operations |
|----------|-------|---------------|----------------|
| PLN-NB | `pln_idf_nb_selector.metta` | `select_pln_nb.py` | evidence-power (IDF), evidence-tensor |
| PLN-Rule | `pln_premise_selector.metta` | `select_pln_rule.py` | pln-modus-ponens, pln-revision |
| PLN-kNN | `pln_knn_selector.metta` | `select_pln_knn.py` | atomspace overlap, modus-ponens, evidence-hplus |
| PLN-kNN+NB | `pln_knn_selector.metta` | `select_pln_knn.py --merge-nb` | kNN + NB merged via pln-revision |
| PLN-Enhanced | `pln_enhanced_selector.metta` | `select_pln_enhanced.py` | NB + co-occurrence boost |
| PLN-Normal-NB | `pln_normal_nb_selector.metta` | `select_pln_normal_nb.py` | xiPLN continuous Normal-Normal conjugate |

PeTTa selectors live in `../hyperon/PeTTa/demos/`, Python drivers in `scripts/`.

## Directory Structure

```
atps/
├── scripts/
│   ├── select_pln_*.py        # PLN selector Python drivers
│   ├── select_mash_*.py       # MaSh baseline selectors
│   ├── mash_*_build_tables.py # Build MaSh training tables
│   ├── mash_*_scorer.py       # MaSh scoring modules (shared)
│   ├── run_eprover.py         # E prover runner (sequential)
│   └── run_eprover_parallel.sh # E prover runner (GNU parallel)
├── datasets/
│   └── extended_mptp5k/
│       ├── chainy/train/      # 4200 training problems (FOF)
│       ├── chainy/val/        # 800 validation problems
│       ├── deps/              # Proof dependencies (bushy_train_deps.jsonl)
│       ├── features_chainy/   # Sparse feature vectors (train)
│       ├── features_chainy_val/ # Sparse feature vectors (val)
│       ├── models/            # MaSh tables (pickle, regeneratable)
│       ├── baselines/         # Selection + result JSONs
│       └── proofs_*/          # E prover output files
└── eprover-standard/          # E 3.0.1-ho
```

## Quick Start

### 1. Build MaSh tables (one-time)

```bash
source atps/venv/bin/activate
python3 scripts/mash_nb_build_tables.py
python3 scripts/mash_knn_build_tables.py
```

### 2. Run a PLN selector (800 val problems)

```bash
# PLN-kNN+NB (best selector)
python3 scripts/select_pln_knn.py --merge-nb \
  --output datasets/extended_mptp5k/baselines/selections_pln_knn_nb_top256.json

# PLN-Normal-NB
python3 scripts/select_pln_normal_nb.py \
  --output datasets/extended_mptp5k/baselines/selections_pln_normal_nb_top256.json
```

### 3. Evaluate with E prover

```bash
# Sequential
python3 scripts/run_eprover.py \
  --selections datasets/extended_mptp5k/baselines/selections_pln_knn_nb_top256.json \
  --problems-dir datasets/extended_mptp5k/chainy/val \
  --output-dir datasets/extended_mptp5k/proofs_pln_knn_nb_top256_5s \
  --timeout 5

# Parallel (GNU parallel, 6 jobs)
bash scripts/run_eprover_parallel.sh \
  datasets/extended_mptp5k/baselines/selections_pln_knn_nb_top256.json \
  datasets/extended_mptp5k/chainy/val \
  datasets/extended_mptp5k/proofs_pln_knn_nb_top256_5s \
  6 5
```

## Resource Limits

- **Cores**: max 8 (machine has 14). Always `nice -n 19`.
- **Timeout**: 5s per problem for E prover (must match training data timeout).
- **Memory**: `ulimit -v 6291456` (6GB) for PeTTa subprocesses.

## Dependencies

- PeTTa: `../hyperon/PeTTa/` (Prolog-based MeTTa runtime)
- PLN libraries: `../hyperon/PeTTa/lib/lib_pln_xi.metta`, `../hyperon/PeTTa/pln_inference/`
- E prover: `eprover-standard/PROVER/eprover` (E 3.0.1-ho)
- Python: numpy, scikit-learn (in venv)

## References

- Blanchette et al. (2016). "Hammering towards QED." J. Formalized Reasoning.
- Goertzel et al. "Probabilistic Logic Networks." Springer.
- Jakubuv & Urban (2023). "Mizar60" (premise selection benchmarks).
