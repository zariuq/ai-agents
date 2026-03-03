# PLN premise automated theorem proving

Premise selection experiments using Probabilistic Logic Networks on the extended MPTP 5k dataset.
Selectors run PeTTa inference. Python drivers handle preparation and evaluation.

Paper: `../lean-projects/mettapedia/papers/PLN-kNN-NB.tex`

## Results

### Round-2 (E 5s, no `-p`, top-256, validation 800 problems)

- MaSh NB: 290/800 (36.25%)
- PLN mixture-local Prior*NB: 288/800 (36.00%)

### Round-4 (E + Vampire, 5s, 28 runs, validation 800 problems)

| Model | E@256 | E@512 | V@256 | V@512 |
|-------|-------|-------|-------|-------|
| PLN mixture-local Prior*NB (EV-pooled) | **288** | **288** | **174** | **173** |
| MaSh NB (E-trained) | 284 | 277 | 171 | 172 |
| MaSh NB (V-trained) | 281 | 280 | 170 | 169 |
| MaSh k-NN (E-trained) | 278 | 285 | 171 | 171 |
| MaSh k-NN (V-trained) | 277 | 283 | 170 | 170 |
| PLN kNN-prior-NB+MaSh (E-trained) | 276 | 280 | 170 | 173 |
| PLN kNN-prior-NB+MaSh (V-trained) | 280 | 280 | 172 | 173 |

### Targeted 30s follow-up (top-256, validation 800 problems)

| Model | E 30s | Vampire 30s |
|-------|-------|-------------|
| MaSh NB | 327/800 (40.88%) | **184/800** (23.00%) |
| PLN mixture-local Prior*NB | 327/800 (40.88%) | 182/800 (22.75%) |

## Selectors

- PLN mixture-local Prior*NB uses `select_pln_mixture_local_nb.py` (pure Python, best single model).
- PLN-NB uses `pln_idf_nb_selector.metta` with `select_pln_nb.py`.
- PLN-Rule uses `pln_premise_selector.metta` with `select_pln_rule.py`.
- PLN-kNN uses `pln_knn_selector.metta` with `select_pln_knn.py`.
- PLN-kNN+NB uses `select_pln_knn.py --merge-nb`.
- PLN-Enhanced uses `pln_enhanced_selector.metta` with `select_pln_enhanced.py`.
- PLN-Normal-NB uses `pln_normal_nb_selector.metta` with `select_pln_normal_nb.py`.

PeTTa selectors live in `../hyperon/PeTTa/demos/`.
Python drivers live in `scripts/`.

## Structure

```
atps/
├── scripts/
│   ├── select_pln_*.py
│   ├── select_mash_*.py
│   ├── mash_*_build_tables.py
│   ├── mash_*_scorer.py
│   ├── run_eprover.py
│   └── run_eprover_parallel.sh
├── datasets/
│   └── extended_mptp5k/
│       ├── chainy/train/
│       ├── chainy/val/
│       ├── deps/
│       ├── features_chainy/
│       ├── features_chainy_val/
│       ├── models/
│       ├── baselines/
│       └── proofs_*/
└── eprover-standard/
```

## Quick start

### MaSh table

```bash
source atps/venv/bin/activate
python3 scripts/mash_nb_build_tables.py
python3 scripts/mash_knn_build_tables.py
```

### Selector

```bash
python3 scripts/select_pln_knn.py --merge-nb \
  --output datasets/extended_mptp5k/baselines/selections_pln_knn_nb_top256.json

python3 scripts/select_pln_normal_nb.py \
  --output datasets/extended_mptp5k/baselines/selections_pln_normal_nb_top256.json
```

### E evaluation

```bash
python3 scripts/run_eprover.py \
  --selections datasets/extended_mptp5k/baselines/selections_pln_knn_nb_top256.json \
  --problems-dir datasets/extended_mptp5k/chainy/val \
  --output-dir datasets/extended_mptp5k/proofs_pln_knn_nb_top256_5s \
  --timeout 5

bash scripts/run_eprover_parallel.sh \
  datasets/extended_mptp5k/baselines/selections_pln_knn_nb_top256.json \
  datasets/extended_mptp5k/chainy/val \
  datasets/extended_mptp5k/proofs_pln_knn_nb_top256_5s \
  6 5
```

## Resource limits

- the limit is 8 cores with `nice -n 19` for the machine.
- the per-problem limit is 5 seconds for E prover.
- the limit is `ulimit -v 6291456` for PeTTa subprocesses.

## Dependencies

- PeTTa is `../hyperon/PeTTa/`.
- PLN libraries are `../hyperon/PeTTa/lib/lib_pln_xi.metta` and `../hyperon/PeTTa/pln_inference/`.
- E prover is `eprover-standard/PROVER/eprover`.
- Python dependencies are numpy and scikit-learn in venv.

## References

- Blanchette et al. 2016 is a core reference.
- Goertzel et al. is a core reference.
- Jakubuv and Urban 2023 is a core reference.
