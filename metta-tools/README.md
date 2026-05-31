# MeTTa formal-reasoning bridge tools — Mizar · TPTP · resolution (WIP)

Converters and prototypes that move formal-mathematics problems — Mizar and
TPTP first-order logic — into MeTTa S-expression form (and back), and feed an
in-progress MeTTa resolution prover. S-expressions are the shared interchange
format throughout.

> **Status: work in progress / experimental.** The pipelines below are at
> different maturity levels and several scripts are exploratory. The Mizar entry
> point depends on an external `mizar-rs` parser that is **not bundled in this
> directory** — point the Mizar commands at your own `mizar-rs` checkout and its
> JSON output.

## Pipelines

### Mizar → S-expression / MeTTa / MORK

Consume the JSON produced by the external `mizar-rs` parser and emit
S-expressions.

| Script | Output |
|--------|--------|
| `mizar_rs_to_sexp.py` | clean S-expressions from mizar-rs JSON |
| `mizar_to_metta.py` | MeTTa-executable format with type annotations |
| `mizar_universal_sexp.py` | S-expressions usable in both MeTTa and MM2/MORK |
| `mizar_proof_verifier.py` | proof + verification-step structure |

```bash
# requires an external mizar-rs producing <article>.mzp.json
python3 mizar_rs_to_sexp.py article.mzp.json article.sexp
python3 mizar_universal_sexp.py article.mzp.json article.sexp   # MeTTa + MM2/MORK
```

Illustrative MeTTa output (`mizar_to_metta.py`):

```lisp
(: singleton (-> Object Set))
(= (in $x (singleton $y)) (eq $x $y))
```

### Mizar ↔ S-expression bijection (lossless round-trip)

Check that conversion loses no information by translating back and comparing.

| Script | Role |
|--------|------|
| `bijective_converter.py` | Mizar ↔ S-expr, extracting full structure |
| `sexp_to_mizar.py`, `sexp_to_mizar_v2.py` | reverse: S-expr → Mizar |
| `round_trip_test.py` | round-trip bijection test |
| `compare_mizar.py` | normalized Mizar-file comparison |

### TPTP FOF pipeline

| Script | Role |
|--------|------|
| `tptp_to_sexp.py`, `sexp_to_tptp.py` | bijective TPTP FOF ↔ S-expr |
| `tptp_to_metta.py`, `sexp_to_metta.py` | → MeTTa backward-chainer format |
| `tptp_to_resolution.py`, `generate_cnf.py` | CNF via E prover → MeTTa resolution clauses |
| `test_fof_bijection.py`, `test_tptp_bijection.py` | round-trip tests |

### MeTTa resolution prover (prototype)

| File | Role |
|------|------|
| `prop_resolution.metta` | propositional resolution in MeTTa |
| `tptp_benchmark/superposition.metta` | superposition experiments |
| `create_tptp_benchmark.py`, `select_tptp_benchmark.py`, `build_benchmark_42.py` | build a 42-problem FOF benchmark (SAT/UNSAT, graded difficulty) |
| `tptp_benchmark/` | benchmark problems + run scripts (`run_benchmark.sh`, `count_statuses.sh`) |
| `trace_resolution.py` | trace a reference (pyprover) resolution run |

### Megalodon bridge (prototype)

`megalodon-bridge/` — MeTTa ↔ Megalodon (`.mg`) round-trip experiments
(apply, let-in, section vars, if-then, …).

## Prerequisites

- Python 3
- Mizar pipeline: an external `mizar-rs` checkout producing `*.mzp.json`, plus the Mizar MML (`MIZFILES`).
- TPTP/resolution pipeline: an E prover binary on `PATH` (for CNF generation).
- MeTTa (optional, to run generated `.metta`): `conda activate hyperon`.

## Test artifacts

`test_cases/` holds worked round-trips (e.g. `aristotle_fof.*`, `aristotle_cnf.*`)
with `*_reconstructed.*` outputs beside the originals for bijection checks.

## Known limitations

- The Mizar pipeline depends on the external `mizar-rs` parser, which is not included here.
- Some Mizar articles crash `mizar-rs`; `SchemeBlock` items are not fully handled.
- The resolution prover and the Megalodon bridge are early prototypes.
