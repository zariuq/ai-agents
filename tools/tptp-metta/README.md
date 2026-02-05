# TPTP ↔ MeTTa Conversion Tools

Bijective converters between TPTP (Thousands of Problems for Theorem Provers) format and S-expressions/MeTTa.

## Pipeline

```
TPTP (.p) → S-expression → MeTTa
         ↑               ↓
         └───────────────┘
           (bijective)
```

## Tools

- `tptp_to_sexp.py` - TPTP FOF → S-expression (full FOL support)
- `sexp_to_tptp.py` - S-expression → TPTP FOF (full FOL support)
- `sexp_to_metta.py` - S-expression → MeTTa format
- `test_tptp_bijection.py` - Round-trip bijection tests

## Resolution Prover (propositional)

- `prop_resolution.metta` - Propositional resolution prover in MeTTa
- `tptp_to_resolution.py` - Convert TPTP to resolution format
- `trace_resolution.py` - Resolution proof tracing

Test cases live under `metta-tools/test_cases/` and `tools/tptp-metta/`.

## Usage

```bash
# Convert TPTP to S-expression
python tptp_to_sexp.py problem.p > problem.sexp

# Convert back to TPTP
python sexp_to_tptp.py problem.sexp > problem_reconstructed.p

# Run bijection tests
python test_tptp_bijection.py
```
