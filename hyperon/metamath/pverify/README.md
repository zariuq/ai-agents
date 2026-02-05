# pverify — Prolog + PeTTa Metamath Verifier

Hybrid verifier: Prolog parses `.mm` files into structured terms, and PeTTa executes
verification rules over those terms.

## Architecture (high‑level)

1. **Prolog** parses `.mm` into structured statements (DCG in `mm_primitives.pl`)
2. **PeTTa** processes statements and checks proofs (various `pverify*.metta` files)
3. End‑to‑end wrapper: `verify_mm.sh`

## Main entrypoints

- `pmverify.metta` — MORK‑optimized verifier
- `pverify_hybrid.metta` — baseline implementation

See `STATUS.md` for current integration notes and `CANONICAL_TEST_RESULTS.md` for test results.

## Usage (PeTTa runner)

```bash
cd ../../PeTTa
./run.sh ../metamath/pverify/pmverify.metta /path/to/file.mm --silent
# or
./run.sh ../metamath/pverify/pverify_hybrid.metta /path/to/file.mm --silent
```

Wrapper:
```bash
./verify_mm.sh /path/to/file.mm
```

## Review checklist

```bash
# Status notes
cat STATUS.md

# Canonical test results
cat CANONICAL_TEST_RESULTS.md
```
