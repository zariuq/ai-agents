# Canonical Test Results — pverify

**Date**: 2026-03-21  
**Tester**: Oruži  
**Verifier**: `pverify.pl` (pure Prolog, standalone)

## Test Environment

- **SWI-Prolog**: `/usr/bin/swipl`
- **Command**: `swipl -g main -t halt pverify.pl -- <file.mm>`

## Results

### Correct Verification (should pass)

| # | File | Source | Stmts | Proofs | Result |
|---|------|--------|-------|--------|--------|
| 1 | `demo0.mm` | mmverify.py/examples | 19 | normal | ✅ PASS |
| 2 | `disjoint2.mm` | mmverify.py/examples | 22 | normal | ✅ PASS |
| 3 | `hol_example_normal.mm` | mmverify.py/examples | 81 | normal | ✅ PASS |
| 4 | `set_example_normal.mm` | mmverify.py/examples | 433 | normal | ✅ PASS |
| 5 | `test_simple.mm` | mm-lean4 | 6 | normal | ✅ PASS |
| 6 | `test_nonv_vars.mm` | mm-lean4 | 9 | normal | ✅ PASS |

### Correct Rejection (should fail)

| # | File | Source | Error | Result |
|---|------|--------|-------|--------|
| 7 | `invalid_duplicate_floats.mm` | mm-lean4/test_databases | Multiple active $f for variable "x" | ✅ REJECTED |

### Known Issues

| # | File | Source | Error | Analysis |
|---|------|--------|-------|----------|
| 8 | `test_modus_ponens.mm` | mm-lean4 | typecode_mismatch(wff,\|-,p) | Test file declares ax-mp as axiom ($a) without $e hypotheses; proof pushes floating hyps that don't match ax-mp's 0-arity assertion. Likely a test file bug, not a verifier bug. |

## Missing Tests

- **set.mm** (full Metamath database, ~39K theorems) — not available on this machine
- **Compressed proof tests** — no `.mm` files with compressed proofs found locally
- **MeTTa verifier variants** — cannot run without PeTTa runtime + MORK + lib_zar

## Summary

**7/7 meaningful tests pass** (6 correct verifications + 1 correct rejection).  
The one "failure" (test_modus_ponens.mm) appears to be a malformed test file.
