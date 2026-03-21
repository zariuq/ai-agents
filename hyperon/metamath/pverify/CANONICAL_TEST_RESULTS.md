# Canonical Test Results -- pverify

**Date**: 2026-03-21  
**Tester**: Oruzi  
**Verifier**: `pverify.pl` (pure Prolog, standalone)

## Test Environment

- **SWI-Prolog**: `/usr/bin/swipl`
- **Command**: `swipl -g main -t halt pverify.pl -- <file.mm>`

## Results

### Correct Verification (should pass)

| # | File | Source | Stmts | Proof Type | Result |
|---|------|--------|-------|------------|--------|
| 1 | `demo0.mm` | mmverify.py/examples | 19 | normal | PASS |
| 2 | `disjoint2.mm` | mmverify.py/examples | 22 | normal | PASS |
| 3 | `hol_example_normal.mm` | mmverify.py/examples | 81 | normal | PASS |
| 4 | `set_example_normal.mm` | mmverify.py/examples | 433 | normal | PASS |
| 5 | `test_simple.mm` | mm-lean4 | 6 | normal | PASS |
| 6 | `test_nonv_vars.mm` | mm-lean4 | 9 | normal | PASS |
| 7 | `test_modus_ponens_fixed.mm` | Oruzi (new) | 14 | normal | PASS |
| 8 | `test_compressed_proof.mm` | Oruzi (new) | 14 | compressed | PASS |

### Correct Rejection (should fail)

| # | File | Source | Error | Result |
|---|------|--------|-------|--------|
| 9 | `invalid_duplicate_floats.mm` | mm-lean4/test_databases | Multiple active $f for variable "x" | REJECTED |

### Known Issues

| # | File | Source | Error | Analysis |
|---|------|--------|-------|----------|
| 10 | `test_modus_ponens.mm` | mm-lean4 | typecode_mismatch(wff,\|-,p) | Test file declares ax-mp as axiom ($a) without $e hypotheses; proof pushes floating hyps that don't match ax-mp's 0-arity assertion. Test file bug, not verifier bug. |

## New Test Files Created

### test_modus_ponens_fixed.mm
Proper modus ponens test with $e hypotheses for ax-mp.
Proves the identity theorem `|- (p -> p)` using the standard 5-step proof
(Margaris p. 51, Hamilton Example 2.7(a), Bell/Machover Lemma 10.3).

### test_compressed_proof.mm
Same proof as test_modus_ponens_fixed.mm but encoded in Metamath compressed
proof format. Tests the compressed proof decoder and verifier.

## Missing Tests

- **set.mm** (full Metamath database, ~39K theorems) -- not available on this machine
- **MeTTa verifier variants** -- cannot run without PeTTa runtime + MORK + lib_zar

## Summary

**9/9 meaningful tests pass** (8 correct verifications + 1 correct rejection).
The one "failure" (test_modus_ponens.mm) is a malformed test file.
