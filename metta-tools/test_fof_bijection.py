#!/usr/bin/env python3
"""
FOF Bijection Test Suite

Tests the bijective mapping: TPTP ↔ S-expressions
Implements double round-trip verification:
  TPTP → SEXP → TPTP2 → SEXP2

Verifies: SEXP ≈ SEXP2 (formulas are identical, ignoring metadata)
"""

import json
import subprocess
import sys
from pathlib import Path


def run_tptp_to_sexp(tptp_file):
    """Convert TPTP to S-expression (JSON)"""
    result = subprocess.run(
        ['python3', 'tptp_to_sexp.py', tptp_file],
        capture_output=True,
        text=True
    )
    if result.returncode != 0:
        print(f"❌ TPTP→SEXP conversion failed: {result.stderr}")
        return None

    json_file = tptp_file.replace('.p', '.json')
    return json_file


def run_sexp_to_tptp(json_file, output_tptp):
    """Convert S-expression (JSON) to TPTP"""
    result = subprocess.run(
        ['python3', 'sexp_to_tptp.py', json_file, output_tptp],
        capture_output=True,
        text=True
    )
    if result.returncode != 0:
        print(f"❌ SEXP→TPTP conversion failed: {result.stderr}")
        return False
    return True


def load_json(json_file):
    """Load JSON file"""
    with open(json_file, 'r') as f:
        return json.load(f)


def compare_formulas(sexp1, sexp2):
    """Compare two S-expressions, ignoring metadata/comments"""
    formulas1 = sexp1.get('formulas', [])
    formulas2 = sexp2.get('formulas', [])

    if len(formulas1) != len(formulas2):
        print(f"❌ Different number of formulas: {len(formulas1)} vs {len(formulas2)}")
        return False

    for i, (f1, f2) in enumerate(zip(formulas1, formulas2)):
        # Compare name, role, and formula
        if f1['name'] != f2['name']:
            print(f"❌ Formula {i}: Name mismatch: {f1['name']} vs {f2['name']}")
            return False

        if f1['role'] != f2['role']:
            print(f"❌ Formula {i}: Role mismatch: {f1['role']} vs {f2['role']}")
            return False

        if f1['formula'] != f2['formula']:
            print(f"❌ Formula {i} ({f1['name']}): Formula mismatch")
            print(f"   Original:  {f1['formula']}")
            print(f"   Round-trip: {f2['formula']}")
            return False

    return True


def test_double_roundtrip(tptp_file):
    """
    Test double round-trip: TPTP → SEXP → TPTP2 → SEXP2
    Verify: SEXP ≈ SEXP2 (formulas identical)
    """
    print(f"\n{'='*80}")
    print(f"Testing: {tptp_file}")
    print(f"{'='*80}")

    # Step 1: TPTP → SEXP
    print("Step 1: TPTP → SEXP")
    json1 = run_tptp_to_sexp(tptp_file)
    if not json1:
        return False
    print(f"  ✅ Generated {json1}")

    # Step 2: SEXP → TPTP2
    print("Step 2: SEXP → TPTP2")
    tptp2 = tptp_file.replace('.p', '_reconstructed.p')
    if not run_sexp_to_tptp(json1, tptp2):
        return False
    print(f"  ✅ Generated {tptp2}")

    # Step 3: TPTP2 → SEXP2
    print("Step 3: TPTP2 → SEXP2")
    json2 = run_tptp_to_sexp(tptp2)
    if not json2:
        return False
    print(f"  ✅ Generated {json2}")

    # Step 4: Compare SEXP ≈ SEXP2
    print("Step 4: Comparing SEXP ≈ SEXP2")
    sexp1 = load_json(json1)
    sexp2 = load_json(json2)

    if compare_formulas(sexp1, sexp2):
        print(f"  ✅ Bijection verified! Formulas are identical.")
        print(f"     Original SEXP: {len(sexp1['formulas'])} formulas")
        print(f"     Round-trip SEXP: {len(sexp2['formulas'])} formulas")
        return True
    else:
        print(f"  ❌ Bijection FAILED! Formulas differ.")
        return False


def main():
    """Run tests on all TPTP test cases"""
    test_dir = Path('test_cases')

    # Find all .p files that are NOT reconstructed files
    tptp_files = [
        str(f) for f in test_dir.glob('*.p')
        if '_reconstructed' not in f.name
    ]

    if not tptp_files:
        print("❌ No TPTP test files found in test_cases/")
        return 1

    print(f"\n{'='*80}")
    print(f"FOF BIJECTION TEST SUITE")
    print(f"{'='*80}")
    print(f"Testing {len(tptp_files)} problems")
    print(f"{'='*80}")

    results = []
    for tptp_file in sorted(tptp_files):
        passed = test_double_roundtrip(tptp_file)
        results.append((tptp_file, passed))

    # Summary
    print(f"\n{'='*80}")
    print(f"SUMMARY")
    print(f"{'='*80}")
    passed = sum(1 for _, p in results if p)
    total = len(results)

    for tptp_file, p in results:
        status = "✅ PASS" if p else "❌ FAIL"
        print(f"{status}: {tptp_file}")

    print(f"\n{passed}/{total} tests passed ({100*passed//total}%)")

    return 0 if passed == total else 1


if __name__ == '__main__':
    sys.exit(main())
