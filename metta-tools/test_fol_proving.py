#!/usr/bin/env python3
"""
FOL Proving Test Suite using PyRes

Tests that our TPTP FOF problems can be proven by PyRes,
validating that our TPTP import pipeline produces valid formulas.
"""

import subprocess
import sys
from pathlib import Path


PYRES_PATH = Path.home() / 'claude' / 'PyRes' / 'pyres-fof.py'


def prove_with_pyres(tptp_file, timeout=10):
    """
    Run PyRes on TPTP file and return proof status

    Returns: 'Theorem', 'CounterSatisfiable', 'ResourceOut', or 'Unknown'
    """
    try:
        result = subprocess.run(
            ['python3', str(PYRES_PATH), str(tptp_file)],
            capture_output=True,
            text=True,
            timeout=timeout
        )

        output = result.stdout + result.stderr

        if 'SZS status Theorem' in output:
            return 'Theorem'
        elif 'SZS status CounterSatisfiable' in output:
            return 'CounterSatisfiable'
        elif 'SZS status ResourceOut' in output:
            return 'ResourceOut'
        else:
            return 'Unknown'

    except subprocess.TimeoutExpired:
        return 'Timeout'
    except Exception as e:
        return f'Error: {e}'


def extract_stats(tptp_file):
    """Extract proof statistics from PyRes output"""
    result = subprocess.run(
        ['python3', str(PYRES_PATH), str(tptp_file)],
        capture_output=True,
        text=True,
        timeout=10
    )

    output = result.stdout
    stats = {}

    for line in output.split('\n'):
        if 'Initial clauses' in line:
            stats['initial_clauses'] = int(line.split(':')[1].strip())
        elif 'Processed clauses' in line:
            stats['processed_clauses'] = int(line.split(':')[1].strip())
        elif 'Total time' in line:
            stats['time'] = line.split(':')[1].strip()

    return stats


def main():
    """Test PyRes on our FOL test suite"""
    test_dir = Path('test_cases')

    # Expected results for each problem
    expected = {
        'socrates_fof.p': 'Theorem',
        'aristotle_fof.p': 'Theorem',
        'transitivity_fof.p': 'Theorem',
        'existential_fof.p': 'Theorem',
        'functions_fof.p': 'Theorem',
        'pelletier_55.p': 'Theorem',
    }

    print("="*80)
    print("FOL PROVING TEST SUITE (PyRes)")
    print("="*80)
    print()

    results = []

    for problem, expected_status in expected.items():
        problem_path = test_dir / problem

        if not problem_path.exists():
            print(f"❌ SKIP: {problem} (file not found)")
            results.append((problem, 'FileNotFound', expected_status, False))
            continue

        print(f"Testing: {problem}")
        actual_status = prove_with_pyres(problem_path)

        passed = (actual_status == expected_status)
        status_icon = "✅" if passed else "❌"

        print(f"  Expected: {expected_status}")
        print(f"  Actual:   {actual_status}")
        print(f"  {status_icon} {'PASS' if passed else 'FAIL'}")

        # Get stats if theorem
        if actual_status == 'Theorem':
            try:
                stats = extract_stats(problem_path)
                if stats:
                    print(f"  Stats: {stats.get('initial_clauses', '?')} initial clauses, "
                          f"{stats.get('processed_clauses', '?')} processed, "
                          f"{stats.get('time', '?')} time")
            except:
                pass

        print()
        results.append((problem, actual_status, expected_status, passed))

    # Summary
    print("="*80)
    print("SUMMARY")
    print("="*80)

    passed = sum(1 for _, _, _, p in results if p)
    total = len(results)

    for problem, actual, expected, p in results:
        status = "✅ PASS" if p else "❌ FAIL"
        print(f"{status}: {problem:30} ({actual} vs {expected})")

    print()
    print(f"{passed}/{total} tests passed ({100*passed//total if total > 0 else 0}%)")

    return 0 if passed == total else 1


if __name__ == '__main__':
    if not PYRES_PATH.exists():
        print(f"❌ PyRes not found at: {PYRES_PATH}")
        print(f"   Please clone PyRes to ~/claude/PyRes")
        sys.exit(1)

    sys.exit(main())
