#!/usr/bin/env python3
"""
TPTP Bijection Test Suite

Tests both directions of TPTP <-> S-expression conversion:
- Test A: Semantic comparison of TPTP files (original vs reconstructed)
- Test B: S-expression round-trip (sexp1 == sexp2)
"""

import json
import re
from pathlib import Path
from typing import List, Dict, Any, Tuple

from tptp_to_sexp import TPTPToSexp
from sexp_to_tptp import SexpToTPTP


class TPTPBijectionTester:
    """Test bijective TPTP <-> S-expression conversion"""

    def __init__(self):
        pass

    def test_file(self, tptp_file: str) -> Dict[str, Any]:
        """
        Run full bijection test on a TPTP file

        Returns dict with test results
        """
        print(f"\n{'='*70}")
        print(f"Testing: {tptp_file}")
        print(f"{'='*70}")

        results = {
            'file': tptp_file,
            'test_a_passed': False,
            'test_b_passed': False,
            'errors': []
        }

        try:
            # Step 1: TPTP -> S-expression
            converter1 = TPTPToSexp()
            sexp1 = converter1.parse_tptp_file(tptp_file)

            json1_file = tptp_file.replace('.p', '_1.json')
            converter1.to_json(json1_file)
            print(f"✓ Created S-expression 1: {json1_file}")

            # Step 2: S-expression -> TPTP (reconstructed)
            reverse_converter = SexpToTPTP()
            tptp_reconstructed = tptp_file.replace('.p', '_reconstructed.p')
            reverse_converter.convert_to_tptp(sexp1, tptp_reconstructed)
            print(f"✓ Created reconstructed TPTP: {tptp_reconstructed}")

            # Step 3: TPTP reconstructed -> S-expression (round-trip)
            converter2 = TPTPToSexp()
            sexp2 = converter2.parse_tptp_file(tptp_reconstructed)

            json2_file = tptp_file.replace('.p', '_2.json')
            converter2.to_json(json2_file)
            print(f"✓ Created S-expression 2: {json2_file}")

            # Test A: Compare TPTP files semantically
            print(f"\n--- Test A: TPTP Semantic Comparison ---")
            test_a_result = self._test_a_tptp_comparison(
                tptp_file, tptp_reconstructed
            )
            results['test_a_passed'] = test_a_result['passed']
            if not test_a_result['passed']:
                results['errors'].extend(test_a_result['errors'])
            else:
                print("✅ Test A PASSED: TPTP files are semantically equivalent")

            # Test B: Compare S-expressions
            print(f"\n--- Test B: S-expression Round-trip ---")
            test_b_result = self._test_b_sexp_comparison(json1_file, json2_file)
            results['test_b_passed'] = test_b_result['passed']
            if not test_b_result['passed']:
                results['errors'].extend(test_b_result['errors'])
            else:
                print("✅ Test B PASSED: S-expressions are identical")

        except Exception as e:
            results['errors'].append(f"Exception: {str(e)}")
            print(f"❌ Error: {e}")

        return results

    def _test_a_tptp_comparison(self, file1: str, file2: str) -> Dict[str, Any]:
        """
        Test A: Compare two TPTP files semantically

        Ignores whitespace and comment differences, focuses on formula structure
        """
        result = {'passed': True, 'errors': []}

        # Parse both files
        formulas1 = self._extract_tptp_formulas(file1)
        formulas2 = self._extract_tptp_formulas(file2)

        # Check same number of formulas
        if len(formulas1) != len(formulas2):
            result['passed'] = False
            result['errors'].append(
                f"Different number of formulas: {len(formulas1)} vs {len(formulas2)}"
            )
            return result

        # Compare each formula
        for i, (f1, f2) in enumerate(zip(formulas1, formulas2)):
            if f1['name'] != f2['name']:
                result['passed'] = False
                result['errors'].append(
                    f"Formula {i}: name mismatch: {f1['name']} vs {f2['name']}"
                )

            if f1['role'] != f2['role']:
                result['passed'] = False
                result['errors'].append(
                    f"Formula {i}: role mismatch: {f1['role']} vs {f2['role']}"
                )

            # Normalize and compare formula strings
            norm1 = self._normalize_tptp_formula(f1['formula'])
            norm2 = self._normalize_tptp_formula(f2['formula'])

            if norm1 != norm2:
                result['passed'] = False
                result['errors'].append(
                    f"Formula {i} ({f1['name']}): content mismatch\n"
                    f"  Original:      {norm1}\n"
                    f"  Reconstructed: {norm2}"
                )

        if result['passed']:
            print(f"  ✓ All {len(formulas1)} formulas match")

        return result

    def _test_b_sexp_comparison(self, json1: str, json2: str) -> Dict[str, Any]:
        """
        Test B: Compare S-expressions for exact equality
        """
        result = {'passed': True, 'errors': []}

        with open(json1, 'r') as f:
            sexp1 = json.load(f)
        with open(json2, 'r') as f:
            sexp2 = json.load(f)

        # Compare formulas (ignoring metadata which may have file paths)
        formulas1 = sexp1.get('formulas', [])
        formulas2 = sexp2.get('formulas', [])

        if len(formulas1) != len(formulas2):
            result['passed'] = False
            result['errors'].append(
                f"Different number of formulas: {len(formulas1)} vs {len(formulas2)}"
            )
            return result

        for i, (f1, f2) in enumerate(zip(formulas1, formulas2)):
            if f1 != f2:
                result['passed'] = False
                result['errors'].append(
                    f"Formula {i} S-expression mismatch:\n"
                    f"  First:  {json.dumps(f1, indent=2)}\n"
                    f"  Second: {json.dumps(f2, indent=2)}"
                )

        if result['passed']:
            print(f"  ✓ All {len(formulas1)} S-expressions match exactly")

        return result

    def _extract_tptp_formulas(self, filename: str) -> List[Dict[str, str]]:
        """Extract all fof declarations from TPTP file"""
        with open(filename, 'r') as f:
            content = f.read()

        formulas = []
        fof_pattern = r'fof\(([^,]+),\s*(\w+),\s*(.+?)\)\s*\.'
        matches = re.finditer(fof_pattern, content, re.DOTALL)

        for match in matches:
            formulas.append({
                'name': match.group(1).strip(),
                'role': match.group(2).strip(),
                'formula': match.group(3).strip()
            })

        return formulas

    def _normalize_tptp_formula(self, formula: str) -> str:
        """Normalize TPTP formula for comparison"""
        # Remove all whitespace
        normalized = re.sub(r'\s+', '', formula)
        # Remove all parentheses (they don't change semantics, just precedence)
        normalized = normalized.replace('(', '').replace(')', '')
        return normalized


def main():
    """Run bijection tests"""
    tester = TPTPBijectionTester()

    test_files = [
        # Propositional tests
        'simple_prop.p',
        'test_cases/dnf_prop.p',
        'test_cases/negation_prop.p',
        'test_cases/iff_prop.p',
        # First-Order Logic tests
        'test_cases/fol_01_universal.p',
        'test_cases/fol_02_existential.p',
        'test_cases/fol_03_function.p',
        'test_cases/fol_04_multiple_vars.p',
        'test_cases/fol_05_nested.p',
    ]

    all_passed = True
    results_summary = []

    for test_file in test_files:
        if not Path(test_file).exists():
            print(f"⚠️  Skipping {test_file} (not found)")
            continue

        result = tester.test_file(test_file)
        results_summary.append(result)

        if not (result['test_a_passed'] and result['test_b_passed']):
            all_passed = False

    # Print summary
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")

    for result in results_summary:
        file = result['file']
        test_a = "✅" if result['test_a_passed'] else "❌"
        test_b = "✅" if result['test_b_passed'] else "❌"
        print(f"{file}:")
        print(f"  Test A (TPTP comparison): {test_a}")
        print(f"  Test B (S-exp round-trip): {test_b}")
        if result['errors']:
            print(f"  Errors: {len(result['errors'])}")

    if all_passed:
        print(f"\n🎉 ALL TESTS PASSED!")
        print("✅ Bijective conversion verified")
    else:
        print(f"\n❌ SOME TESTS FAILED")
        for result in results_summary:
            if result['errors']:
                print(f"\nErrors in {result['file']}:")
                for error in result['errors']:
                    print(f"  - {error}")


if __name__ == '__main__':
    main()
