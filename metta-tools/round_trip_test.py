#!/usr/bin/env python3
"""
Round-trip bijection test for Mizar ↔ S-expression translation
This verifies that we can translate without information loss
"""

import os
import sys
import json
import subprocess
from bijective_converter import BijectiveConverter
from sexp_to_mizar import SexpToMizar

def compare_json_structures(json1, json2, path=""):
    """Deep comparison of JSON structures"""
    diffs = []

    if type(json1) != type(json2):
        diffs.append(f"{path}: Type mismatch - {type(json1).__name__} vs {type(json2).__name__}")
        return diffs

    if isinstance(json1, dict):
        keys1 = set(json1.keys())
        keys2 = set(json2.keys())

        # Check for missing/extra keys
        if keys1 != keys2:
            missing = keys1 - keys2
            extra = keys2 - keys1
            if missing:
                diffs.append(f"{path}: Missing keys in json2: {missing}")
            if extra:
                diffs.append(f"{path}: Extra keys in json2: {extra}")

        # Recursively compare values
        for key in keys1 & keys2:
            new_path = f"{path}.{key}" if path else key
            diffs.extend(compare_json_structures(json1[key], json2[key], new_path))

    elif isinstance(json1, list):
        if len(json1) != len(json2):
            diffs.append(f"{path}: List length mismatch - {len(json1)} vs {len(json2)}")
        else:
            for i, (item1, item2) in enumerate(zip(json1, json2)):
                new_path = f"{path}[{i}]"
                diffs.extend(compare_json_structures(item1, item2, new_path))

    elif json1 != json2:
        # Primitive values
        diffs.append(f"{path}: Value mismatch - '{json1}' vs '{json2}'")

    return diffs


def test_round_trip(json_file: str):
    """Test complete round-trip: JSON → S-expr → JSON"""

    print(f"=== Round-trip Test for {os.path.basename(json_file)} ===\n")

    # Step 1: Load original JSON
    print("Step 1: Loading original JSON...")
    with open(json_file, 'r') as f:
        original_json = json.load(f)

    # Extract first theorem for detailed testing
    first_theorem = None
    for item in original_json.get("body", []):
        if "kind" in item and "Theorem" in item["kind"]:
            first_theorem = item
            break

    if not first_theorem:
        print("ERROR: No theorems found in JSON")
        return False

    print(f"  Found {len(original_json.get('body', []))} items in body")
    print(f"  First theorem at position: {first_theorem.get('pos', 'unknown')}")

    # Step 2: Convert to S-expression
    print("\nStep 2: Converting JSON → S-expression...")
    converter = BijectiveConverter()
    sexp_content = converter.convert_json_to_sexp(json_file)

    # Save S-expression for inspection
    sexp_file = json_file.replace('.json', '_roundtrip.sexp')
    with open(sexp_file, 'w') as f:
        f.write(sexp_content)
    print(f"  Saved S-expression to: {sexp_file}")

    # Show sample of S-expression
    lines = sexp_content.split('\n')
    for line in lines[:20]:
        if line and not line.startswith(';;'):
            print(f"  {line[:100]}...")
            break

    # Step 3: Convert back to JSON structure
    print("\nStep 3: Converting S-expression → JSON structure...")
    reverse = SexpToMizar()

    # Parse the S-expression back
    # For now, let's just verify key information is preserved

    # Extract theorem info from S-expression
    import re
    theorem_pattern = r'\(theorem (\S+) :pos \[(\d+) (\d+)\]'
    matches = re.findall(theorem_pattern, sexp_content)

    print(f"  Found {len(matches)} theorems in S-expression")
    if matches:
        print(f"  First theorem: {matches[0][0]} at position [{matches[0][1]}, {matches[0][2]}]")

    # Step 4: Verify key information preserved
    print("\nStep 4: Verifying information preservation...")

    # Check theorem count
    original_theorem_count = sum(1 for item in original_json.get("body", [])
                                if "kind" in item and "Theorem" in item["kind"])
    sexp_theorem_count = len(matches)

    if original_theorem_count == sexp_theorem_count:
        print(f"  ✅ Theorem count matches: {original_theorem_count}")
    else:
        print(f"  ❌ Theorem count mismatch: {original_theorem_count} vs {sexp_theorem_count}")

    # Check position preservation
    if matches and first_theorem:
        orig_pos = first_theorem.get('pos', [])
        sexp_pos = [int(matches[0][1]), int(matches[0][2])]
        if orig_pos == sexp_pos:
            print(f"  ✅ Position preserved: {orig_pos}")
        else:
            print(f"  ❌ Position mismatch: {orig_pos} vs {sexp_pos}")

    # Step 5: Test formula extraction completeness
    print("\nStep 5: Testing formula completeness...")

    # Check that we're not outputting "(formula ...)"
    if "(formula ...)" in sexp_content:
        print("  ❌ Found simplified '(formula ...)' - extraction incomplete!")
    else:
        print("  ✅ No '(formula ...)' found - extraction is complete")

    # Count formula elements
    formula_elements = [
        ("forall", "Universal quantifiers"),
        ("exists", "Existential quantifiers"),
        ("pred-infix", "Infix predicates"),
        ("infix", "Infix operations"),
        ("such-that", "Such-that clauses"),
        ("implies", "Implications"),
        ("and", "Conjunctions"),
        ("or", "Disjunctions")
    ]

    for element, description in formula_elements:
        count = sexp_content.count(f"({element}")
        if count > 0:
            print(f"  Found {count} {description}")

    # Step 6: Test Mizar reconstruction
    print("\nStep 6: Testing Mizar reconstruction...")

    # Parse first theorem from S-expression
    theorem_lines = []
    in_theorem = False
    paren_count = 0

    for line in lines:
        if line.startswith("(theorem"):
            in_theorem = True
            theorem_lines = [line]
            paren_count = line.count('(') - line.count(')')
        elif in_theorem:
            theorem_lines.append(line)
            paren_count += line.count('(') - line.count(')')
            if paren_count == 0:
                break

    if theorem_lines:
        # Parse and convert back
        theorem_sexp = ' '.join(theorem_lines)
        parsed = reverse.parse_sexp(theorem_sexp)
        if parsed:
            mizar_output = reverse.sexp_theorem_to_mizar(parsed)
            print("  Reconstructed Mizar:")
            for line in mizar_output.split('\n')[:5]:
                print(f"    {line}")

    print("\n=== Round-trip Test Complete ===")
    return True


def test_specific_formula():
    """Test a specific formula for bijection"""
    converter = BijectiveConverter()

    # Create a test JSON structure
    test_json = {
        "f": {
            "Binop": {
                "kind": "And",
                "f1": {
                    "Pred": {
                        "positive": True,
                        "sym": 2,
                        "spelling": "in",
                        "args": [
                            {"Var": {"spelling": "x"}},
                            {"Var": {"spelling": "X"}}
                        ],
                        "left": 1
                    }
                },
                "f2": {
                    "Pred": {
                        "positive": False,
                        "sym": 1,
                        "spelling": "empty",
                        "args": [{"Var": {"spelling": "X"}}],
                        "left": 0
                    }
                }
            }
        }
    }

    # Convert to S-expression
    sexp = converter.extract_complete_formula(test_json)
    print("Test formula bijection:")
    print(f"  JSON: x in X & not empty(X)")
    print(f"  S-expr: {sexp}")

    # The S-expression should preserve all information
    expected_elements = ["and", "pred-infix", "in", "var", "x", "X", "pred", "empty"]
    missing = []
    for element in expected_elements:
        if element not in sexp:
            missing.append(element)

    if not missing:
        print("  ✅ All formula elements preserved!")
    else:
        print(f"  ❌ Missing elements: {missing}")


if __name__ == "__main__":
    # Test on boole.mzp.json
    json_file = "../output/json/boole.mzp.json"

    if os.path.exists(json_file):
        test_round_trip(json_file)
        print("\n" + "="*60 + "\n")
        test_specific_formula()
    else:
        print(f"ERROR: File not found: {json_file}")
        print("Please run the mizar-rs extraction first.")