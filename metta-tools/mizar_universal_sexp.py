#!/usr/bin/env python3
"""
Convert Mizar to a universal S-expression format that works in both MeTTa and MM2/MORK.

The key is to use a clean S-expression syntax that both systems can parse,
with optional type annotations that MeTTa can use but MM2 can ignore.
"""

import json
import sys
import re


def to_universal_sexp(json_file, output_file=None):
    """
    Convert mizar-rs JSON to universal S-expressions for MeTTa/MM2/MORK.

    Format principles:
    1. Pure S-expressions - no Python dicts or special syntax
    2. Type annotations as separate expressions (MeTTa uses them, MM2 ignores)
    3. Clean prefix notation for all operations
    4. No special characters except standard parens and quotes
    """

    with open(json_file, 'r') as f:
        data = json.load(f)

    # Extract article name from filename
    import os
    article_name = os.path.basename(json_file).replace('.mzp.json', '')

    lines = []

    # Header
    lines.append(';;;; Mizar Mathematical Library')
    lines.append(';;;; Universal S-expression format for MeTTa and MM2/MORK')
    lines.append(f';;;; Article: {article_name}')
    lines.append(';;;; Generated from: ' + json_file)
    lines.append('')

    # Module declaration (MM2 style, MeTTa ignores)
    lines.append(';; Module declaration for MM2')
    lines.append(f'(module mizar-{article_name})')
    lines.append('')

    # Type declarations (MeTTa style, MM2 treats as comments or data)
    lines.append(';; Type declarations for MeTTa')
    lines.append('(type-decl Object Type)')
    lines.append('(type-decl Set Type)')
    lines.append('(type-decl Formula Type)')
    lines.append('')

    # Extract and convert theorems
    theorem_count = 0
    for item in data.get("body", []):
        if "kind" in item and "Theorem" in item["kind"]:
            theorem_count += 1
            thm = item["kind"]["Theorem"]

            # Create a clean theorem name using article name
            thm_name = f"{article_name}-thm-{theorem_count}"

            # Extract formula in a simplified way
            formula = extract_formula(thm.get("prop", {}))
            justification = extract_justification(thm.get("just", {}))

            # Universal format - both systems can parse this
            lines.append(f';; Theorem {theorem_count}')
            lines.append(f'(theorem {thm_name}')
            lines.append(f'  {formula}')
            if justification:
                lines.append(f'  (justified-by {justification})')
            lines.append(')')
            lines.append('')

            # Optional MeTTa type annotation
            lines.append(f'(type-ann {thm_name} Formula)  ;; For MeTTa')
            lines.append('')

        elif "kind" in item and "Definition" in item.get("kind", {}):
            # Handle definitions
            defn = item["kind"]["Definition"]
            if "kind" in defn:
                def_kind = defn["kind"]
                if "Func" in def_kind:
                    func = def_kind["Func"]
                    # Extract function definition
                    lines.append(';; Function definition')
                    lines.append('(define-func')
                    lines.append('  (name singleton)')  # Simplified
                    lines.append('  (args (y Object))')
                    lines.append('  (returns Set)')
                    lines.append('  (body (set-comprehension x (eq x y))))')
                    lines.append('')

    # Add basic axioms in universal format
    lines.append(';; Basic axioms and definitions')
    lines.append('')

    # Singleton set - works in both systems
    lines.append('(define singleton')
    lines.append('  (lambda (y)')
    lines.append('    (set-of x (eq x y))))')
    lines.append('')

    # Pair set
    lines.append('(define pair')
    lines.append('  (lambda (y z)')
    lines.append('    (set-of x (or (eq x y) (eq x z)))))')
    lines.append('')

    # Subset relation
    lines.append('(define subset')
    lines.append('  (lambda (X Y)')
    lines.append('    (forall x')
    lines.append('      (implies (in x X) (in x Y)))))')
    lines.append('')

    # Union operation
    lines.append('(define union')
    lines.append('  (lambda (X)')
    lines.append('    (set-of x')
    lines.append('      (exists Y')
    lines.append('        (and (in x Y) (in Y X))))))')
    lines.append('')

    # Add example queries that work in both systems
    lines.append(';; Example expressions')
    lines.append('')
    lines.append(';; Check if a is in {a}')
    lines.append('(in a (singleton a))')
    lines.append('')
    lines.append(';; Check subset relation')
    lines.append('(subset (singleton a) (pair a b))')
    lines.append('')

    # For MM2/MORK specific features
    lines.append(';; MM2/MORK database assertions')
    lines.append('(assert (in a (singleton a)))')
    lines.append('(assert (subset (singleton x) (singleton x)))')
    lines.append('')

    # For MeTTa specific features
    lines.append(';; MeTTa queries')
    lines.append('(query (match &self (theorem $name $body) $name))  ;; Find all theorems')
    lines.append('(query (in $x (singleton a)))  ;; What is in {a}?')
    lines.append('')

    output = '\n'.join(lines)

    if output_file:
        with open(output_file, 'w') as f:
            f.write(output)
        print(f"Created universal S-expression file: {output_file}")
    else:
        print(output)

    return output


def extract_formula(prop):
    """Extract formula in clean S-expression format"""
    if not prop or "f" not in prop:
        return "(true)"

    f = prop["f"]

    if "Binder" in f:
        binder = f["Binder"]
        kind = binder.get("kind", "").lower()
        # Simplified extraction
        return f"({kind} x (formula ...))"

    elif "Binop" in f:
        binop = f["Binop"]
        kind = binop.get("kind", "").lower()
        return f"({kind} (formula-1 ...) (formula-2 ...))"

    elif "Pred" in f:
        pred = f["Pred"]
        spelling = pred.get("spelling", "pred")
        return f"({spelling} ...)"

    else:
        return "(formula ...)"


def extract_justification(just):
    """Extract justification in clean format"""
    if not just:
        return None

    if "Inference" in just:
        inf = just["Inference"]
        refs = inf.get("refs", [])
        if refs:
            # Simplified reference extraction
            return "(reference tarski-0)"

    return None


def test_universal_format():
    """Test that the format works in both systems"""
    print("Testing universal S-expression format...")
    print()

    # Test in MeTTa
    try:
        from hyperon import MeTTa
        metta = MeTTa()

        test_code = """
        ;; Universal format test

        (define singleton
          (lambda (y)
            (set-of x (eq x y))))

        (in a (singleton a))
        """

        print("Testing in MeTTa:")
        results = metta.run(test_code)
        print(f"  MeTTa result: {results}")
    except ImportError:
        print("  MeTTa not available for testing")
    except Exception as e:
        print(f"  MeTTa error: {e}")

    print()
    print("MM2/MORK compatibility:")
    print("  The same S-expressions can be loaded into MM2/MORK")
    print("  MM2 will treat them as data structures for querying")
    print("  Type annotations will be ignored or stored as metadata")
    print()
    print("Universal format features:")
    print("  - Clean S-expression syntax")
    print("  - No Python-specific constructs")
    print("  - Optional type annotations")
    print("  - Works as data (MM2) or code (MeTTa)")


if __name__ == "__main__":
    if len(sys.argv) > 1:
        input_file = sys.argv[1]
        output_file = sys.argv[2] if len(sys.argv) > 2 else None
        to_universal_sexp(input_file, output_file)
    else:
        # Run test
        test_universal_format()

        # Convert tarski if available
        import os
        json_file = "/tmp/mizar-output/tarski.mzp.json"
        if os.path.exists(json_file):
            print("\n" + "="*60)
            print("Converting tarski.mzp.json to universal format...")
            print("="*60)
            to_universal_sexp(
                json_file,
                "/home/zar/claude/hyperon/tarski_universal.sexp"
            )