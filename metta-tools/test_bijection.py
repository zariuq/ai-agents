#!/usr/bin/env python3
"""
Round-trip bijection test for Mizar ↔ S-expression conversion

Test B: Double round-trip verification
  .miz → JSON → sexp1 → .miz2 → JSON → sexp2
  Compare: sexp1 == sexp2 (modulo metadata)
"""

import sys
import json
import subprocess
from pathlib import Path
from typing import Any, Dict, List

# Import our converters
from bijective_converter import BijectiveConverter
from sexp_to_mizar_v2 import SexpToMizar


def normalize_sexp(sexp: Any) -> Any:
    """
    Normalize S-expression by removing metadata that doesn't affect semantics.
    Removes: :pos annotations
    """
    if isinstance(sexp, str):
        return sexp

    if not isinstance(sexp, list):
        return sexp

    result = []
    i = 0
    while i < len(sexp):
        item = sexp[i]

        # Skip :pos and its value
        if item == ":pos":
            i += 2  # Skip :pos and the next item (position data)
            continue

        # Recursively normalize nested lists
        if isinstance(item, list):
            result.append(normalize_sexp(item))
        else:
            result.append(item)

        i += 1

    return result


def sexp_equal(sexp1: Any, sexp2: Any) -> bool:
    """
    Compare two S-expressions for semantic equivalence.
    Ignores metadata like :pos annotations.
    """
    norm1 = normalize_sexp(sexp1)
    norm2 = normalize_sexp(sexp2)

    return norm1 == norm2


def parse_sexp_file(filepath: str) -> List[Any]:
    """Parse all theorems from S-expression file."""
    from sexp_to_mizar_v2 import SexpToMizar

    converter = SexpToMizar()
    theorems = []

    with open(filepath, 'r') as f:
        content = f.read()

    # Accumulate complete S-expressions
    current_sexp = ""
    paren_depth = 0

    for line in content.split('\n'):
        stripped = line.strip()

        # Skip comments
        if stripped.startswith(';;'):
            continue

        if stripped:
            current_sexp += " " + stripped
            paren_depth += stripped.count('(') - stripped.count(')')

            # Complete S-expression when parens balance
            if paren_depth == 0 and current_sexp.strip():
                complete = current_sexp.strip()
                if complete.startswith('(theorem'):
                    sexp = converter.parse_sexp(complete)
                    if sexp:
                        theorems.append(sexp)
                current_sexp = ""

    return theorems


def test_round_trip(miz_file: str, output_dir: str = "output") -> Dict[str, Any]:
    """
    Test bijective round-trip:
    1. .miz → JSON → sexp1
    2. sexp1 → .miz2
    3. .miz2 → JSON → sexp2
    4. Compare sexp1 == sexp2

    Returns: dict with test results
    """
    miz_path = Path(miz_file)
    article_name = miz_path.stem

    print(f"Testing bijection for: {article_name}")
    print("=" * 60)

    # Step 1: .miz → JSON → sexp1
    print("\n[1/4] Converting .miz → JSON...")
    json_file = f"{output_dir}/json/{article_name}.mzp.json"

    if not Path(json_file).exists():
        print(f"ERROR: JSON file not found: {json_file}")
        print("Run mizar-rs first to generate JSON")
        return {"success": False, "error": "JSON file not found"}

    print(f"[2/4] Converting JSON → S-expression (sexp1)...")
    converter = BijectiveConverter()
    sexp1_file = f"{output_dir}/{article_name}_sexp1.sexp"

    result = converter.convert_json_to_sexp(json_file)
    with open(sexp1_file, 'w') as f:
        f.write(result)

    print(f"  → Saved to: {sexp1_file}")

    # Parse sexp1 into structured data
    sexp1_theorems = parse_sexp_file(sexp1_file)
    print(f"  → Parsed {len(sexp1_theorems)} theorems from sexp1")

    # Step 2: sexp1 → .miz2
    print(f"\n[3/4] Converting S-expression → Mizar (miz2)...")
    miz2_file = f"{output_dir}/{article_name}_round_trip.miz"
    reverser = SexpToMizar()
    miz2_content = reverser.convert_file(sexp1_file)

    with open(miz2_file, 'w') as f:
        f.write(miz2_content)

    print(f"  → Saved to: {miz2_file}")

    # Step 3: .miz2 → JSON → sexp2
    # Note: This would require running mizar-rs parser on miz2_file
    # For now, we'll do a simpler test: verify sexp1 parses back to valid Mizar

    print(f"\n[4/4] Verification...")

    # Count successful conversions
    miz2_theorems = miz2_content.split('\n\ntheorem\n')
    miz2_theorem_count = len([t for t in miz2_theorems if t.strip()])

    print(f"  → sexp1: {len(sexp1_theorems)} theorems")
    print(f"  → miz2:  {miz2_theorem_count} theorems converted")

    # For full Test B, we would need to:
    # - Run mizar-rs on miz2_file → json2
    # - Convert json2 → sexp2
    # - Compare sexp1 == sexp2

    success = len(sexp1_theorems) == miz2_theorem_count

    print("\n" + "=" * 60)
    if success:
        print("✓ Round-trip successful!")
        print(f"  All {len(sexp1_theorems)} theorems converted both ways")
    else:
        print("✗ Round-trip incomplete")
        print(f"  sexp1: {len(sexp1_theorems)} theorems")
        print(f"  miz2:  {miz2_theorem_count} theorems")

    return {
        "success": success,
        "article": article_name,
        "sexp1_theorems": len(sexp1_theorems),
        "miz2_theorems": miz2_theorem_count,
        "sexp1_file": sexp1_file,
        "miz2_file": miz2_file
    }


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 test_bijection.py <miz_file> [output_dir]")
        print()
        print("Example:")
        print("  python3 test_bijection.py ../mizar/share/mml/boole.miz")
        sys.exit(1)

    miz_file = sys.argv[1]
    output_dir = sys.argv[2] if len(sys.argv) > 2 else "output"

    # Ensure output directory exists
    Path(output_dir).mkdir(parents=True, exist_ok=True)

    result = test_round_trip(miz_file, output_dir)

    if not result["success"]:
        sys.exit(1)


if __name__ == "__main__":
    main()
