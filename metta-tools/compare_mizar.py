#!/usr/bin/env python3
"""
Test A: Compare Mizar files with normalization

Normalizes syntactic differences like:
- Extra parentheses: (X \\/ {}) vs X \\/ {}
- Proof content: actual steps vs "..." placeholder
- Justification details: XBOOLE_0:def 1 vs xboole_0
- Whitespace differences
"""

import sys
import re
from typing import List, Tuple


def normalize_mizar_line(line: str) -> str:
    """
    Normalize a Mizar line to ignore syntactic differences.

    Removes:
    - Extra parentheses around formulas
    - Whitespace variations
    - Proof content (replaced with marker)
    """
    # Strip whitespace
    line = line.strip()

    # Skip empty lines
    if not line:
        return ""

    # Normalize proof content to marker
    if line == "...":
        return "PROOF_CONTENT"

    # Skip proof end markers
    if line == "end":
        return ""

    # Normalize extra parentheses in formulas
    # e.g., "(X \\/ {})" -> "X \\/ {}"
    line = re.sub(r'^\((.*)\)$', r'\1', line)

    # Normalize multiple spaces to single space
    line = re.sub(r'\s+', ' ', line)

    # Normalize justification references (strip article details)
    # "by XBOOLE_0:def 1" -> "by xboole_0"
    line = re.sub(r'by\s+([A-Z_]+):.*', r'by \1', line, flags=re.IGNORECASE)

    return line


def extract_theorems(mizar_file: str) -> List[str]:
    """
    Extract and normalize theorems from a Mizar file.

    Returns list of normalized theorem strings.
    """
    with open(mizar_file, 'r') as f:
        content = f.read()

    theorems = []
    current_theorem = []
    in_theorem = False
    proof_depth = 0  # Track nested proof blocks

    for line in content.split('\n'):
        stripped = line.strip()

        # Start of theorem
        if stripped == "theorem" and not in_theorem:
            in_theorem = True
            current_theorem = ["theorem"]
            proof_depth = 0
            continue

        if in_theorem:
            # Start of proof (may be nested)
            if stripped == "proof":
                proof_depth += 1
                current_theorem.append("proof")
                continue

            # End of proof/block (may be nested)
            if stripped == "end" or stripped.startswith("end;"):
                current_theorem.append("end")
                proof_depth -= 1

                # Theorem complete when all proof blocks closed
                if proof_depth == 0:
                    theorems.append('\n'.join(current_theorem))
                    current_theorem = []
                    in_theorem = False
                continue

            # Check if line ends with justification (may be continuation)
            # Handle both "... by Foo;" and "by Foo;" (with or without semicolon)
            if proof_depth == 0 and (" by " in stripped or stripped.startswith("by ")):
                if stripped.endswith(";") or stripped.startswith("by "):
                    current_theorem.append(stripped)
                    # Theorem complete
                    theorems.append('\n'.join(current_theorem))
                    current_theorem = []
                    in_theorem = False
                    continue

            # Add line to current theorem (but normalize proof content)
            if proof_depth > 0 and stripped and not stripped.startswith("proof") and not stripped.startswith("end"):
                # Inside proof - replace with marker
                if not current_theorem or current_theorem[-1] != "...":
                    current_theorem.append("...")
            else:
                current_theorem.append(stripped)

    # Normalize each theorem
    normalized = []
    for thm in theorems:
        lines = [normalize_mizar_line(line) for line in thm.split('\n')]
        # Filter out empty lines
        lines = [l for l in lines if l]
        normalized.append('\n'.join(lines))

    return normalized


def compare_theorem_formulas(thm1: str, thm2: str) -> Tuple[bool, str]:
    """
    Compare two theorems focusing on their mathematical content.

    Returns (is_equal, difference_message)
    """
    # Extract just the formula (line after "theorem")
    # Remove justifications from formulas
    lines1 = [l for l in thm1.split('\n') if l and l != "theorem" and not l.startswith("proof") and not l.startswith("by ")]
    lines2 = [l for l in thm2.split('\n') if l and l != "theorem" and not l.startswith("proof") and not l.startswith("by ")]

    if not lines1 or not lines2:
        return False, "Missing formula"

    formula1 = lines1[0]
    formula2 = lines2[0]

    # Normalize formulas
    def normalize_formula(s):
        # Strip justifications if embedded in formula
        s = re.sub(r'\s+by\s+.*?;?\s*$', '', s)

        # Normalize escaped operators (double backslash to single)
        s = s.replace('\\\\/', '\\/')
        s = s.replace('/\\\\', '/\\')
        s = s.replace('\\\\+\\\\', '\\+\\')
        s = s.replace('\\\\', '\\')  # All remaining double backslashes to single

        # Remove extra parentheses around individual terms
        s = re.sub(r'\(([XYZxyzABC]\s*[\\/+]+\s*\{\})\)', r'\1', s)
        s = re.sub(r'\((\{\}\s*[\\/+]+\s*[XYZxyzABC])\)', r'\1', s)

        # Remove parentheses around conjunctions in st clauses
        s = re.sub(r'\((.*?)\s+(is\s+\w+)\s+&\s+(.*?)\)', r'\1 \2 & \3', s)

        # Remove parentheses around entire formulas after holds
        s = re.sub(r'holds\s+\(([^()]+)\)\s*$', r'holds \1', s)

        # Normalize whitespace
        s = re.sub(r'\s+', ' ', s).strip()

        return s

    formula1 = normalize_formula(formula1)
    formula2 = normalize_formula(formula2)

    if formula1 == formula2:
        return True, ""

    return False, f"Formula mismatch:\n  Expected: {formula1}\n  Got:      {formula2}"


def compare_mizar_files(file1: str, file2: str, verbose: bool = False) -> bool:
    """
    Compare two Mizar files semantically.

    Returns True if equivalent, False otherwise.
    """
    print(f"Comparing Mizar files:")
    print(f"  File 1: {file1}")
    print(f"  File 2: {file2}")
    print()

    theorems1 = extract_theorems(file1)
    theorems2 = extract_theorems(file2)

    print(f"Theorems extracted:")
    print(f"  File 1: {len(theorems1)} theorems")
    print(f"  File 2: {len(theorems2)} theorems")
    print()

    if len(theorems1) != len(theorems2):
        print(f"❌ MISMATCH: Different number of theorems!")
        return False

    all_match = True
    mismatches = []

    for i, (thm1, thm2) in enumerate(zip(theorems1, theorems2), 1):
        matches, msg = compare_theorem_formulas(thm1, thm2)

        if matches:
            if verbose:
                print(f"✓ Theorem {i}: Match")
        else:
            print(f"✗ Theorem {i}: {msg}")
            mismatches.append((i, thm1, thm2))
            all_match = False

    print()
    print("=" * 60)
    if all_match:
        print(f"✅ SUCCESS: All {len(theorems1)} theorems match!")
        return True
    else:
        print(f"❌ FAILURE: {len(mismatches)} theorem(s) don't match")
        return False


def main():
    if len(sys.argv) < 3:
        print("Usage: python3 compare_mizar.py <file1.miz> <file2.miz> [--verbose]")
        print()
        print("Example:")
        print("  python3 compare_mizar.py ../mizar/share/mml/boole.miz ../output/boole_round_trip.miz")
        sys.exit(1)

    file1 = sys.argv[1]
    file2 = sys.argv[2]
    verbose = "--verbose" in sys.argv

    success = compare_mizar_files(file1, file2, verbose)

    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
