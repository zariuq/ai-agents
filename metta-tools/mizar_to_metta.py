#!/usr/bin/env python3
"""
Convert Mizar S-expressions to MeTTa-compatible format.
MeTTa has specific requirements for its S-expression syntax.
"""

import re

def convert_to_metta(sexp_file, output_file=None):
    """
    Convert Mizar S-expressions to MeTTa format.
    """

    metta_lines = []
    metta_lines.append(";; Mizar Mathematical Library in MeTTa format")
    metta_lines.append(";; Converted from Mizar S-expressions")
    metta_lines.append("")

    # Add type declarations
    metta_lines.append(";; Type declarations")
    metta_lines.append("(: Object Type)")
    metta_lines.append("(: Set Type)")
    metta_lines.append("(: Formula Type)")
    metta_lines.append("")

    # Add basic predicates
    metta_lines.append(";; Basic predicates")
    metta_lines.append("(: in (-> Object Set Formula))")
    metta_lines.append("(: eq (-> Object Object Formula))")
    metta_lines.append("(: subset (-> Set Set Formula))")
    metta_lines.append("")

    # Add logical operators
    metta_lines.append(";; Logical operators")
    metta_lines.append("(: and (-> Formula Formula Formula))")
    metta_lines.append("(: or (-> Formula Formula Formula))")
    metta_lines.append("(: not (-> Formula Formula))")
    metta_lines.append("(: implies (-> Formula Formula Formula))")
    metta_lines.append("(: iff (-> Formula Formula Formula))")
    metta_lines.append("(: forall (-> Variable Formula Formula))")
    metta_lines.append("(: exists (-> Variable Formula Formula))")
    metta_lines.append("")

    with open(sexp_file, 'r') as f:
        content = f.read()

    # Extract theorems
    theorem_pattern = r'\(theorem\s+\(pos\s+\d+\s+\d+\)\s+(.*?)\s+\(by.*?\)\)'
    theorems = re.findall(theorem_pattern, content, re.DOTALL)

    metta_lines.append(";; Theorems from Mizar")
    for i, theorem in enumerate(theorems[:10], 1):  # Just first 10 for demo
        # Clean up the theorem content
        theorem = theorem.replace('\n', ' ')
        theorem = re.sub(r'\s+', ' ', theorem)

        # Create a simplified MeTTa representation
        metta_lines.append(f"(: theorem-{i} Formula)")

        # Try to extract the main structure
        if "forall" in theorem:
            metta_lines.append(f"(= theorem-{i}")
            metta_lines.append(f"   (forall $x")
            metta_lines.append(f"     (mizar-formula {i})))")
        elif "imp" in theorem:
            metta_lines.append(f"(= theorem-{i}")
            metta_lines.append(f"   (implies")
            metta_lines.append(f"     (mizar-antecedent {i})")
            metta_lines.append(f"     (mizar-consequent {i})))")
        else:
            metta_lines.append(f"(= theorem-{i} (mizar-formula {i}))")
        metta_lines.append("")

    # Add some example definitions
    metta_lines.append(";; Example definitions from Mizar")
    metta_lines.append("")
    metta_lines.append(";; Singleton set")
    metta_lines.append("(: singleton (-> Object Set))")
    metta_lines.append("(= (in $x (singleton $y))")
    metta_lines.append("   (eq $x $y))")
    metta_lines.append("")

    metta_lines.append(";; Pair set")
    metta_lines.append("(: pair (-> Object Object Set))")
    metta_lines.append("(= (in $x (pair $y $z))")
    metta_lines.append("   (or (eq $x $y) (eq $x $z)))")
    metta_lines.append("")

    metta_lines.append(";; Union")
    metta_lines.append("(: union (-> Set Set))")
    metta_lines.append("(= (in $x (union $X))")
    metta_lines.append("   (exists $Y")
    metta_lines.append("     (and (in $x $Y) (in $Y $X))))")
    metta_lines.append("")

    # Add queries
    metta_lines.append(";; Example queries")
    metta_lines.append("")
    metta_lines.append(";; Query: Is a in {a}?")
    metta_lines.append("!(in a (singleton a))")
    metta_lines.append("")
    metta_lines.append(";; Query: Find all theorems")
    metta_lines.append("!(match &self (: $thm Formula) $thm)")
    metta_lines.append("")

    output = '\n'.join(metta_lines)

    if output_file:
        with open(output_file, 'w') as f:
            f.write(output)
        print(f"Created MeTTa file: {output_file}")
    else:
        print(output)

    return output


def test_in_metta():
    """Test the MeTTa format directly"""
    from hyperon import MeTTa

    metta = MeTTa()

    # Create a simple test
    test_code = """
    ;; Simple Mizar concepts in MeTTa

    ;; Types
    (: Object Type)
    (: Set Type)

    ;; Basic operations
    (: singleton (-> Object Set))
    (: in (-> Object Set Bool))
    (: eq (-> Object Object Bool))

    ;; Axiom: x in {y} iff x = y
    (= (in $x (singleton $y))
       (eq $x $y))

    ;; Test: a in {a}
    !(in a (singleton a))

    ;; Test: a in {b}
    !(in a (singleton b))
    """

    print("Testing MeTTa code:")
    print(test_code)
    print("\nResults:")

    try:
        results = metta.run(test_code)
        for r in results:
            print(f"  {r}")
    except Exception as e:
        print(f"Error: {e}")


if __name__ == "__main__":
    import sys

    if len(sys.argv) > 1:
        input_file = sys.argv[1]
        output_file = sys.argv[2] if len(sys.argv) > 2 else None
        convert_to_metta(input_file, output_file)
    else:
        # Run the test
        print("Running MeTTa test...\n")
        test_in_metta()

        # Also convert the tarski file if it exists
        import os
        if os.path.exists("/home/zar/claude/hyperon/tarski_clean.sexp"):
            print("\n" + "="*50)
            print("Converting tarski_clean.sexp to MeTTa format...")
            print("="*50)
            convert_to_metta(
                "/home/zar/claude/hyperon/tarski_clean.sexp",
                "/home/zar/claude/hyperon/tarski.metta"
            )