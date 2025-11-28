#!/usr/bin/env python3
"""
TPTP to MeTTa Resolution Prover Pipeline (Using E Prover for CNF)

Workflow:
1. Use E prover to convert TPTP FOF to CNF
2. Parse E's CNF output
3. Generate MeTTa clauses for prop_resolution.metta

This version uses TRUSTED E prover for CNF conversion!
"""

import sys
import subprocess
import re
import os


def eprover_cnf(tptp_file, eprover_path="../../eprover/PROVER/eprover"):
    """
    Use E prover to convert TPTP to CNF

    Returns list of CNF clauses
    """
    cmd = [
        eprover_path,
        "--cnf",
        "--tstp-format",
        "--no-preprocessing",
        tptp_file
    ]

    result = subprocess.run(cmd, capture_output=True, text=True)

    if result.returncode != 0:
        raise RuntimeError(f"E prover failed: {result.stderr}")

    return parse_e_cnf_output(result.stdout)


def parse_e_cnf_output(output):
    """
    Parse E prover's CNF output

    Example CNF line:
      cnf(i_0_1, plain, (knight_a|knave_a)).
      cnf(i_0_3, plain, (~knight_a|~knave_a)).

    Returns: list of (name, role, clause) tuples
    """
    clauses = []

    # Match cnf(...) lines
    cnf_pattern = r'cnf\(([^,]+),\s*([^,]+),\s*\(([^)]+)\)\)\.'

    for match in re.finditer(cnf_pattern, output):
        name = match.group(1)
        role = match.group(2)
        clause_str = match.group(3)

        # Parse clause literals
        literals = parse_clause_literals(clause_str)
        clauses.append((name, role, literals))

    return clauses


def parse_clause_literals(clause_str):
    """
    Parse clause literal string

    Input: "knight_a|knave_a" or "~knight_a|~knave_a"
    Output: ['knight_a', 'knave_a'] or ['~knight_a', '~knave_a']
    """
    # Split by |
    parts = [p.strip() for p in clause_str.split('|')]
    return parts


def cnf_to_metta_clause(literals, clause_type="axiom"):
    """
    Convert CNF clause to MeTTa format (tagged for pattern matching)

    Input: ['knight_a', '~knave_a'], 'axiom'
    Output: '(axiom (lit knight_a) (nlit knave_a))'
    """
    metta_lits = []
    for lit in literals:
        if lit.startswith('~'):
            # Negative literal
            atom = lit[1:]
            metta_lits.append(f"(nlit {atom})")
        else:
            # Positive literal
            metta_lits.append(f"(lit {lit})")

    return f"({clause_type} " + " ".join(metta_lits) + ")"


def generate_metta_resolution_file(cnf_clauses, output_file):
    """Generate a MeTTa file with CNF clauses for resolution"""

    with open(output_file, 'w') as f:
        f.write(";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n")
        f.write(";;; CNF Clauses for Propositional Resolution\n")
        f.write(";;; Auto-generated from TPTP via E Prover\n")
        f.write(";;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n")


        axiom_clauses = []
        goal_clauses = []

        for name, role, literals in cnf_clauses:
            clause_str = ' | '.join(literals) if literals else 'FALSE'
            f.write(f";; {name} ({role}): {clause_str}\n")

            if role in ['plain', 'axiom']:
                metta_clause = cnf_to_metta_clause(literals, 'axiom')
                f.write(f"{metta_clause}\n\n")
                axiom_clauses.append(metta_clause)
            elif role == 'negated_conjecture':
                # E already negated the conjecture for refutation
                metta_clause = cnf_to_metta_clause(literals, 'goal')
                f.write(f"{metta_clause}\n\n")
                goal_clauses.append(metta_clause)

        f.write("\n")
        f.write(";; Ready for resolution!\n")
        f.write("! \"CNF loaded - tagged format for pattern matching\"\n")


def main():
    """Convert TPTP problem to MeTTa resolution format using E prover"""

    if len(sys.argv) < 2:
        print("Usage: python tptp_to_resolution_eprover.py <tptp_file> [output_metta]")
        print()
        print("Example:")
        print("  python tptp_to_resolution_eprover.py test_cases/knights_knaves.p")
        sys.exit(1)

    tptp_file = sys.argv[1]

    # Determine output file
    if len(sys.argv) >= 3:
        output_file = sys.argv[2]
    else:
        # Auto-generate output filename
        base = os.path.splitext(os.path.basename(tptp_file))[0]
        output_file = f"test_cases/{base}_eprover_resolution.metta"

    print(f"Converting {tptp_file} to MeTTa resolution format...")
    print("Using E Prover for CNF conversion (TRUSTED)...")

    # Use E prover for CNF
    cnf_clauses = eprover_cnf(tptp_file)

    print(f"✅ E Prover generated {len(cnf_clauses)} CNF clauses")

    # Generate MeTTa file
    generate_metta_resolution_file(cnf_clauses, output_file)

    print(f"✅ Written to: {output_file}")
    print()
    print("To run:")
    print(f"  conda activate hyperon")
    print(f"  metta {output_file}")


if __name__ == '__main__':
    main()
