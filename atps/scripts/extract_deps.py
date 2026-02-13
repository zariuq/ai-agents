#!/usr/bin/env python3
"""
Extract proof dependencies from TSTP proof objects.

Usage: python3 extract_deps.py <proofs_dir> > deps.jsonl
"""

import sys
import re
import json
from pathlib import Path
from collections import defaultdict


def parse_tstp_proof(proof_file):
    """Extract premises used in a TSTP proof."""
    with open(proof_file) as f:
        content = f.read()

    # Check if proof was found
    if "SZS status Theorem" not in content:
        return None

    # Extract all fof/cnf statements with their sources
    used_premises = set()
    all_premises = set()

    # Pattern 1: Direct file references (these are original problem premises)
    # fof(name, role, formula, file('problem.p', name))
    for match in re.finditer(r"fof\((\w+),\s*(\w+),.*?file\(['\"].*?['\"]\s*,\s*(\w+)\)", content, re.DOTALL):
        premise_name = match.group(1)
        role = match.group(2)
        file_name = match.group(3)

        # Skip generated clauses (usually start with i_, c_, or similar)
        if not premise_name.startswith(('i_', 'c_', 'esk', 'sK')):
            all_premises.add(premise_name)

    # Pattern 2: Track which premises appear in inference steps
    # Look for inference() clauses that reference premises
    for match in re.finditer(r"inference\([^,]+,\s*\[[^\]]*\],\s*\[(.*?)\]\)", content, re.DOTALL):
        premise_refs = match.group(1)
        # Extract premise names from the reference list
        for prem in re.findall(r"(\w+)", premise_refs):
            if not prem.startswith(('i_', 'c_', 'esk', 'sK', 'theory', 'inference')):
                if prem in all_premises:
                    used_premises.add(prem)

    # Alternative: Look at the proof derivation directly
    # Count any premise that appears in a cnf() derived clause
    for match in re.finditer(r"cnf\(.*?inference.*?\[(.*?)\]", content, re.DOTALL):
        refs = match.group(1)
        for prem in re.findall(r"(\w+)", refs):
            if prem in all_premises:
                used_premises.add(prem)

    # If we didn't find used premises via inference, try the proof object
    if not used_premises:
        # Some proofs list used axioms differently
        # Look for any premise that appears in CNF clauses
        for match in re.finditer(r"cnf\((\w+)", content):
            clause_name = match.group(1)
            if clause_name in all_premises:
                used_premises.add(clause_name)

    return {
        'all_premises': sorted(all_premises),
        'used_premises': sorted(used_premises)
    }


def extract_problem_info(problem_file):
    """Extract basic info from original problem file."""
    if not problem_file.exists():
        return {}

    with open(problem_file) as f:
        content = f.read()

    # Find conjecture
    conjecture_match = re.search(r"fof\((\w+),\s*conjecture,", content)
    conjecture = conjecture_match.group(1) if conjecture_match else None

    # Count premises in original problem
    premises = []
    for match in re.finditer(r"fof\((\w+),\s*axiom,", content):
        premises.append(match.group(1))

    return {
        'conjecture': conjecture,
        'total_premises': len(premises),
        'premise_names': premises
    }


def main():
    if len(sys.argv) != 2:
        print("Usage: python3 extract_deps.py <proofs_dir>", file=sys.stderr)
        sys.exit(1)

    proofs_dir = Path(sys.argv[1])

    if not proofs_dir.exists():
        print(f"Error: Directory {proofs_dir} not found", file=sys.stderr)
        sys.exit(1)

    # Process all .out files
    proven_count = 0
    failed_count = 0

    for proof_file in sorted(proofs_dir.glob("*.out")):
        deps = parse_tstp_proof(proof_file)

        if deps is None:
            # Proof not found
            failed_count += 1
            continue

        proven_count += 1

        # Extract problem name (remove .p.out suffix)
        problem_name = proof_file.stem
        if problem_name.endswith('.p'):
            problem_name = problem_name[:-2]

        # Try to get original problem info
        problem_file = proofs_dir.parent / "test_subset" / f"{problem_name}.p"
        problem_info = extract_problem_info(problem_file)

        # Output JSON line
        result = {
            'problem': problem_name,
            'status': 'proven',
            'used_premises': deps['used_premises'],
            'available_premises': deps['all_premises'],
            'num_used': len(deps['used_premises']),
            'num_available': len(deps['all_premises']),
        }

        if problem_info:
            result['conjecture'] = problem_info.get('conjecture')
            result['original_premises'] = problem_info.get('total_premises', 0)

        print(json.dumps(result))

    # Print summary to stderr
    print(f"\n=== Dependency Extraction Summary ===", file=sys.stderr)
    print(f"Proven problems: {proven_count}", file=sys.stderr)
    print(f"Failed problems: {failed_count}", file=sys.stderr)
    print(f"Total processed: {proven_count + failed_count}", file=sys.stderr)


if __name__ == "__main__":
    main()
