#!/usr/bin/env python3
"""
Select 42 TPTP FOF problems with verified status annotations

Extracts problems from TPTP archive and selects based on:
- Official status (Theorem, CounterSatisfiable, Satisfiable, Unsatisfiable)
- Problem size (prefer smaller/simpler)
- Domain diversity
"""

import os
import re
import subprocess
from pathlib import Path
from collections import defaultdict


def extract_tptp_problems(archive_path, target_dir):
    """Extract FOF problems from TPTP archive"""
    print("Extracting TPTP FOF problems...")

    # Get list of FOF problems (+N naming convention)
    result = subprocess.run(
        ["tar", "-tzf", archive_path],
        capture_output=True,
        text=True
    )

    # Filter for FOF problems (avoid THF ^N and TFF _N)
    fof_problems = []
    for line in result.stdout.splitlines():
        if '/Problems/' in line and line.endswith('.p'):
            # FOF uses +N naming (e.g., PUZ001+1.p)
            if re.search(r'\+\d+\.p$', line):
                fof_problems.append(line)

    print(f"Found {len(fof_problems)} FOF problems")

    # Extract a representative sample for analysis
    sample_size = min(200, len(fof_problems))
    problems_to_extract = fof_problems[:sample_size]

    for problem in problems_to_extract:
        subprocess.run(
            ["tar", "-xzf", archive_path, problem],
            cwd=str(target_dir.parent),
            capture_output=True
        )

    return problems_to_extract


def parse_problem_metadata(problem_path):
    """Extract metadata from TPTP problem file"""
    with open(problem_path, 'r') as f:
        content = f.read()

    metadata = {
        'path': problem_path,
        'name': Path(problem_path).name,
        'status': None,
        'domain': None,
        'spc': None,
        'size': len(content),
        'num_fof': content.count('fof('),
        'num_cnf': content.count('cnf('),
    }

    # Extract status
    status_match = re.search(r'% Status\s*:\s*(\w+)', content)
    if status_match:
        metadata['status'] = status_match.group(1)

    # Extract domain
    domain_match = re.search(r'% Domain\s*:\s*([^\n]+)', content)
    if domain_match:
        metadata['domain'] = domain_match.group(1).strip()

    # Extract SPC
    spc_match = re.search(r'% SPC\s*:\s*(\S+)', content)
    if spc_match:
        metadata['spc'] = spc_match.group(1)

    return metadata


def select_benchmark_problems(problems_metadata, target_count=42):
    """Select diverse set of problems"""

    # Group by status
    by_status = defaultdict(list)
    for meta in problems_metadata:
        if meta['status']:
            by_status[meta['status']].append(meta)

    print(f"\nProblems by status:")
    for status, probs in sorted(by_status.items()):
        print(f"  {status}: {len(probs)}")

    # Target distribution (aiming for balance)
    target_dist = {
        'Theorem': 21,           # Provable (UNSAT of Ax ∧ ¬Conj)
        'CounterSatisfiable': 10, # Non-theorems with countermodel
        'Satisfiable': 7,        # Satisfiable problem sets
        'Unsatisfiable': 4,      # Pure UNSAT (no conjecture)
    }

    selected = []

    for status, target in target_dist.items():
        candidates = by_status.get(status, [])

        if not candidates:
            print(f"  Warning: No {status} problems found")
            continue

        # Sort by size (prefer smaller/simpler)
        candidates.sort(key=lambda x: (x['num_fof'] + x['num_cnf'], x['size']))

        # Take the target number
        take = min(target, len(candidates))
        selected.extend(candidates[:take])

        print(f"  Selected {take} {status} problems")

    return selected


def create_benchmark_suite(selected_problems, output_dir):
    """Copy selected problems to benchmark directory"""
    output_dir.mkdir(exist_ok=True)

    # Create index
    index_lines = []
    index_lines.append("# TPTP FOF Benchmark (42 Problems) - From Official TPTP Library\n")
    index_lines.append(f"\n**Total:** {len(selected_problems)} problems\n")
    index_lines.append("\n## Problems by Status\n")

    by_status = defaultdict(list)
    for meta in selected_problems:
        by_status[meta['status']].append(meta)

    counter = 1

    for status in ['Theorem', 'CounterSatisfiable', 'Satisfiable', 'Unsatisfiable']:
        if status not in by_status:
            continue

        index_lines.append(f"\n### {status} ({len(by_status[status])} problems)\n")

        for meta in by_status[status]:
            # Copy file with new sequential name
            new_name = f"tptp_{counter:03d}_{status.lower()}.p"
            new_path = output_dir / new_name

            # Copy from TPTP extraction
            src_path = Path(meta['path'])
            if src_path.exists():
                subprocess.run(['cp', str(src_path), str(new_path)])

                index_lines.append(
                    f"{counter}. **{new_name}** - {meta['name']} "
                    f"(Domain: {meta['domain']}, {meta['num_fof']} FOF formulas)\n"
                )

                counter += 1

    # Write index
    with open(output_dir / "INDEX.md", 'w') as f:
        f.writelines(index_lines)

    print(f"\n✅ Created benchmark in {output_dir}")
    print(f"   {len(selected_problems)} problems selected")


def main():
    """Main benchmark selection process"""

    tptp_dir = Path("/home/zar/claude/hyperon/TPTP")
    archive = tptp_dir / "TPTP-v9.2.1.tgz"
    extract_dir = tptp_dir / "TPTP-v9.2.1"
    output_dir = Path("/home/zar/claude/mizar-rs/metta-tools/tptp_fol_benchmark_42_official")

    if not archive.exists():
        print(f"Error: TPTP archive not found at {archive}")
        return

    # Extract problems
    extracted_problems = extract_tptp_problems(archive, extract_dir)

    # Parse metadata
    print("\nParsing problem metadata...")
    problems_metadata = []
    for prob_path in extracted_problems:
        full_path = tptp_dir / prob_path
        if full_path.exists():
            meta = parse_problem_metadata(full_path)
            if meta['status']:  # Only include if status is known
                problems_metadata.append(meta)

    print(f"Parsed {len(problems_metadata)} problems with status annotations")

    # Select benchmark
    selected = select_benchmark_problems(problems_metadata, target_count=42)

    # Create benchmark suite
    create_benchmark_suite(selected, output_dir)

    print(f"\n🎉 Benchmark selection complete!")
    print(f"   Output: {output_dir}")


if __name__ == '__main__':
    main()
