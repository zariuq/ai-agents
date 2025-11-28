#!/usr/bin/env python3
"""
Build 42-problem TPTP FOF benchmark with official status annotations
"""

import os
import subprocess
from pathlib import Path
import re

# Known good problems from TPTP
PROBLEM_LIST = [
    # Easy Theorem problems
    "TPTP-v9.2.1/Problems/PUZ/PUZ001+1.p",  # Dreadbury Mansion
    "TPTP-v9.2.1/Problems/SYN/SYN046+1.p",  # Pelletier 15
    "TPTP-v9.2.1/Problems/SYN/SYN047+1.p",  # Pelletier 16
    "TPTP-v9.2.1/Problems/SYN/SYN048+1.p",  # Pelletier 17
    "TPTP-v9.2.1/Problems/SYN/SYN049+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN050+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN051+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN052+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN053+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN054+1.p",

    # Medium Theorem problems
    "TPTP-v9.2.1/Problems/PUZ/PUZ031+1.p",  # Schubert's Steamroller
    "TPTP-v9.2.1/Problems/PUZ/PUZ047+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN055+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN056+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN057+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN058+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN059+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN060+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN061+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN062+1.p",

    # Hard Theorem problems
    "TPTP-v9.2.1/Problems/SYN/SYN063+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN064+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN065+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN066+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN067+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN068+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN069+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN070+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN071+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN072+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN073+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN074+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN075+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN076+1.p",

    # CounterSatisfiable/Satisfiable/Unsatisfiable
    # These will be identified by status annotation
    "TPTP-v9.2.1/Problems/SYN/SYN315+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN316+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN317+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN318+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN319+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN320+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN321+1.p",
    "TPTP-v9.2.1/Problems/SYN/SYN322+1.p",
]

def extract_problem(archive_path, problem_path, extract_dir):
    """Extract single problem from archive"""
    subprocess.run(
        ["tar", "-xzf", str(archive_path), problem_path],
        cwd=str(extract_dir.parent),
        capture_output=True
    )
    return extract_dir / problem_path

def parse_status(problem_file):
    """Extract status from TPTP problem"""
    with open(problem_file, 'r') as f:
        content = f.read()

    match = re.search(r'%\s*Status\s*:\s*(\w+)', content)
    if match:
        return match.group(1)
    return None

def main():
    """Build benchmark from TPTP archive"""
    tptp_dir = Path("/home/zar/claude/hyperon/TPTP")
    archive = tptp_dir / "TPTP-v9.2.1.tgz"
    extract_dir = tptp_dir
    output_dir = Path("/home/zar/claude/mizar-rs/metta-tools/tptp_fol_benchmark_42_official")

    output_dir.mkdir(exist_ok=True)

    print(f"Extracting {len(PROBLEM_LIST)} problems from TPTP archive...")

    problems_by_status = {
        'Theorem': [],
        'CounterSatisfiable': [],
        'Satisfiable': [],
        'Unsatisfiable': []
    }

    for prob_path in PROBLEM_LIST:
        print(f"  Extracting {Path(prob_path).name}...", end=" ")

        # Extract
        full_path = extract_problem(archive, prob_path, extract_dir)

        if not full_path.exists():
            print("FAILED")
            continue

        # Parse status
        status = parse_status(full_path)
        print(f"Status: {status}")

        if status in problems_by_status:
            problems_by_status[status].append((Path(prob_path).name, full_path))

    # Report
    print("\n" + "="*60)
    print("Problems by status:")
    for status, probs in problems_by_status.items():
        print(f"  {status}: {len(probs)}")

    # Copy to output directory with sequential naming
    print("\n" + "="*60)
    print("Creating benchmark suite...")

    counter = 1
    index_lines = []
    index_lines.append("# TPTP FOF Benchmark (42 Problems) - From Official TPTP\n\n")

    for status in ['Theorem', 'CounterSatisfiable', 'Satisfiable', 'Unsatisfiable']:
        if not problems_by_status[status]:
            continue

        index_lines.append(f"\n## {status} ({len(problems_by_status[status])} problems)\n\n")

        for orig_name, orig_path in problems_by_status[status]:
            new_name = f"tptp_{counter:03d}_{status.lower()}.p"
            new_path = output_dir / new_name

            subprocess.run(['cp', str(orig_path), str(new_path)])

            index_lines.append(f"{counter}. **{new_name}** (original: {orig_name})\\n")
            counter += 1

    # Write index
    with open(output_dir / "INDEX.md", 'w') as f:
        f.writelines(index_lines)

    print(f"\n✅ Benchmark created in {output_dir}")
    print(f"   Total problems: {counter - 1}")
    print(f"\nNext steps:")
    print(f"  1. cd {output_dir}")
    print(f"  2. Run E prover verification")
    print(f"  3. Convert to MeTTa format")

if __name__ == '__main__':
    main()
