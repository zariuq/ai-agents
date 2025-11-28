#!/usr/bin/env python3
"""Generate CNF versions of FOF test problems using E prover"""

import subprocess
from pathlib import Path

test_dir = Path('test_cases')
fof_files = test_dir.glob('*_fof.p')

for fof_file in sorted(fof_files):
    base_name = fof_file.stem.replace('_fof', '')
    cnf_file = test_dir / f"{base_name}_cnf.p"

    print(f"Generating {cnf_file.name} from {fof_file.name}...")

    # Run E prover to generate CNF
    result = subprocess.run(
        ['eprover', '--cnf', str(fof_file)],
        capture_output=True,
        text=True
    )

    # Extract CNF clauses
    cnf_lines = [line for line in result.stdout.split('\n') if line.startswith('cnf(')]

    if cnf_lines:
        with open(cnf_file, 'w') as f:
            for line in cnf_lines:
                f.write(line + '\n')
        print(f"  ✅ Generated {len(cnf_lines)} clauses")
    else:
        print(f"  ❌ No CNF generated")

print("\nDone!")
