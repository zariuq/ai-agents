#!/usr/bin/env python3
"""
Extract dependencies from Extended MPTP 5k bushy training proofs.

Parses E prover proof outputs (run with -p flag) to find which axioms
were actually used in each proof via file() annotations.

E prover -p output format:
  fof(axiom_name, axiom, ..., file('path', axiom_name)).
  fof(conjecture_name, conjecture, ..., file('path', conjecture_name)).

We extract axiom_name from lines with 'axiom' role that have file() refs.
"""

import re
import json
import sys
from pathlib import Path

# Defaults (bushy training)
DEFAULT_PROOFS_DIR = "/home/zar/claude/atps/datasets/extended_mptp5k/baselines/bushy_train"
DEFAULT_PROBLEMS_DIR = "/home/zar/claude/atps/datasets/extended_mptp5k/bushy/train"
DEFAULT_OUTPUT_FILE = "/home/zar/claude/atps/datasets/extended_mptp5k/deps/bushy_train_deps.jsonl"

# Match: file('...', axiom_name)
FILE_REF_RE = re.compile(r"file\('[^']*',\s*(\w+)\)")
# Match: fof(name, role, ...) or cnf(name, role, ...)
FORMULA_RE = re.compile(r"^(fof|cnf)\(([^,]+),\s*([^,]+),")


def extract_proof_axioms(proof_output):
    """
    Extract axiom names used in proof from E prover -p output.

    Joins multi-line fof/cnf formulas before parsing, since E may wrap
    long formulas across multiple lines.
    """
    used = set()
    # Join multi-line formulas: collect non-comment lines, then split on
    # formula boundaries (fof( or cnf( at start of line)
    lines = []
    for line in proof_output.split("\n"):
        stripped = line.strip()
        if stripped.startswith("%") or not stripped:
            continue
        lines.append(stripped)

    # Rejoin into single string and split on formula starts
    text = " ".join(lines)
    # Split before each fof( or cnf( that starts a formula
    formulas = re.split(r'(?=(?:fof|cnf)\()', text)

    for formula in formulas:
        formula = formula.strip()
        if not formula:
            continue
        file_match = FILE_REF_RE.search(formula)
        if not file_match:
            continue
        axiom_name = file_match.group(1)
        formula_match = FORMULA_RE.match(formula)
        if formula_match:
            role = formula_match.group(3).strip()
            if role in ("axiom", "hypothesis", "definition"):
                used.add(axiom_name)
    return used


def extract_available_axioms(problem_file):
    """Extract all axioms available in the problem file."""
    axioms = set()
    with open(problem_file) as f:
        for line in f:
            m = FORMULA_RE.match(line.strip())
            if m:
                role = m.group(3).strip()
                if role in ("axiom", "hypothesis", "definition"):
                    axioms.add(m.group(2).strip())
    return axioms


def main():
    if len(sys.argv) == 4:
        PROOFS_DIR = Path(sys.argv[1])
        PROBLEMS_DIR = Path(sys.argv[2])
        OUTPUT_FILE = Path(sys.argv[3])
    elif len(sys.argv) == 1:
        PROOFS_DIR = Path(DEFAULT_PROOFS_DIR)
        PROBLEMS_DIR = Path(DEFAULT_PROBLEMS_DIR)
        OUTPUT_FILE = Path(DEFAULT_OUTPUT_FILE)
    else:
        print("Usage: extract_deps_extended_mptp.py [PROOFS_DIR PROBLEMS_DIR OUTPUT_FILE]")
        sys.exit(1)

    print("Extracting dependencies from training proofs...")
    print(f"  Proofs dir: {PROOFS_DIR}")
    print(f"  Problems dir: {PROBLEMS_DIR}")

    OUTPUT_FILE.parent.mkdir(parents=True, exist_ok=True)

    proved_count = 0
    deps_extracted = 0
    fallback_count = 0

    with open(OUTPUT_FILE, "w") as out_f:
        for proof_file in sorted(PROOFS_DIR.glob("*.out")):
            with open(proof_file) as f:
                proof_output = f.read()

            proved = ("Proof found" in proof_output or
                      "SZS status Theorem" in proof_output)

            if not proved:
                continue

            proved_count += 1
            problem_name = proof_file.stem

            # Find matching problem file
            problem_file = PROBLEMS_DIR / problem_name
            if not problem_file.exists():
                # Try without .out suffix variations
                candidates = list(PROBLEMS_DIR.glob(f"*{problem_name}*"))
                if not candidates:
                    print(f"  WARN: No problem file for {problem_name}")
                    continue
                problem_file = candidates[0]

            used_axioms = extract_proof_axioms(proof_output)
            available_axioms = extract_available_axioms(problem_file)

            if not used_axioms:
                # This should NOT happen with -p flag. Flag it clearly.
                fallback_count += 1
                print(f"  ERROR: No file() annotations found for {problem_name}!")
                print(f"    Was E run with -p flag?")
                continue  # Do NOT fall back to all axioms

            dep_info = {
                "problem": f"train/{problem_name}",
                "problem_name": problem_name,
                "proved": True,
                "used_axioms": sorted(list(used_axioms)),
                "available_axioms": sorted(list(available_axioms)),
                "num_used": len(used_axioms),
                "num_available": len(available_axioms),
            }

            out_f.write(json.dumps(dep_info) + "\n")
            deps_extracted += 1

            if deps_extracted % 200 == 0:
                print(f"  Processed {deps_extracted} proofs...", flush=True)

    print(f"\nExtracted dependencies from {deps_extracted} proofs")
    print(f"  Total proved: {proved_count}")
    if fallback_count > 0:
        print(f"  WARNING: {fallback_count} proofs had no file() annotations!")
    print(f"  Output: {OUTPUT_FILE}")

    # Stats
    if deps_extracted > 0:
        with open(OUTPUT_FILE) as f:
            deps = [json.loads(line) for line in f]

        avg_used = sum(d["num_used"] for d in deps) / len(deps)
        avg_available = sum(d["num_available"] for d in deps) / len(deps)

        print(f"\nStatistics:")
        print(f"  Avg axioms used: {avg_used:.1f}")
        print(f"  Avg axioms available: {avg_available:.1f}")
        print(f"  Usage ratio: {100*avg_used/avg_available:.1f}%")

        # Sanity check: used should be << available
        if avg_used == avg_available:
            print(f"  ERROR: used == available! Extraction likely broken.")
        elif avg_used / avg_available > 0.5:
            print(f"  WARN: Usage ratio >50% — unusually high, check data.")
        else:
            print(f"  OK: Usage ratio looks reasonable.")


if __name__ == "__main__":
    main()
