#!/usr/bin/env python3
"""
Run E prover on problems, saving .out files.

Two modes:
  1. Full problems (no selection):
     python3 scripts/run_eprover.py --problems-dir DIR --output-dir DIR

  2. With premise selection:
     python3 scripts/run_eprover.py --problems-dir DIR --selections FILE --output-dir DIR

The selections file is a JSON: { "problem_name": ["axiom1", ...], ... }
When provided, a filtered problem (containing only selected axioms) is created
in a temp directory and passed to E.

Output: one .out file per problem in --output-dir.
"""

import argparse
import json
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

EPROVER = "/home/zar/claude/atps/eprover-standard/PROVER/eprover"
FORMULA_RE = re.compile(r"^(fof|cnf)\(([^,]+),\s*([^,]+),")


def run_one(problem_file, timeout, out_file):
    """Run E prover on one problem, save output to out_file."""
    try:
        result = subprocess.run(
            [
                "nice", "-n", "19",
                EPROVER,
                "--free-numbers",
                "--auto-schedule",
                f"--cpu-limit={timeout}",
                str(problem_file),
            ],
            capture_output=True,
            text=True,
            timeout=timeout + 10,
        )
        with open(out_file, "w") as f:
            f.write(result.stdout)
            if result.stderr:
                f.write(result.stderr)
        proved = "Proof found" in result.stdout or "SZS status Theorem" in result.stdout
        return proved
    except subprocess.TimeoutExpired:
        Path(out_file).write_text("% Timeout\n")
        return False
    except Exception as exc:
        Path(out_file).write_text(f"% Error: {exc}\n")
        return False


def create_filtered_problem(problem_file, selected_axioms, output_file):
    """Create problem with only selected axioms (plus conjecture etc.)."""
    selected = set(selected_axioms)
    out_lines = []
    with open(problem_file) as f:
        for line in f:
            stripped = line.strip()
            if not stripped or stripped.startswith("%"):
                out_lines.append(line)
                continue
            m = FORMULA_RE.match(stripped)
            if not m:
                out_lines.append(line)
                continue
            role = m.group(3).strip()
            if role in {"axiom", "hypothesis", "definition"}:
                name = m.group(2).strip()
                if name in selected:
                    out_lines.append(line)
            else:
                out_lines.append(line)
    with open(output_file, "w") as f:
        f.writelines(out_lines)


def main():
    parser = argparse.ArgumentParser(description="Run E prover, save .out files")
    parser.add_argument("--problems-dir", required=True, help="Directory with .p problem files")
    parser.add_argument("--output-dir", required=True, help="Directory for .out files")
    parser.add_argument("--selections", default=None, help="Selections JSON (filtered mode)")
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--max-problems", type=int, default=None)
    parser.add_argument("--save-results", default=None,
                        help="Save result JSON (timeout appended to name if not present)")
    args = parser.parse_args()

    problems_dir = Path(args.problems_dir)
    output_dir = Path(args.output_dir)

    if output_dir.exists() and any(output_dir.glob("*.out")):
        print(f"ERROR: {output_dir} already contains .out files. Use a fresh directory.", file=sys.stderr)
        sys.exit(1)

    output_dir.mkdir(parents=True, exist_ok=True)

    selections = None
    if args.selections:
        with open(args.selections) as f:
            selections = json.load(f)
        print(f"Loaded selections for {len(selections)} problems")

    problems = sorted(p.name for p in problems_dir.iterdir() if p.is_file())
    if args.max_problems:
        problems = problems[: args.max_problems]

    print(f"Running E on {len(problems)} problems, timeout={args.timeout}s")
    if selections:
        print(f"Mode: filtered (premise selection)")
    else:
        print(f"Mode: full (all axioms)")

    solved = 0
    total = 0
    t0 = time.time()

    with tempfile.TemporaryDirectory() as tmpdir:
        for i, pname in enumerate(problems):
            if i == 0 or (i + 1) % 50 == 0:
                elapsed = time.time() - t0
                print(f"  {i+1}/{len(problems)} (solved: {solved}, {elapsed:.0f}s)", flush=True)

            pfile = problems_dir / pname
            out_file = output_dir / f"{pname}.out"
            total += 1

            if selections is not None:
                if pname not in selections or not selections[pname]:
                    Path(out_file).write_text("% No selections for this problem\n")
                    continue
                filtered = Path(tmpdir) / pname
                create_filtered_problem(pfile, selections[pname], filtered)
                pfile = filtered

            if run_one(pfile, args.timeout, out_file):
                solved += 1

    elapsed = time.time() - t0
    print(f"\nDone: {solved}/{total} solved in {elapsed:.0f}s ({100*solved/total:.1f}%)")
    print(f"Output: {output_dir}")

    # Save result JSON with timeout in metadata
    if args.save_results:
        result_path = Path(args.save_results)
        # Ensure timeout is in the filename
        if f"_{args.timeout}s" not in result_path.stem:
            result_path = result_path.with_stem(f"{result_path.stem}_{args.timeout}s")
        solved_list = []
        for pname in problems:
            out_file = output_dir / f"{pname}.out"
            if out_file.exists():
                txt = out_file.read_text()
                if "Proof found" in txt or "SZS status Theorem" in txt:
                    solved_list.append(pname)
        result = {
            "solved": len(solved_list),
            "total": total,
            "timeout": args.timeout,
            "rate": round(len(solved_list) / max(total, 1), 4),
            "problems_solved": solved_list,
        }
        result_path.parent.mkdir(parents=True, exist_ok=True)
        with open(result_path, "w") as f:
            json.dump(result, f)
        print(f"Results: {result_path}")


if __name__ == "__main__":
    main()
