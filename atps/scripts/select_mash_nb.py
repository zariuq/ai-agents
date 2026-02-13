#!/usr/bin/env python3
"""
MaSh NB premise selection (selection only, no E prover).

Scores all candidate axioms for each validation problem using MaSh sparse NB,
selects top-k, and writes a selections JSON.

Usage:
  python3 scripts/select_mash_nb.py --top-k 256 --output selections.json

Output format:
  { "problem_name": ["axiom1", "axiom2", ...], ... }
"""

import argparse
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from mash_nb_scorer import (
    load_tables,
    normalize_axiom_name,
    parse_sparse_line,
    read_problem_formulas,
    score_all_axioms,
)

DATASET_DIR = Path("/home/zar/claude/atps/datasets/extended_mptp5k")
CHAINY_TRAIN_DIR = DATASET_DIR / "chainy" / "train"
CHAINY_VAL_DIR = DATASET_DIR / "chainy" / "val"
FEATURES_TRAIN_DIR = DATASET_DIR / "features_chainy"
FEATURES_VAL_DIR = DATASET_DIR / "features_chainy_val"


def load_problem_features(problem_name, problem_file, features_dir):
    """Load conjecture features and normalized axiom map from one problem."""
    vec_file = features_dir / f"{problem_name}.vec"
    if not vec_file.exists():
        return None, None

    formulas = read_problem_formulas(problem_file)
    with open(vec_file) as vf:
        vec_lines = [line for line in vf if line.strip()]

    aligned = min(len(formulas), len(vec_lines))
    if aligned == 0:
        return None, None

    gamma_features = None
    axiom_map = {}

    for idx in range(aligned):
        fname, role = formulas[idx]
        if role in {"conjecture", "negated_conjecture"}:
            gamma_features = parse_sparse_line(vec_lines[idx])
        elif role in {"axiom", "hypothesis", "definition"}:
            norm = normalize_axiom_name(fname)
            if norm not in axiom_map:
                axiom_map[norm] = (fname, parse_sparse_line(vec_lines[idx]))

    return gamma_features, axiom_map


def main():
    parser = argparse.ArgumentParser(description="MaSh NB premise selection")
    parser.add_argument("--top-k", type=int, default=256)
    parser.add_argument("--split", choices=["train", "val"], default="val")
    parser.add_argument("--max-problems", type=int, default=None)
    parser.add_argument("--tables", type=str, default=None,
                        help="Optional path to MaSh NB tables pickle")
    parser.add_argument("--output", required=True, help="Output selections JSON")
    args = parser.parse_args()

    sfreq, tfreq, idf, extended_features, sigma = load_tables(args.tables)
    print(f"Loaded MaSh NB tables: {len(tfreq)} axioms, {len(idf)} features")

    if args.split == "train":
        problems_dir = CHAINY_TRAIN_DIR
        features_dir = FEATURES_TRAIN_DIR
    else:
        problems_dir = CHAINY_VAL_DIR
        features_dir = FEATURES_VAL_DIR

    problems = sorted(p.name for p in problems_dir.iterdir() if p.is_file())
    if args.max_problems:
        problems = problems[: args.max_problems]
    print(f"Split: {args.split}, problems: {len(problems)}, top-k: {args.top_k}")

    selections = {}
    no_features = 0
    t0 = time.time()

    for i, pname in enumerate(problems):
        if i == 0 or (i + 1) % 100 == 0:
            print(f"  {i+1}/{len(problems)} ({time.time()-t0:.0f}s)", flush=True)

        pfile = problems_dir / pname
        gamma_features, axiom_map = load_problem_features(pname, pfile, features_dir)
        if gamma_features is None or not axiom_map:
            no_features += 1
            selections[pname] = []
            continue

        scored = score_all_axioms(
            list(axiom_map.keys()),
            gamma_features,
            sfreq, tfreq, idf,
            extended_features=extended_features,
            **sigma,
        )
        # Map normalized names back to original names
        selections[pname] = [axiom_map[norm][0] for norm, _ in scored[: args.top_k]]

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(selections, f)

    elapsed = time.time() - t0
    print(f"Done in {elapsed:.0f}s. Skipped (no features): {no_features}")
    print(f"Saved: {out_path}")


if __name__ == "__main__":
    main()
