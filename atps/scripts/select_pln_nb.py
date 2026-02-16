#!/usr/bin/env python3
"""
PLN IDF-weighted Naive Bayes premise selection (selection only, no E prover).

Uses PeTTa to execute PLN evidence-tensor + evidence-power inference for scoring.
This is genuine PLN: evidence-power implements Knuth-Skilling regraduation,
evidence-tensor implements sequential composition (independence assumption).

Python prepares TSV inputs (with IDF column), invokes PeTTa, parses STVs, selects top-k.

Usage:
  python3 scripts/select_pln_nb.py --top-k 256 --output selections.json

Output format:
  { "problem_name": ["axiom1", "axiom2", ...], ... }
"""

import argparse
import json
import os
import sys
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR))
sys.path.insert(0, str(SCRIPT_DIR / "_private"))
from mash_nb_scorer import (
    load_tables as load_nb_tables,
    normalize_axiom_name,
    parse_sparse_line,
    read_problem_formulas,
    score_all_axioms as score_mash_nb_all,
)
from pln_phase_batching import run_petta_jobs

DATASET_DIR = Path("/home/zar/claude/atps/datasets/extended_mptp5k")
CHAINY_TRAIN_DIR = DATASET_DIR / "chainy" / "train"
CHAINY_VAL_DIR = DATASET_DIR / "chainy" / "val"
FEATURES_TRAIN_DIR = DATASET_DIR / "features_chainy"
FEATURES_VAL_DIR = DATASET_DIR / "features_chainy_val"
TEMP_ROOT = DATASET_DIR / "pln_eval_temp"

PETTA_DIR = Path("/home/zar/claude/hyperon/PeTTa")
PETTA_RUN = PETTA_DIR / "run.sh"
PETTA_SELECTOR = "demos/pln_idf_nb_selector_jobs.metta"


def _fmt(x):
    return f"{float(x):.10g}"


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


def prefilter_with_mash_nb(candidates, gamma_features, nb_state, prefilter_k):
    """Use MaSh NB to reduce candidate set before PLN scoring."""
    if len(candidates) <= prefilter_k:
        return candidates
    sfreq, tfreq, idf, extended_features, sigma = nb_state
    scored = score_mash_nb_all(
        candidates, gamma_features, sfreq, tfreq, idf,
        extended_features=extended_features, **sigma,
    )
    return [ax for ax, _ in scored[:prefilter_k]]


def build_batch_files(pname, batch_idx, batch_axioms, goal_features,
                      sfreq, tfreq, idf, extended_features,
                      nb_def_prior_weight, nb_global_weight,
                      nb_confidence_kappa, work_dir):
    """Create evidence/query TSV files for one PeTTa IDF-NB scoring batch.

    Evidence format (6-column with IDF):
      prior<TAB>axiom<TAB>pos<TAB>neg
      feat<TAB>axiom<TAB>feature<TAB>pos<TAB>neg<TAB>idf_weight
    """
    goal_list = sorted(goal_features)
    goal_set = set(goal_list)
    goal_csv = ",".join(str(f) for f in goal_list)

    evidence_path = work_dir / f"nb_{pname}_b{batch_idx}_ev.tsv"
    query_path = work_dir / f"nb_{pname}_b{batch_idx}_q.tsv"

    qid_to_axiom = {}
    skipped = []

    with open(evidence_path, "w") as ef, open(query_path, "w") as qf:
        ef.write(f"param\tglobal_weight\t{_fmt(nb_global_weight)}\n")
        ef.write(f"param\tconfidence_kappa\t{_fmt(nb_confidence_kappa)}\n")

        for i, phi in enumerate(batch_axioms):
            t_phi = float(tfreq.get(phi, 0))
            if t_phi <= 0.0:
                skipped.append(phi)
                continue

            ef.write(f"prior\t{phi}\t{_fmt(t_phi)}\t{_fmt(nb_def_prior_weight)}\n")

            s_phi = sfreq.get(phi, {})
            f_bar_phi = extended_features.get(phi)
            f_bar = set(f_bar_phi) if f_bar_phi is not None else set(s_phi.keys())

            for f in goal_set & f_bar:
                sf = float(s_phi.get(f, 0))
                if sf <= 0.0:
                    sf = 0.5
                neg = max(t_phi - sf, 0.5)
                idf_w = float(idf.get(f, 1.0))
                ef.write(f"feat\t{phi}\t{f}\t{_fmt(sf)}\t{_fmt(neg)}\t{_fmt(idf_w)}\n")

            for f in goal_set - f_bar:
                idf_w = float(idf.get(f, 1.0))
                ef.write(f"feat\t{phi}\t{f}\t{_fmt(0.5)}\t{_fmt(max(t_phi, 0.5))}\t{_fmt(idf_w)}\n")

            qid = f"q{batch_idx}_{i}"
            qid_to_axiom[qid] = phi
            qf.write(f"{qid}\t{phi}\t{goal_csv}\n")

    return evidence_path, query_path, qid_to_axiom, skipped


def score_one_problem(pname, candidate_axioms, goal_features, sfreq, tfreq,
                      idf, extended_features, args):
    """Score all candidates for one problem via batched PeTTa calls."""
    work_dir = args.run_temp_root / pname
    work_dir.mkdir(parents=True, exist_ok=True)

    batch_size = args.petta_batch_size or len(candidate_axioms) or 1
    scored_map = {}
    batch_tasks = []

    for bstart in range(0, len(candidate_axioms), batch_size):
        batch_idx = bstart // batch_size
        batch = candidate_axioms[bstart:bstart + batch_size]
        ev, q, qmap, skipped = build_batch_files(
            pname, batch_idx, batch, goal_features,
            sfreq, tfreq, idf, extended_features,
            args.nb_def_prior_weight, args.nb_global_weight,
            args.nb_confidence_kappa, work_dir,
        )
        batch_tasks.append(
            {
                "job_id": f"{pname}_nb_{batch_idx}",
                "ev": ev,
                "q": q,
                "qmap": qmap,
                "skipped": skipped,
            }
        )

    job_rows = [
        {"job_id": t["job_id"], "data_path": t["ev"], "query_path": t["q"]}
        for t in batch_tasks
        if t["qmap"]
    ]
    stv_by_job_qid, _metrics = run_petta_jobs(
        selector=PETTA_SELECTOR,
        petta_dir=PETTA_DIR,
        petta_run=PETTA_RUN,
        job_rows=job_rows,
        jobs_dir=work_dir / "_jobs",
        timeout_sec=args.petta_timeout,
        batch_size=args.petta_job_batch_size,
        batch_prefix=f"{pname}_nb",
        keep_jobs_tsv=args.keep_tsv,
        parallel_batches=args.petta_parallel_batches,
    )

    for task in batch_tasks:
        if not task["qmap"]:
            continue
        for qid, phi in task["qmap"].items():
            key = (task["job_id"], qid)
            if key in stv_by_job_qid:
                s, _c = stv_by_job_qid[key]
                scored_map[phi] = s
            else:
                scored_map[phi] = -1e30

    if not args.keep_tsv:
        for t in batch_tasks:
            t["ev"].unlink(missing_ok=True)
            t["q"].unlink(missing_ok=True)

    for t in batch_tasks:
        for phi in t["skipped"]:
            scored_map[phi] = -1e30
    for phi in candidate_axioms:
        scored_map.setdefault(phi, -1e30)

    return sorted(scored_map.items(), key=lambda x: -x[1])


def main():
    parser = argparse.ArgumentParser(description="PLN IDF-NB premise selection via PeTTa")
    parser.add_argument("--top-k", type=int, default=256)
    parser.add_argument("--split", choices=["train", "val"], default="val")
    parser.add_argument("--max-problems", type=int, default=None)
    parser.add_argument("--nb-tables", type=str, default=None,
                        help="Optional path to MaSh NB tables pickle")
    parser.add_argument("--output", required=True, help="Output selections JSON")
    parser.add_argument("--prefilter-k", type=int, default=512,
                        help="MaSh NB prefilter to reduce candidates before PLN scoring")
    parser.add_argument("--petta-batch-size", type=int, default=32)
    parser.add_argument("--petta-job-batch-size", type=int, default=20)
    parser.add_argument("--petta-parallel-batches", type=int, default=1,
                        help="Number of concurrent PeTTa batch invocations (default 1)")
    parser.add_argument("--petta-timeout", type=int, default=240)
    parser.add_argument("--nb-def-prior-weight", type=float, default=1000.0)
    parser.add_argument("--nb-global-weight", type=float, default=1.0,
                        help="Global PLN evidence regraduation budget for IDF-NB")
    parser.add_argument("--nb-confidence-kappa", type=float, default=1000.0,
                        help="Confidence scale kappa for c=total/(total+kappa)")
    parser.add_argument("--keep-tsv", action="store_true")
    parser.add_argument("--problems", nargs="*",
                        help="Specific problem names to process (default: all)")
    parser.add_argument("--run-id", default=None,
                        help="Optional run id for temp dir isolation")
    args = parser.parse_args()

    run_id = args.run_id or f"{int(time.time())}_{os.getpid()}"
    args.run_temp_root = TEMP_ROOT / f"pln_nb_{run_id}"
    args.run_temp_root.mkdir(parents=True, exist_ok=True)

    if not PETTA_RUN.exists():
        raise FileNotFoundError(f"PeTTa runner not found: {PETTA_RUN}")

    sfreq, tfreq, idf, extended_features, sigma = load_nb_tables(args.nb_tables)
    nb_state = (sfreq, tfreq, idf, extended_features, sigma)
    print(f"Loaded tables: {len(tfreq)} axioms, {len(idf)} features")

    if args.split == "train":
        problems_dir = CHAINY_TRAIN_DIR
        features_dir = FEATURES_TRAIN_DIR
    else:
        problems_dir = CHAINY_VAL_DIR
        features_dir = FEATURES_VAL_DIR

    if args.problems:
        val_problems = sorted(args.problems)
    else:
        val_problems = sorted(p.name for p in problems_dir.iterdir() if p.is_file())
    if args.max_problems:
        val_problems = val_problems[:args.max_problems]
    print(f"Problems: {len(val_problems)}, top-k: {args.top_k}, run_id: {run_id}")

    selections = {}
    no_features = 0
    petta_failures = 0
    t0 = time.time()

    for i, pname in enumerate(val_problems):
        if i == 0 or (i + 1) % 25 == 0:
            print(f"  {i+1}/{len(val_problems)} ({time.time()-t0:.0f}s, failures: {petta_failures})",
                  flush=True)

        pfile = problems_dir / pname
        gamma_features, axiom_map = load_problem_features(pname, pfile, features_dir)
        if gamma_features is None or not axiom_map:
            no_features += 1
            selections[pname] = []
            continue

        candidates = list(axiom_map.keys())
        candidates = prefilter_with_mash_nb(candidates, gamma_features, nb_state, args.prefilter_k)
        goal_features = set(gamma_features)

        try:
            scored = score_one_problem(
                pname, candidates, goal_features,
                sfreq, tfreq, idf, extended_features, args,
            )
            selections[pname] = [axiom_map[norm][0] for norm, _ in scored[:args.top_k]
                                 if norm in axiom_map]
        except Exception as exc:
            petta_failures += 1
            print(f"  WARN {pname}: {exc}", flush=True)
            selections[pname] = []

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(selections, f)

    elapsed = time.time() - t0
    print(f"Done in {elapsed:.0f}s. No features: {no_features}, PeTTa failures: {petta_failures}")
    print(f"Saved: {out_path}")


if __name__ == "__main__":
    main()
