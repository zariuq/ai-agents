#!/usr/bin/env python3
"""
PLN Normal premise selector (continuous carrier over PLN-NB observations).

Pipeline per problem:
1) Compute PLN-NB STVs in PeTTa (`demos/pln_idf_nb_selector.metta`).
2) Convert each NB STV to Normal observation:
     x = logit(strength), n = c/(1-c)
3) Run continuous selector in PeTTa (`demos/pln_normal_nb_selector.metta`).
4) Rank by resulting STV strength and select top-k.

This keeps NB scoring in PLN (PeTTa) and uses the Normal carrier as
context-dependent interpretation over sufficient statistics.
"""

import argparse
import json
import math
import re
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from mash_nb_scorer import (
    load_tables as load_nb_tables,
    normalize_axiom_name,
    parse_sparse_line,
    read_problem_formulas,
)
from pln_phase_batching import run_petta_jobs

DATASET_DIR = Path("/home/zar/claude/atps/datasets/extended_mptp5k")
CHAINY_VAL_DIR = DATASET_DIR / "chainy" / "val"
FEATURES_VAL_DIR = DATASET_DIR / "features_chainy_val"
TEMP_ROOT = DATASET_DIR / "pln_eval_temp"

PETTA_DIR = Path("/home/zar/claude/hyperon/PeTTa")
PETTA_RUN = PETTA_DIR / "run.sh"
NB_SELECTOR = "demos/pln_idf_nb_selector_jobs.metta"
NORMAL_SELECTOR = "demos/pln_normal_nb_selector_jobs.metta"

RESULT_RE = re.compile(
    r"^\(Result\s+([^\s\)]+)\s+[^\s\)]+\s+\(stv\s+([-+0-9.eE]+)\s+([-+0-9.eE]+)\)\)\s*$"
)


def _fmt(x):
    return f"{float(x):.10g}"


def load_val_problem_features(problem_name, problem_file):
    """Load conjecture features and normalized axiom map from one val problem."""
    vec_file = FEATURES_VAL_DIR / f"{problem_name}.vec"
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


def run_petta(selector, data_path, query_path, timeout_sec):
    """Run a PeTTa selector and parse (Result qid axiom (stv s c)) lines."""
    cmd = ["bash", str(PETTA_RUN), selector, str(data_path), str(query_path), "--silent"]
    result = subprocess.run(
        cmd,
        cwd=str(PETTA_DIR),
        capture_output=True,
        text=True,
        timeout=timeout_sec,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"PeTTa exit {result.returncode}: {(result.stderr or '').strip()[:220]}"
        )

    stv_by_qid = {}
    for line in (result.stdout or "").splitlines():
        m = RESULT_RE.match(line.strip())
        if m:
            stv_by_qid[m.group(1)] = (float(m.group(2)), float(m.group(3)))
    return stv_by_qid


def build_nb_batch_files(
    pname,
    batch_idx,
    batch_axioms,
    goal_features,
    sfreq,
    tfreq,
    idf,
    extended_features,
    nb_def_prior_weight,
    nb_global_weight,
    nb_confidence_kappa,
    work_dir,
):
    """Create evidence/query TSV for one batch of PLN-NB scoring in PeTTa."""
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
            f_bar_phi = extended_features.get(phi) if extended_features is not None else None
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
                ef.write(
                    f"feat\t{phi}\t{f}\t{_fmt(0.5)}\t{_fmt(max(t_phi, 0.5))}\t{_fmt(idf_w)}\n"
                )

            qid = f"n{batch_idx}_{i}"
            qid_to_axiom[qid] = phi
            qf.write(f"{qid}\t{phi}\t{goal_csv}\n")

    return evidence_path, query_path, qid_to_axiom, skipped


def compute_pln_nb_stvs(candidate_axioms, goal_features, nb_state, args, work_dir, pname):
    """Compute NB STVs via the PeTTa PLN-NB selector (all-PLN path)."""
    sfreq, tfreq, idf, extended_features, _sigma = nb_state

    if not candidate_axioms:
        return {}

    batch_size = args.nb_batch_size or len(candidate_axioms) or 1
    stvs = {}
    batch_tasks = []

    for bstart in range(0, len(candidate_axioms), batch_size):
        batch_idx = bstart // batch_size
        batch = candidate_axioms[bstart:bstart + batch_size]
        ev, q, qmap, skipped = build_nb_batch_files(
            pname,
            batch_idx,
            batch,
            goal_features,
            sfreq,
            tfreq,
            idf,
            extended_features,
            args.nb_def_prior_weight,
            args.nb_global_weight,
            args.nb_confidence_kappa,
            work_dir,
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
        selector=NB_SELECTOR,
        petta_dir=PETTA_DIR,
        petta_run=PETTA_RUN,
        job_rows=job_rows,
        jobs_dir=work_dir / "_jobs",
        timeout_sec=args.petta_timeout,
        batch_size=args.petta_job_batch_size,
        batch_prefix=f"{pname}_nb",
        keep_jobs_tsv=args.keep_tsv,
    )

    for task in batch_tasks:
        if task["qmap"]:
            for qid, axiom in task["qmap"].items():
                key = (task["job_id"], qid)
                if key in stv_by_job_qid:
                    stvs[axiom] = stv_by_job_qid[key]
        for axiom in task["skipped"]:
            stvs.setdefault(axiom, (0.5, 0.0))

    if not args.keep_tsv:
        for task in batch_tasks:
            task["ev"].unlink(missing_ok=True)
            task["q"].unlink(missing_ok=True)

    return stvs


def nb_stv_to_normal_obs(stv, args):
    """Map NB STV to continuous observation (x, n) for Normal carrier."""
    s, c = stv
    eps = max(1e-12, float(args.normal_prob_eps))
    s = min(1.0 - eps, max(eps, float(s)))
    logit = math.log(s / (1.0 - s))
    logit = max(-args.normal_logit_clip, min(args.normal_logit_clip, logit))

    c = min(0.9999, max(0.0, float(c)))
    weight = c / (1.0 - c) if c < 0.9999 else args.normal_n_cap
    n = max(args.normal_min_n, min(args.normal_n_cap, weight))
    n = n * args.normal_n_scale
    return logit, max(1e-6, n)


def build_normal_batch_files(pname, batch_idx, batch_axioms, nb_stvs, args, work_dir):
    """Create TSV files for one PeTTa continuous scoring batch."""
    data_path = work_dir / f"normal_{pname}_b{batch_idx}_data.tsv"
    query_path = work_dir / f"normal_{pname}_b{batch_idx}_q.tsv"

    qid_to_axiom = {}
    with open(data_path, "w") as df, open(query_path, "w") as qf:
        df.write(f"param\tmu0\t{_fmt(args.normal_mu0)}\n")
        df.write(f"param\ttau0_sq\t{_fmt(args.normal_tau0_sq)}\n")
        df.write(f"param\tsigma_sq\t{_fmt(args.normal_sigma_sq)}\n")
        df.write(f"param\tkappa\t{_fmt(args.normal_kappa)}\n")
        df.write(f"param\tglobal_weight\t{_fmt(args.normal_global_weight)}\n")

        for i, phi in enumerate(batch_axioms):
            x, n = nb_stv_to_normal_obs(nb_stvs.get(phi, (0.5, 0.0)), args)
            df.write(f"obs\t{phi}\t{_fmt(x)}\t{_fmt(n)}\n")
            qid = f"q{batch_idx}_{i}"
            qid_to_axiom[qid] = phi
            qf.write(f"{qid}\t{phi}\n")

    return data_path, query_path, qid_to_axiom


def score_one_problem(pname, candidate_axioms, goal_features, nb_state, args):
    """Score all candidates for one problem via PLN-NB -> PLN-Normal."""
    work_dir = TEMP_ROOT / "pln_normal" / pname
    work_dir.mkdir(parents=True, exist_ok=True)

    nb_stvs = compute_pln_nb_stvs(
        candidate_axioms, goal_features, nb_state, args, work_dir, pname
    )

    normal_candidates = list(candidate_axioms)
    if args.prefilter_k > 0 and len(normal_candidates) > args.prefilter_k:
        ranked = sorted(
            normal_candidates,
            key=lambda ax: nb_stvs.get(ax, (0.5, 0.0))[0],
            reverse=True,
        )
        normal_candidates = ranked[:args.prefilter_k]

    batch_size = args.petta_batch_size or len(normal_candidates) or 1
    scored_map = {}
    batch_tasks = []

    for bstart in range(0, len(normal_candidates), batch_size):
        batch_idx = bstart // batch_size
        batch = normal_candidates[bstart:bstart + batch_size]
        data_path, query_path, qid_to_axiom = build_normal_batch_files(
            pname, batch_idx, batch, nb_stvs, args, work_dir
        )
        batch_tasks.append(
            {
                "job_id": f"{pname}_norm_{batch_idx}",
                "data": data_path,
                "query": query_path,
                "qmap": qid_to_axiom,
            }
        )

    job_rows = [
        {"job_id": t["job_id"], "data_path": t["data"], "query_path": t["query"]}
        for t in batch_tasks
    ]
    stv_by_job_qid, _metrics = run_petta_jobs(
        selector=NORMAL_SELECTOR,
        petta_dir=PETTA_DIR,
        petta_run=PETTA_RUN,
        job_rows=job_rows,
        jobs_dir=work_dir / "_jobs",
        timeout_sec=args.petta_timeout,
        batch_size=args.petta_job_batch_size,
        batch_prefix=f"{pname}_normal",
        keep_jobs_tsv=args.keep_tsv,
    )

    for task in batch_tasks:
        for qid, phi in task["qmap"].items():
            key = (task["job_id"], qid)
            if key in stv_by_job_qid:
                s, _c = stv_by_job_qid[key]
                scored_map[phi] = s
            else:
                scored_map[phi] = -1e30

    if not args.keep_tsv:
        for t in batch_tasks:
            t["data"].unlink(missing_ok=True)
            t["query"].unlink(missing_ok=True)

    for phi in candidate_axioms:
        scored_map.setdefault(phi, -1e30)

    return sorted(scored_map.items(), key=lambda x: -x[1])


def main():
    parser = argparse.ArgumentParser(
        description="PLN Normal premise selection via PLN-NB observations + PeTTa Normal carrier"
    )
    parser.add_argument("--top-k", type=int, default=256)
    parser.add_argument("--max-problems", type=int, default=None)
    parser.add_argument("--output", required=True, help="Output selections JSON")
    parser.add_argument(
        "--prefilter-k",
        type=int,
        default=0,
        help="If >0, keep top prefilter-k by PLN-NB strength before Normal stage",
    )

    parser.add_argument("--petta-batch-size", type=int, default=32)
    parser.add_argument("--petta-job-batch-size", type=int, default=20)
    parser.add_argument("--petta-timeout", type=int, default=240)

    parser.add_argument("--nb-batch-size", type=int, default=32)
    parser.add_argument("--nb-def-prior-weight", type=float, default=1000.0)
    parser.add_argument("--nb-global-weight", type=float, default=1.0)
    parser.add_argument("--nb-confidence-kappa", type=float, default=1000.0)

    parser.add_argument("--normal-mu0", type=float, default=0.0)
    parser.add_argument("--normal-tau0-sq", type=float, default=1.0)
    parser.add_argument("--normal-sigma-sq", type=float, default=1.0)
    parser.add_argument("--normal-kappa", type=float, default=1000.0)
    parser.add_argument("--normal-global-weight", type=float, default=1.0)
    parser.add_argument("--normal-prob-eps", type=float, default=1e-6)
    parser.add_argument("--normal-logit-clip", type=float, default=8.0)
    parser.add_argument("--normal-min-n", type=float, default=1e-3)
    parser.add_argument("--normal-n-cap", type=float, default=200.0)
    parser.add_argument("--normal-n-scale", type=float, default=1.0)

    parser.add_argument("--keep-tsv", action="store_true")
    parser.add_argument("--problems", nargs="*", help="Specific problem names to process")
    args = parser.parse_args()

    if not PETTA_RUN.exists():
        raise FileNotFoundError(f"PeTTa runner not found: {PETTA_RUN}")

    nb_state = load_nb_tables()
    print(f"Loaded tables: {len(nb_state[1])} axioms, {len(nb_state[2])} features")

    if args.problems:
        val_problems = sorted(args.problems)
    else:
        val_problems = sorted(p.name for p in CHAINY_VAL_DIR.iterdir() if p.is_file())
    if args.max_problems:
        val_problems = val_problems[:args.max_problems]
    print(f"Problems: {len(val_problems)}, top-k: {args.top_k}")

    selections = {}
    no_features = 0
    failures = 0
    t0 = time.time()

    for i, pname in enumerate(val_problems):
        if i == 0 or (i + 1) % 10 == 0:
            print(f"  {i+1}/{len(val_problems)} ({time.time()-t0:.0f}s, failures: {failures})",
                  flush=True)

        pfile = CHAINY_VAL_DIR / pname
        gamma_features, axiom_map = load_val_problem_features(pname, pfile)
        if gamma_features is None or not axiom_map:
            no_features += 1
            selections[pname] = []
            continue

        candidates = list(axiom_map.keys())
        goal_features = set(gamma_features)

        try:
            scored = score_one_problem(pname, candidates, goal_features, nb_state, args)
            selections[pname] = [axiom_map[norm][0] for norm, _ in scored[:args.top_k]
                                 if norm in axiom_map]
        except Exception as exc:
            failures += 1
            print(f"  WARN {pname}: {exc}", flush=True)
            selections[pname] = []

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(selections, f)

    elapsed = time.time() - t0
    print(f"Done in {elapsed:.0f}s. No features: {no_features}, failures: {failures}")
    print(f"Saved: {out_path}")


if __name__ == "__main__":
    main()
