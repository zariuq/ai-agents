#!/usr/bin/env python3
"""
Optimized PLN-native kNN-prior + NB-likelihood premise selector.

Python only does data retrieval / serialization:
  - Find top-K neighbors by shared feature count
  - Write raw features (goal + neighbor) to TSV
  - Optionally write NB evidence to a Prolog facts file (.pl)

PeTTa does ALL reasoning in batched invocations:
  - Feature overlap via Prolog atomspace (goal_feat_db ∩ nbr_feat_db)
  - Similarity evidence from feature overlap (PLN)
  - kNN prior evidence accumulation via hplus (PLN Revision)
  - Global prior + kNN prior composition
  - NB likelihood fold (prior removed)
  - Posterior composition from prior + likelihood in log-domain
  - Multiple problems handled in one process via jobs TSV

Usage:
  python3 scripts/select_pln_knn_prior_nb_opt.py --top-k 256 --merge-nb --output sel.json
  python3 scripts/select_pln_knn_prior_nb_opt.py --smoke-test --merge-nb --output /dev/null
"""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
import re
import resource
import shutil
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

DATASET_DIR = Path("/home/zar/claude/atps/datasets/extended_mptp5k")
CHAINY_TRAIN_DIR = DATASET_DIR / "chainy" / "train"
CHAINY_VAL_DIR = DATASET_DIR / "chainy" / "val"
FEATURES_TRAIN_DIR = DATASET_DIR / "features_chainy"
FEATURES_VAL_DIR = DATASET_DIR / "features_chainy_val"
DEPS_FILE = DATASET_DIR / "deps" / "bushy_train_deps.jsonl"
TEMP_ROOT = DATASET_DIR / "pln_eval_temp"

PETTA_DIR = Path("/home/zar/claude/hyperon/PeTTa")
PETTA_RUN = PETTA_DIR / "run.sh"
COMBINED_SELECTOR = "demos/pln_knn_prior_nb_selector_opt.metta"

RESULT_RE = re.compile(
    r"^\(Result\s+([^\s\)]+)\s+([^\s\)]+)\s+[^\s\)]+\s+\(stv\s+([-+0-9.eE]+)\s+([-+0-9.eE]+)\)\)\s*$"
)
AXIOM_ROLES = {"axiom", "hypothesis", "definition"}
CONJ_ROLES = {"conjecture", "negated_conjecture"}


def _fmt(x):
    return f"{float(x):.10g}"


def _pl_atom(x):
    """Encode a Python value as a quoted Prolog atom."""
    s = str(x).replace("'", "''")
    return f"'{s}'"


# -- Training data -------------------------------------------------------------

def load_training_data(deps_file=DEPS_FILE):
    """Load proved training problems: conjecture features + used axioms."""
    deps_by_name = {}
    with open(deps_file) as f:
        for line in f:
            rec = json.loads(line)
            pname = rec["problem_name"]
            used = rec.get("used_axioms", [])
            if used:
                deps_by_name.setdefault(pname, set()).update(
                    normalize_axiom_name(a) for a in used
                )

    training = []
    for pname, used_set in deps_by_name.items():
        vec_file = FEATURES_TRAIN_DIR / f"{pname}.vec"
        prob_file = CHAINY_TRAIN_DIR / pname
        if not vec_file.exists() or not prob_file.exists():
            continue

        formulas = read_problem_formulas(prob_file)
        with open(vec_file) as vf:
            vec_lines = [line for line in vf if line.strip()]

        aligned = min(len(formulas), len(vec_lines))
        gamma_features = None
        for idx in range(aligned):
            _, role = formulas[idx]
            if role in CONJ_ROLES:
                gamma_features = parse_sparse_line(vec_lines[idx])
                break

        if gamma_features is not None and len(gamma_features) > 0:
            training.append({
                "problem": pname,
                "gamma_features": gamma_features,
                "used_axioms": used_set,
            })

    return training


# -- Data retrieval (NOT reasoning) -------------------------------------------

def find_top_k_neighbors(goal_features, training_data, k=16):
    """Find K training problems with most shared features. Data retrieval only."""
    overlaps = []
    for entry in training_data:
        shared = len(goal_features & entry["gamma_features"])
        if shared > 0:
            overlaps.append((shared, entry))
    overlaps.sort(key=lambda x: -x[0])
    return [(e["problem"], e["gamma_features"], e["used_axioms"])
            for _, e in overlaps[:k]]


# -- Combined TSV writer (ONE file for everything) ----------------------------

def write_nb_prolog(path, axioms, goal_features, nb_state, args):
    """Write NB evidence as Prolog facts for fast consult loading."""
    sfreq, tfreq, idf, extended_features, _ = nb_state
    goal_set = set(goal_features)

    with open(path, "w") as f:
        for phi in axioms:
            t_phi = float(tfreq.get(phi, 0.0))
            if t_phi <= 0.0:
                continue

            f.write(
                f"nb_prior_db({_pl_atom(phi)}, {_fmt(t_phi)}, {_fmt(args.nb_def_prior_weight)}).\n"
            )

            s_phi = sfreq.get(phi, {})
            f_bar_phi = extended_features.get(phi) if extended_features else None
            f_bar = set(f_bar_phi) if f_bar_phi is not None else set(s_phi.keys())

            for feat in goal_set & f_bar:
                sf = float(s_phi.get(feat, 0.0))
                if sf <= 0.0:
                    sf = 0.5
                neg = max(t_phi - sf, 0.5)
                idf_w = float(idf.get(feat, 1.0))
                f.write(
                    f"nb_feat_db({_pl_atom(phi)}, {_pl_atom(feat)}, {_fmt(sf)}, {_fmt(neg)}, {_fmt(idf_w)}).\n"
                )

            for feat in goal_set - f_bar:
                idf_w = float(idf.get(feat, 1.0))
                f.write(
                    f"nb_feat_db({_pl_atom(phi)}, {_pl_atom(feat)}, {_fmt(0.5)}, {_fmt(max(t_phi, 0.5))}, {_fmt(idf_w)}).\n"
                )


def build_combined_tsv(pname, candidate_axioms, goal_features,
                       neighbors, nb_state, args, work_dir):
    """Write ONE TSV with kNN features + params + queries (+ optional NB .pl path)."""
    data_path = work_dir / f"combined_{pname}_data.tsv"
    query_path = work_dir / f"combined_{pname}_q.tsv"
    nb_pl_path = None

    goal_list = sorted(goal_features)
    goal_csv = ",".join(str(f) for f in goal_list)

    if args.merge_nb and nb_state is not None:
        nb_pl_path = work_dir / f"nb_{pname}.pl"
        write_nb_prolog(nb_pl_path, candidate_axioms, goal_list, nb_state, args)

    with open(data_path, "w") as df:
        # Parameters
        df.write(f"param\tkappa\t{_fmt(args.kappa)}\n")
        df.write(f"param\tglobal_weight\t{_fmt(args.global_weight)}\n")
        df.write(f"param\tsim_kappa\t{_fmt(args.sim_kappa)}\n")
        df.write(f"param\tneg_weight\t{_fmt(args.neg_weight)}\n")
        df.write(f"param\ttau_power\t{_fmt(args.tau_power)}\n")
        df.write(f"param\tdeps_factor\t{_fmt(args.deps_factor)}\n")
        df.write(f"param\tgate_kappa\t{_fmt(args.gate_kappa)}\n")
        df.write(f"param\tused_confidence\t{_fmt(args.used_confidence)}\n")

        if args.merge_nb:
            df.write(f"param\tnb_global_weight\t{_fmt(args.nb_global_weight)}\n")
            df.write(f"param\tnb_confidence_kappa\t{_fmt(args.nb_confidence_kappa)}\n")
            df.write(f"param\tpost_confidence_kappa\t{_fmt(args.post_confidence_kappa)}\n")
            if nb_pl_path is not None:
                df.write(f"param\tnb_pl_file\t{nb_pl_path}\n")

        # Goal features → Prolog atomspace
        for f in goal_list:
            df.write(f"goal_feat\t{f}\n")

        # Neighbor features → Prolog atomspace
        for nbr_name, nbr_feats, used_set in neighbors:
            for f in sorted(nbr_feats):
                df.write(f"nbr_feat\t{nbr_name}\t{f}\n")
            # Which axioms this neighbor used (among candidates)
            for phi in candidate_axioms:
                if phi in used_set:
                    df.write(f"nbr_used\t{nbr_name}\t{phi}\n")

        # NB evidence is written to a separate .pl file and loaded via consult.

    # Queries (include goal features for NB scoring)
    qid_to_axiom = {}
    with open(query_path, "w") as qf:
        for i, phi in enumerate(candidate_axioms):
            qid = f"q{i}"
            qid_to_axiom[qid] = phi
            if args.merge_nb:
                qf.write(f"query\t{qid}\t{phi}\t{goal_csv}\n")
            else:
                qf.write(f"query\t{qid}\t{phi}\n")

    return data_path, query_path, qid_to_axiom, nb_pl_path


# -- PeTTa interface (ONE call) -----------------------------------------------

def _limit_mem():
    resource.setrlimit(resource.RLIMIT_AS, (6 * 1024**3, 6 * 1024**3))


def run_petta_batch_jobs(job_rows, timeout_sec, jobs_path, selector_path):
    """Run one PeTTa process over a batch of jobs."""
    jobs_path.parent.mkdir(parents=True, exist_ok=True)
    with open(jobs_path, "w") as jf:
        for row in job_rows:
            jf.write(f"job\t{row['job_id']}\t{row['data_path']}\t{row['query_path']}\n")

    cmd = ["nice", "-n", "19", "bash", str(PETTA_RUN), selector_path,
           str(jobs_path), "--silent"]
    result = subprocess.run(
        cmd, cwd=str(PETTA_DIR),
        capture_output=True, text=True, timeout=timeout_sec,
        preexec_fn=_limit_mem,
    )
    if result.returncode != 0:
        stderr_snip = (result.stderr or "").strip()[:300]
        raise RuntimeError(f"PeTTa exit {result.returncode}: {stderr_snip}")

    stv_by_job_qid = {}
    for line in (result.stdout or "").splitlines():
        m = RESULT_RE.match(line.strip())
        if m:
            stv_by_job_qid[(m.group(1), m.group(2))] = (float(m.group(3)), float(m.group(4)))
    return stv_by_job_qid


def prepare_problem_job(pname, candidate_axioms, goal_features,
                        training_data, nb_state, args, run_temp_root):
    """Prepare one problem's serialized payload for batch scoring."""
    work_dir = run_temp_root / pname
    work_dir.mkdir(parents=True, exist_ok=True)

    # Data retrieval: find neighbors by shared feature count
    neighbors = find_top_k_neighbors(goal_features, training_data, k=args.knn_k)

    # Write ONE combined TSV
    data_path, query_path, qid_to_axiom, nb_pl_path = build_combined_tsv(
        pname, candidate_axioms, goal_features,
        neighbors, nb_state, args, work_dir,
    )

    axiom_to_qid = {axiom: qid for qid, axiom in qid_to_axiom.items()}
    return {
        "job_id": pname,
        "problem": pname,
        "candidate_axioms": candidate_axioms,
        "data_path": data_path,
        "query_path": query_path,
        "nb_pl_path": nb_pl_path,
        "axiom_to_qid": axiom_to_qid,
    }


def score_job_result(job, stv_by_job_qid):
    scored = []
    job_id = job["job_id"]
    for phi in job["candidate_axioms"]:
        qid = job["axiom_to_qid"].get(phi)
        if qid is None:
            scored.append((phi, -1e30))
            continue
        stv = stv_by_job_qid.get((job_id, qid))
        if stv is None:
            scored.append((phi, -1e30))
        else:
            scored.append((phi, stv[0]))
    scored.sort(key=lambda x: -x[1])
    return scored


def cleanup_job_files(job):
    job["data_path"].unlink(missing_ok=True)
    job["query_path"].unlink(missing_ok=True)
    if job["nb_pl_path"] is not None:
        job["nb_pl_path"].unlink(missing_ok=True)


def load_problem(pname, problems_dir, features_dir):
    """Load conjecture features and axiom map for one problem."""
    pfile = problems_dir / pname
    vec_file = features_dir / f"{pname}.vec"
    if not pfile.exists() or not vec_file.exists():
        return None, None

    formulas = read_problem_formulas(pfile)
    with open(vec_file) as vf:
        vec_lines = [line for line in vf if line.strip()]

    aligned = min(len(formulas), len(vec_lines))
    if aligned == 0:
        return None, None

    gamma_features = None
    axiom_map = {}

    for idx in range(aligned):
        fname, role = formulas[idx]
        if role in CONJ_ROLES:
            gamma_features = parse_sparse_line(vec_lines[idx])
        elif role in AXIOM_ROLES:
            norm = normalize_axiom_name(fname)
            if norm not in axiom_map:
                axiom_map[norm] = fname

    return gamma_features, axiom_map


def batched(seq, batch_size):
    size = max(1, int(batch_size))
    for i in range(0, len(seq), size):
        yield seq[i:i + size]


def main():
    parser = argparse.ArgumentParser(
        description="Optimized PLN kNN-prior + NB-likelihood selector (batched PeTTa)")
    parser.add_argument("--top-k", type=int, default=256)
    parser.add_argument("--split", choices=["train", "val"], default="val")
    parser.add_argument("--max-problems", type=int, default=None)
    parser.add_argument("--output", required=True, help="Output selections JSON")
    parser.add_argument("--nb-tables", type=str, default=None,
                        help="Optional path to MaSh NB tables pickle")
    parser.add_argument("--deps-file", type=str, default=str(DEPS_FILE),
                        help="Dependencies JSONL for kNN prior training data")
    parser.add_argument("--knn-k", type=int, default=16,
                        help="Number of nearest neighbors (default 16)")
    parser.add_argument("--neg-weight", type=float, default=0.05)
    parser.add_argument("--tau-power", type=float, default=6.0,
                        help="MaSh-like similarity sharpening exponent")
    parser.add_argument("--deps-factor", type=float, default=2.7,
                        help="MaSh-like dependency emphasis for used-neighbor evidence")
    parser.add_argument("--gate-kappa", type=float, default=10.0,
                        help="Reliability gate scale: g = W / (W + gate_kappa)")
    parser.add_argument("--kappa", type=float, default=10.0)
    parser.add_argument("--global-weight", type=float, default=1.0)
    parser.add_argument("--sim-kappa", type=float, default=5.0)
    parser.add_argument("--used-confidence", type=float, default=0.95)
    parser.add_argument("--merge-nb", action="store_true",
                        help="Also compute PLN-NB and merge via PLN Revision")
    parser.add_argument("--nb-def-prior-weight", type=float, default=1000.0)
    parser.add_argument("--nb-global-weight", type=float, default=1.0)
    parser.add_argument("--nb-confidence-kappa", type=float, default=1000.0)
    parser.add_argument("--post-confidence-kappa", type=float, default=None,
                        help="Posterior confidence scale (defaults to nb-confidence-kappa)")
    parser.add_argument("--petta-selector", type=str, default=COMBINED_SELECTOR,
                        help="PeTTa selector script path relative to PeTTa root")
    parser.add_argument("--run-id", type=str, default=None,
                        help="Optional unique run id for temp namespace")
    parser.add_argument("--petta-batch-size", type=int, default=20,
                        help="Problems per PeTTa process (default 20)")
    parser.add_argument("--petta-job-batch-size", type=int, default=None,
                        help="Alias for --petta-batch-size")
    parser.add_argument("--petta-parallel-batches", type=int, default=1,
                        help="Concurrent PeTTa batch invocations (default 1)")
    parser.add_argument("--petta-timeout", type=int, default=240)
    parser.add_argument("--batch-metrics-out", type=str, default=None,
                        help="Optional JSON path for per-batch timing metrics")
    parser.add_argument("--keep-tsv", action="store_true")
    parser.add_argument("--smoke-test", action="store_true",
                        help="Only process first 20 problems")
    parser.add_argument("--problems", nargs="*")
    args = parser.parse_args()

    if args.petta_job_batch_size is not None:
        args.petta_batch_size = args.petta_job_batch_size

    if args.smoke_test and args.max_problems is None:
        args.max_problems = 20

    if args.post_confidence_kappa is None:
        args.post_confidence_kappa = args.nb_confidence_kappa

    if args.split == "train":
        problems_dir = CHAINY_TRAIN_DIR
        features_dir = FEATURES_TRAIN_DIR
    else:
        problems_dir = CHAINY_VAL_DIR
        features_dir = FEATURES_VAL_DIR

    run_id = args.run_id or f"{int(time.time())}_{os.getpid()}"
    run_temp_root = TEMP_ROOT / f"pln_knn_opt_{run_id}"
    run_temp_root.mkdir(parents=True, exist_ok=True)

    print("Loading training data (features + deps)...", flush=True)
    training_data = load_training_data(args.deps_file)
    print(f"  {len(training_data)} proved training problems with features")

    nb_state = None
    if args.merge_nb:
        print("Loading MaSh NB tables for merge...", flush=True)
        nb_state = load_nb_tables(args.nb_tables)
        print(f"  {len(nb_state[1])} axioms in NB tables")

    if args.problems:
        val_problems = sorted(args.problems)
    else:
        val_problems = sorted(p.name for p in problems_dir.iterdir() if p.is_file())
    if args.max_problems:
        val_problems = val_problems[:args.max_problems]

    mode = "PLN-kNNPrior+NBLikelihood-opt" if args.merge_nb else "PLN-kNNPrior-only-opt"
    print(f"Mode: {mode}, split: {args.split}, problems: {len(val_problems)}, top-k: {args.top_k}, "
          f"knn_k: {args.knn_k}, kappa: {args.kappa}, sim_kappa: {args.sim_kappa}, "
          f"petta_batch_size: {args.petta_batch_size}, run_id: {run_id}")

    selections = {}
    jobs = []
    job_to_axiom_map = {}
    prep_durations = []
    batch_metrics = []
    no_features = 0
    failures = 0
    t0 = time.time()

    for i, pname in enumerate(val_problems):
        if i == 0 or (i + 1) % 5 == 0:
            elapsed = time.time() - t0
            print(f"  {i+1}/{len(val_problems)} ({elapsed:.0f}s, failures: {failures})",
                  flush=True)

        gamma_features, axiom_map = load_problem(pname, problems_dir, features_dir)
        if gamma_features is None or not axiom_map:
            no_features += 1
            selections[pname] = []
            continue

        candidates = list(axiom_map.keys())
        job_to_axiom_map[pname] = axiom_map

        try:
            prep_start = time.time()
            job = prepare_problem_job(
                pname, candidates, gamma_features,
                training_data, nb_state, args, run_temp_root,
            )
            jobs.append(job)
            prep_durations.append(time.time() - prep_start)
        except Exception as exc:
            failures += 1
            print(f"  WARN {pname}: {exc}", flush=True)
            selections[pname] = []

    prep_elapsed = time.time() - t0
    if prep_durations:
        avg_ms = 1000.0 * (sum(prep_durations) / len(prep_durations))
    else:
        avg_ms = 0.0
    print(f"  Preparation: jobs={len(jobs)} elapsed={prep_elapsed:.2f}s "
          f"avg={avg_ms:.1f}ms/job", flush=True)

    batches = list(batched(jobs, args.petta_batch_size))

    def run_batch(bidx: int, batch):
        jobs_path = run_temp_root / f"jobs_batch_{bidx:05d}.tsv"
        batch_t0 = time.time()
        batch_failed = False
        try:
            petta_t0 = time.time()
            stv_by_job_qid = run_petta_batch_jobs(
                batch, args.petta_timeout, jobs_path, args.petta_selector
            )
            petta_elapsed = time.time() - petta_t0
        except Exception as exc:
            stv_by_job_qid = {}
            batch_failed = True
            petta_elapsed = time.time() - batch_t0
            return {
                "batch_index": bidx,
                "batch": batch,
                "jobs_path": jobs_path,
                "failed": batch_failed,
                "error": str(exc),
                "stv_by_job_qid": stv_by_job_qid,
                "petta_seconds": petta_elapsed,
                "batch_seconds": time.time() - batch_t0,
            }
        return {
            "batch_index": bidx,
            "batch": batch,
            "jobs_path": jobs_path,
            "failed": batch_failed,
            "error": None,
            "stv_by_job_qid": stv_by_job_qid,
            "petta_seconds": petta_elapsed,
            "batch_seconds": time.time() - batch_t0,
        }

    def consume_batch_result(res):
        nonlocal failures
        bidx = res["batch_index"]
        batch = res["batch"]
        jobs_path = res["jobs_path"]
        batch_failed = res["failed"]
        stv_by_job_qid = res["stv_by_job_qid"]
        petta_elapsed = res["petta_seconds"]
        batch_elapsed = res["batch_seconds"]
        if batch_failed:
            failures += len(batch)
            print(f"  WARN batch {bidx+1}: {res['error']}", flush=True)

        post_t0 = time.time()
        for job in batch:
            pname = job["problem"]
            if pname in selections:
                continue
            if batch_failed:
                selections[pname] = []
            else:
                axiom_map = job_to_axiom_map[pname]
                scored = score_job_result(job, stv_by_job_qid)
                selections[pname] = [axiom_map[norm] for norm, _ in scored[:args.top_k]
                                     if norm in axiom_map]
            if not args.keep_tsv:
                cleanup_job_files(job)
        if not args.keep_tsv:
            jobs_path.unlink(missing_ok=True)

        post_elapsed = time.time() - post_t0
        jobs_scored = 0 if batch_failed else len(batch)
        results_returned = len(stv_by_job_qid)
        throughput = 0.0 if batch_elapsed <= 0 else (len(batch) / batch_elapsed)
        batch_metric = {
            "batch_index": bidx + 1,
            "batch_size": len(batch),
            "failed": batch_failed,
            "petta_seconds": petta_elapsed,
            "post_seconds": post_elapsed,
            "batch_seconds": batch_elapsed,
            "jobs_scored": jobs_scored,
            "results_returned": results_returned,
            "jobs_per_second": throughput,
        }
        batch_metrics.append(batch_metric)
        print(
            f"    batch {bidx+1}/{len(batches)} "
            f"batch_time={batch_elapsed:.2f}s "
            f"petta={petta_elapsed:.2f}s post={post_elapsed:.2f}s "
            f"results={results_returned} throughput={throughput:.2f} jobs/s",
            flush=True,
        )

    workers = max(1, int(args.petta_parallel_batches))
    if workers <= 1 or len(batches) <= 1:
        for bidx, batch in enumerate(batches):
            elapsed = time.time() - t0
            print(f"  Batch {bidx+1}/{len(batches)} size={len(batch)} ({elapsed:.0f}s)",
                  flush=True)
            res = run_batch(bidx, batch)
            consume_batch_result(res)
    else:
        print(f"  Running PeTTa batches in parallel: workers={workers}", flush=True)
        with ThreadPoolExecutor(max_workers=workers) as pool:
            future_to_idx = {
                pool.submit(run_batch, bidx, batch): bidx
                for bidx, batch in enumerate(batches)
            }
            done = 0
            for fut in as_completed(future_to_idx):
                done += 1
                bidx = future_to_idx[fut]
                elapsed = time.time() - t0
                print(f"  Batch done {done}/{len(batches)} (batch {bidx+1}, {elapsed:.0f}s)",
                      flush=True)
                res = fut.result()
                consume_batch_result(res)

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(selections, f)

    if not args.keep_tsv:
        shutil.rmtree(run_temp_root, ignore_errors=True)

    elapsed = time.time() - t0
    n_sel = sum(1 for v in selections.values() if v)
    print(f"\nDone in {elapsed:.0f}s. Selections: {n_sel}/{len(val_problems)}, "
          f"no_features: {no_features}, failures: {failures}")
    print(f"Saved: {out_path}")

    if args.batch_metrics_out:
        metrics_path = Path(args.batch_metrics_out)
        metrics_path.parent.mkdir(parents=True, exist_ok=True)
        batch_metrics.sort(key=lambda m: m["batch_index"])
        summary = {
            "mode": mode,
            "run_id": run_id,
            "problems": len(val_problems),
            "jobs": len(jobs),
            "petta_batch_size": args.petta_batch_size,
            "elapsed_seconds": elapsed,
            "prep_seconds": prep_elapsed,
            "avg_prep_ms_per_job": avg_ms,
            "failures": failures,
            "batch_metrics": batch_metrics,
        }
        with open(metrics_path, "w") as f:
            json.dump(summary, f, indent=2)
        print(f"Saved batch metrics: {metrics_path}")


if __name__ == "__main__":
    main()
