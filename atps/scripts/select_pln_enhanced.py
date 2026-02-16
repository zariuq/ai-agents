#!/usr/bin/env python3
"""
PLN Enhanced premise selection — two-phase with co-occurrence boost.

Phase 1: PLN IDF-NB scoring (existing pln_idf_nb_selector.metta)
Phase 2: Co-occurrence boost via PLN Deduction + Revision (pln_enhanced_selector.metta)

The key insight: if axiom A scored highly in phase 1, and A co-occurs with B
in training proofs, PLN Deduction propagates evidence from A to B.

Usage:
  python3 scripts/select_pln_enhanced.py --top-k 256 --output selections.json

Output format:
  { "problem_name": ["axiom1", "axiom2", ...], ... }
"""

import argparse
import json
import math
import os
import re
import subprocess
import sys
import time
from collections import Counter, defaultdict
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
DEPS_FILE = DATASET_DIR / "deps" / "bushy_train_deps.jsonl"
TEMP_ROOT = DATASET_DIR / "pln_eval_temp"

PETTA_DIR = Path("/home/zar/claude/hyperon/PeTTa")
PETTA_RUN = PETTA_DIR / "run.sh"
PHASE1_SELECTOR = "demos/pln_idf_nb_selector_jobs.metta"
PHASE2_SELECTOR = "demos/pln_enhanced_selector_jobs.metta"

RESULT_RE = re.compile(
    r"^\(Result\s+([^\s\)]+)\s+[^\s\)]+\s+\(stv\s+([-+0-9.eE]+)\s+([-+0-9.eE]+)\)\)\s*$"
)


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


def build_cooccurrence_table(deps_file, min_count=2):
    """Build axiom co-occurrence table from training proof dependencies.

    Returns dict: (axiom_a, axiom_b) → (pos, neg, idf_a, idf_b)
    where idf_x = ln(N / partners_count(x)) measures specificity.
    """
    cooc = Counter()
    axiom_total = Counter()
    partners = defaultdict(set)

    with open(deps_file) as f:
        for line in f:
            rec = json.loads(line)
            used = rec.get("used_axioms", [])
            if not used:
                continue
            normed = [normalize_axiom_name(a) for a in used]
            for a in normed:
                axiom_total[a] += 1
            for i, a in enumerate(normed):
                for b in normed[i+1:]:
                    pair = tuple(sorted([a, b]))
                    cooc[pair] += 1
                    partners[a].add(b)
                    partners[b].add(a)

    # Compute co-occurrence IDF: ln(N / partners_count)
    n_axioms = len(partners)
    cooc_idf = {}
    for a, ps in partners.items():
        cooc_idf[a] = math.log(max(n_axioms, 1) / max(len(ps), 1))

    # Filter to pairs with sufficient evidence
    filtered = {}
    for (a, b), count in cooc.items():
        if count >= min_count:
            neg_a = max(axiom_total[a] - count, 1)
            neg_b = max(axiom_total[b] - count, 1)
            neg = min(neg_a, neg_b)
            # Store IDF for both partners
            filtered[(a, b)] = (count, neg, cooc_idf.get(a, 1.0), cooc_idf.get(b, 1.0))

    return filtered


def build_phase1_files(pname, batch_idx, batch_axioms, goal_features,
                       sfreq, tfreq, idf, extended_features,
                       nb_def_prior_weight, nb_global_weight,
                       nb_confidence_kappa, work_dir):
    """Create evidence/query TSV files for phase 1 (IDF-NB scoring)."""
    goal_list = sorted(goal_features)
    goal_set = set(goal_list)
    goal_csv = ",".join(str(f) for f in goal_list)

    evidence_path = work_dir / f"enh_p1_{pname}_b{batch_idx}_ev.tsv"
    query_path = work_dir / f"enh_p1_{pname}_b{batch_idx}_q.tsv"

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


def run_petta(selector, evidence_path, query_path, timeout_sec):
    """Run PeTTa selector and parse (Result qid axiom (stv s c)) lines."""
    cmd = ["bash", str(PETTA_RUN), selector,
           str(evidence_path), str(query_path), "--silent"]
    result = subprocess.run(
        cmd, cwd=str(PETTA_DIR),
        capture_output=True, text=True, timeout=timeout_sec,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"PeTTa exit {result.returncode}: {(result.stderr or '').strip()[:200]}"
        )

    stv_by_qid = {}
    for line in (result.stdout or "").splitlines():
        m = RESULT_RE.match(line.strip())
        if m:
            stv_by_qid[m.group(1)] = (float(m.group(2)), float(m.group(3)))
    return stv_by_qid


def build_phase2_files(pname, candidate_axioms, phase1_stvs, cooc_table,
                       work_dir, global_weight=0.05, kappa=10.0,
                       max_partners=20, score_threshold=0.0,
                       max_init_confidence=0.9):
    """Create data/query TSV files for phase 2 (κ-bounded co-occurrence revision).

    Co-occurrence rows include IDF weight for the SOURCE partner:
      cooc<TAB>axiom_A<TAB>axiom_B<TAB>pos<TAB>neg<TAB>idf_of_source
    The IDF measures specificity: common axioms (many partners) get low IDF.

    κ controls the maximum influence of co-occurrence on the final score.
    Higher κ → lower co-occurrence confidence → less influence in PLN Revision.

    max_init_confidence caps phase-1 confidence so PLN Revision can adjust.
    Without this, IDF-NB produces c≈1 (infinite weight), blocking all reranking.
    """
    data_path = work_dir / f"enh_p2_{pname}_data.tsv"
    query_path = work_dir / f"enh_p2_{pname}_q.tsv"

    candidate_set = set(candidate_axioms)
    qid_to_axiom = {}

    with open(data_path, "w") as df, open(query_path, "w") as qf:
        # Write parameters
        df.write(f"param\tglobal_weight\t{_fmt(global_weight)}\n")
        df.write(f"param\tkappa\t{_fmt(kappa)}\n")

        # Write phase 1 STVs (cap confidence so revision can adjust)
        for phi in candidate_axioms:
            s, c = phase1_stvs.get(phi, (0.5, 0.01))
            c = min(c, max_init_confidence)
            df.write(f"init\t{phi}\t{_fmt(s)}\t{_fmt(c)}\n")

        # Write co-occurrence evidence with IDF (only between candidates)
        written_cooc = set()
        for phi in candidate_axioms:
            partners_written = 0
            # Sort potential partners by phase1 score (best first)
            partner_scores = []
            for psi in candidate_axioms:
                if phi == psi:
                    continue
                pair = tuple(sorted([phi, psi]))
                if pair in cooc_table:
                    ps, _ = phase1_stvs.get(psi, (0.5, 0.01))
                    if ps >= score_threshold:
                        partner_scores.append((psi, ps, pair))

            partner_scores.sort(key=lambda x: -x[1])

            for psi, ps, pair in partner_scores[:max_partners]:
                if pair in written_cooc:
                    continue
                pos, neg, idf_a, idf_b = cooc_table[pair]
                # Use IDF of the SOURCE partner (the one providing evidence)
                # For pair (a, b), when φ=a looking at partner b, use idf_b
                source_idf = idf_b if pair[0] == phi else idf_a
                df.write(f"cooc\t{pair[0]}\t{pair[1]}\t{_fmt(pos)}\t{_fmt(neg)}\t{_fmt(source_idf)}\n")
                written_cooc.add(pair)
                partners_written += 1

        # Write queries
        for i, phi in enumerate(candidate_axioms):
            qid = f"e{i}"
            qid_to_axiom[qid] = phi
            qf.write(f"{qid}\t{phi}\n")

    return data_path, query_path, qid_to_axiom


def score_one_problem(pname, candidate_axioms, goal_features, sfreq, tfreq,
                      idf, extended_features, cooc_table, args):
    """Two-phase scoring for one problem."""
    work_dir = args.run_temp_root / pname
    work_dir.mkdir(parents=True, exist_ok=True)

    # === Phase 1: IDF-NB scoring ===
    batch_size = args.petta_batch_size or len(candidate_axioms) or 1
    phase1_stvs = {}
    batch_tasks = []

    for bstart in range(0, len(candidate_axioms), batch_size):
        batch_idx = bstart // batch_size
        batch = candidate_axioms[bstart:bstart + batch_size]
        ev, q, qmap, skipped = build_phase1_files(
            pname, batch_idx, batch, goal_features,
            sfreq, tfreq, idf, extended_features,
            args.nb_def_prior_weight, args.nb_global_weight,
            args.nb_confidence_kappa, work_dir,
        )
        batch_tasks.append(
            {
                "job_id": f"{pname}_p1_{batch_idx}",
                "ev": ev,
                "q": q,
                "qmap": qmap,
                "skipped": skipped,
            }
        )

    p1_job_rows = [
        {"job_id": t["job_id"], "data_path": t["ev"], "query_path": t["q"]}
        for t in batch_tasks
        if t["qmap"]
    ]
    p1_stv_by_job_qid, _metrics = run_petta_jobs(
        selector=PHASE1_SELECTOR,
        petta_dir=PETTA_DIR,
        petta_run=PETTA_RUN,
        job_rows=p1_job_rows,
        jobs_dir=work_dir / "_jobs",
        timeout_sec=args.petta_timeout,
        batch_size=args.petta_job_batch_size,
        batch_prefix=f"{pname}_p1",
        keep_jobs_tsv=args.keep_tsv,
        parallel_batches=args.petta_parallel_batches,
    )

    for task in batch_tasks:
        if not task["qmap"]:
            continue
        for qid, phi in task["qmap"].items():
            key = (task["job_id"], qid)
            if key in p1_stv_by_job_qid:
                phase1_stvs[phi] = p1_stv_by_job_qid[key]
            else:
                phase1_stvs[phi] = (0.5, 0.01)

    for task in batch_tasks:
        for phi in task["skipped"]:
            phase1_stvs[phi] = (0.5, 0.01)

    # === Phase 2: Co-occurrence boost ===
    data_path, query_path, qid_to_axiom = build_phase2_files(
        pname, candidate_axioms, phase1_stvs, cooc_table,
        work_dir, global_weight=args.cooc_global_weight,
        kappa=args.cooc_kappa,
        max_partners=args.max_cooc_partners,
        score_threshold=args.cooc_score_threshold,
        max_init_confidence=args.max_init_confidence,
    )

    try:
        p2_job_rows = [
            {"job_id": f"{pname}_p2", "data_path": data_path, "query_path": query_path}
        ]
        p2_stv_by_job_qid, _metrics = run_petta_jobs(
            selector=PHASE2_SELECTOR,
            petta_dir=PETTA_DIR,
            petta_run=PETTA_RUN,
            job_rows=p2_job_rows,
            jobs_dir=work_dir / "_jobs",
            timeout_sec=args.petta_timeout,
            batch_size=1,
            batch_prefix=f"{pname}_p2",
            keep_jobs_tsv=args.keep_tsv,
            parallel_batches=args.petta_parallel_batches,
        )
        phase2_stvs = {qid: stv for (job_id, qid), stv in p2_stv_by_job_qid.items()}
    except Exception as exc:
        # Fall back to phase 1 scores if phase 2 fails
        phase2_stvs = {}

    # Build final scores
    scored_map = {}
    for phi in candidate_axioms:
        qid_candidates = [qid for qid, ax in qid_to_axiom.items() if ax == phi]
        if qid_candidates and qid_candidates[0] in phase2_stvs:
            s, c = phase2_stvs[qid_candidates[0]]
            scored_map[phi] = s
        elif phi in phase1_stvs:
            scored_map[phi] = phase1_stvs[phi][0]
        else:
            scored_map[phi] = -1e30

    # Clean up TSV files
    if not args.keep_tsv:
        for t in batch_tasks:
            t["ev"].unlink(missing_ok=True)
            t["q"].unlink(missing_ok=True)
        data_path.unlink(missing_ok=True)
        query_path.unlink(missing_ok=True)

    return sorted(scored_map.items(), key=lambda x: -x[1])


def main():
    parser = argparse.ArgumentParser(description="PLN Enhanced two-phase premise selection")
    parser.add_argument("--top-k", type=int, default=256)
    parser.add_argument("--split", choices=["train", "val"], default="val")
    parser.add_argument("--max-problems", type=int, default=None)
    parser.add_argument("--nb-tables", type=str, default=None,
                        help="Optional path to MaSh NB tables pickle")
    parser.add_argument("--deps-file", type=str, default=str(DEPS_FILE),
                        help="Dependencies JSONL for co-occurrence table")
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
                        help="Phase-1 global PLN evidence regraduation budget")
    parser.add_argument("--nb-confidence-kappa", type=float, default=1000.0,
                        help="Phase-1 confidence scale kappa for c=total/(total+kappa)")
    parser.add_argument("--min-cooc-count", type=int, default=2,
                        help="Minimum co-occurrence count to include pair")
    parser.add_argument("--max-cooc-partners", type=int, default=20,
                        help="Max co-occurrence partners per axiom in phase 2")
    parser.add_argument("--cooc-global-weight", type=float, default=0.05,
                        help="Global dampening for co-occurrence evidence-power (0=off, 1=full)")
    parser.add_argument("--cooc-kappa", type=float, default=10.0,
                        help="Prior weight κ for co-occurrence STV conversion (higher=less influence)")
    parser.add_argument("--max-init-confidence", type=float, default=0.9,
                        help="Cap phase-1 confidence so PLN Revision can adjust (default 0.9)")
    parser.add_argument("--cooc-score-threshold", type=float, default=0.0,
                        help="Min phase-1 strength for partner to propagate evidence")
    parser.add_argument("--keep-tsv", action="store_true")
    parser.add_argument("--problems", nargs="*",
                        help="Specific problem names to process (default: all)")
    parser.add_argument("--run-id", default=None,
                        help="Optional run id for temp dir isolation")
    args = parser.parse_args()

    run_id = args.run_id or f"{int(time.time())}_{os.getpid()}"
    args.run_temp_root = TEMP_ROOT / f"pln_enhanced_{run_id}"
    args.run_temp_root.mkdir(parents=True, exist_ok=True)

    if not PETTA_RUN.exists():
        raise FileNotFoundError(f"PeTTa runner not found: {PETTA_RUN}")

    print("Loading MaSh NB tables...", flush=True)
    sfreq, tfreq, idf, extended_features, sigma = load_nb_tables(args.nb_tables)
    nb_state = (sfreq, tfreq, idf, extended_features, sigma)
    print(f"  {len(tfreq)} axioms, {len(idf)} features")

    print("Building co-occurrence table...", flush=True)
    cooc_table = build_cooccurrence_table(args.deps_file, min_count=args.min_cooc_count)
    print(f"  {len(cooc_table)} co-occurrence pairs (min_count={args.min_cooc_count})")

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
    failures = 0
    t0 = time.time()

    for i, pname in enumerate(val_problems):
        if i == 0 or (i + 1) % 5 == 0:
            print(f"  {i+1}/{len(val_problems)} ({time.time()-t0:.0f}s, failures: {failures})",
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
                sfreq, tfreq, idf, extended_features, cooc_table, args,
            )
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
