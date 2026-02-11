#!/usr/bin/env python3
"""
PLN-native k-NN premise selector (v2) -- ALL reasoning in ONE PeTTa call.

Python only does data retrieval / serialization:
  - Find top-K neighbors by shared feature count
  - Write raw features (goal + neighbor) to TSV
  - Optionally write NB evidence to a Prolog facts file (.pl)

PeTTa does ALL reasoning in a single invocation:
  - Feature overlap via Prolog atomspace (goal_feat_db ∩ nbr_feat_db)
  - Similarity evidence from feature overlap (PLN)
  - kNN evidence accumulation via hplus (PLN Revision)
  - NB scoring via tensor/power (PLN)
  - kNN + NB merge via pln-revision (PLN)

Usage:
  python3 scripts/select_pln_knn.py --top-k 256 --output selections.json
  python3 scripts/select_pln_knn.py --top-k 256 --merge-nb --output sel.json
  python3 scripts/select_pln_knn.py --smoke-test --output /dev/null
"""

import argparse
import json
import re
import resource
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
COMBINED_SELECTOR = "demos/pln_knn_selector.metta"

RESULT_RE = re.compile(
    r"^\(Result\s+([^\s\)]+)\s+[^\s\)]+\s+\(stv\s+([-+0-9.eE]+)\s+([-+0-9.eE]+)\)\)\s*$"
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

def load_training_data():
    """Load proved training problems: conjecture features + used axioms."""
    deps_by_name = {}
    with open(DEPS_FILE) as f:
        for line in f:
            rec = json.loads(line)
            pname = rec["problem_name"]
            used = rec.get("used_axioms", [])
            if used:
                deps_by_name[pname] = {normalize_axiom_name(a) for a in used}

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
        df.write(f"param\tused_confidence\t{_fmt(args.used_confidence)}\n")

        if args.merge_nb:
            df.write(f"param\tnb_global_weight\t{_fmt(args.nb_global_weight)}\n")
            df.write(f"param\tnb_confidence_kappa\t{_fmt(args.nb_confidence_kappa)}\n")
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


def run_petta(data_path, query_path, timeout_sec):
    """Run combined PeTTa selector — ONE invocation for everything."""
    cmd = ["nice", "-n", "19", "bash", str(PETTA_RUN), COMBINED_SELECTOR,
           str(data_path), str(query_path), "--silent"]
    result = subprocess.run(
        cmd, cwd=str(PETTA_DIR),
        capture_output=True, text=True, timeout=timeout_sec,
        preexec_fn=_limit_mem,
    )
    if result.returncode != 0:
        stderr_snip = (result.stderr or "").strip()[:300]
        raise RuntimeError(f"PeTTa exit {result.returncode}: {stderr_snip}")

    stv_by_qid = {}
    for line in (result.stdout or "").splitlines():
        m = RESULT_RE.match(line.strip())
        if m:
            stv_by_qid[m.group(1)] = (float(m.group(2)), float(m.group(3)))
    return stv_by_qid


def score_one_problem(pname, candidate_axioms, goal_features,
                      training_data, nb_state, args):
    """Score one problem — ONE PeTTa call for kNN + NB + merge."""
    work_dir = TEMP_ROOT / "pln_knn" / pname
    work_dir.mkdir(parents=True, exist_ok=True)

    # Data retrieval: find neighbors by shared feature count
    neighbors = find_top_k_neighbors(goal_features, training_data, k=args.knn_k)

    # Write ONE combined TSV
    data_path, query_path, qid_to_axiom, nb_pl_path = build_combined_tsv(
        pname, candidate_axioms, goal_features,
        neighbors, nb_state, args, work_dir,
    )

    # ONE PeTTa call for everything
    try:
        stv_by_qid = run_petta(data_path, query_path, args.petta_timeout)
    except Exception as exc:
        print(f"  WARN PeTTa failed for {pname}: {exc}", flush=True)
        stv_by_qid = {}

    # Build scored list
    scored = []
    for phi in candidate_axioms:
        qid_candidates = [qid for qid, ax in qid_to_axiom.items() if ax == phi]
        if qid_candidates and qid_candidates[0] in stv_by_qid:
            s, c = stv_by_qid[qid_candidates[0]]
            scored.append((phi, s))
        else:
            scored.append((phi, -1e30))

    if not args.keep_tsv:
        data_path.unlink(missing_ok=True)
        query_path.unlink(missing_ok=True)
        if nb_pl_path is not None:
            nb_pl_path.unlink(missing_ok=True)

    scored.sort(key=lambda x: -x[1])
    return scored


def load_val_problem(pname):
    """Load conjecture features and axiom map for a val problem."""
    pfile = CHAINY_VAL_DIR / pname
    vec_file = FEATURES_VAL_DIR / f"{pname}.vec"
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


def main():
    parser = argparse.ArgumentParser(
        description="PLN-native k-NN + NB premise selector (v2, single PeTTa call)")
    parser.add_argument("--top-k", type=int, default=256)
    parser.add_argument("--max-problems", type=int, default=None)
    parser.add_argument("--output", required=True, help="Output selections JSON")
    parser.add_argument("--knn-k", type=int, default=16,
                        help="Number of nearest neighbors (default 16)")
    parser.add_argument("--neg-weight", type=float, default=0.5)
    parser.add_argument("--kappa", type=float, default=10.0)
    parser.add_argument("--global-weight", type=float, default=1.0)
    parser.add_argument("--sim-kappa", type=float, default=5.0)
    parser.add_argument("--used-confidence", type=float, default=0.95)
    parser.add_argument("--merge-nb", action="store_true",
                        help="Also compute PLN-NB and merge via PLN Revision")
    parser.add_argument("--nb-def-prior-weight", type=float, default=1000.0)
    parser.add_argument("--nb-global-weight", type=float, default=1.0)
    parser.add_argument("--nb-confidence-kappa", type=float, default=1000.0)
    parser.add_argument("--petta-batch-size", type=int, default=1,
                        help="Compatibility flag (unused in one-problem-per-call mode)")
    parser.add_argument("--petta-job-batch-size", type=int, default=1,
                        help="Compatibility flag (unused in one-problem-per-call mode)")
    parser.add_argument("--petta-timeout", type=int, default=240)
    parser.add_argument("--keep-tsv", action="store_true")
    parser.add_argument("--smoke-test", action="store_true",
                        help="Only process first 20 problems")
    parser.add_argument("--problems", nargs="*")
    args = parser.parse_args()

    if args.smoke_test and args.max_problems is None:
        args.max_problems = 20

    print("Loading training data (features + deps)...", flush=True)
    training_data = load_training_data()
    print(f"  {len(training_data)} proved training problems with features")

    nb_state = None
    if args.merge_nb:
        print("Loading MaSh NB tables for merge...", flush=True)
        nb_state = load_nb_tables()
        print(f"  {len(nb_state[1])} axioms in NB tables")

    if args.problems:
        val_problems = sorted(args.problems)
    else:
        val_problems = sorted(p.name for p in CHAINY_VAL_DIR.iterdir() if p.is_file())
    if args.max_problems:
        val_problems = val_problems[:args.max_problems]

    mode = "PLN-kNN+NB-v2" if args.merge_nb else "PLN-kNN-v2"
    print(f"Mode: {mode}, problems: {len(val_problems)}, top-k: {args.top_k}, "
          f"knn_k: {args.knn_k}, kappa: {args.kappa}, sim_kappa: {args.sim_kappa}")

    selections = {}
    no_features = 0
    failures = 0
    t0 = time.time()

    for i, pname in enumerate(val_problems):
        if i == 0 or (i + 1) % 5 == 0:
            elapsed = time.time() - t0
            print(f"  {i+1}/{len(val_problems)} ({elapsed:.0f}s, failures: {failures})",
                  flush=True)

        gamma_features, axiom_map = load_val_problem(pname)
        if gamma_features is None or not axiom_map:
            no_features += 1
            selections[pname] = []
            continue

        candidates = list(axiom_map.keys())

        try:
            scored = score_one_problem(
                pname, candidates, gamma_features,
                training_data, nb_state, args,
            )
            selections[pname] = [axiom_map[norm] for norm, _ in scored[:args.top_k]
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
    n_sel = sum(1 for v in selections.values() if v)
    print(f"\nDone in {elapsed:.0f}s. Selections: {n_sel}/{len(val_problems)}, "
          f"no_features: {no_features}, failures: {failures}")
    print(f"Saved: {out_path}")


if __name__ == "__main__":
    main()
