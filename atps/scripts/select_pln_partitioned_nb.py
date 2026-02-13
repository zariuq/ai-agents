#!/usr/bin/env python3
"""
PLN-native partitioned Prior-NB premise selector.

Architecture (every step is a proven PLN inference rule):

  1. Per-cluster local prior via similarity regraduation:
     power(Evidence(used, total-used), sim(goal, centroid))
     [Lean: Evidence.power, toOdds_power_rpow]

  2. Pool local priors via Revision (hplus = coordinate add):
     LocalPrior = sum_j power(evidence_j, sim_j)
     Prior = GlobalPrior + LocalPrior
     [Lean: poolE_eq_hplus_of_externalBayes_totalAdd]

  3. Normalize + Tensor with NB likelihood:
     Posterior = Normalize(t_P, Prior) * Normalize(t_L, Likelihood_NB)
     score = toStrength(Posterior)
     [Lean: normalizeEvidence_toStrength, toOdds_tensor_mul]

Usage:
  python3 scripts/select_pln_partitioned_nb.py --top-k 256 --output selections.json
  python3 scripts/select_pln_partitioned_nb.py --smoke-test --top-k 256 --output /dev/null
"""

import argparse
import json
import math
import pickle
import sys
import time
from collections import defaultdict
from pathlib import Path

import numpy as np
from scipy.sparse import csr_matrix

sys.path.insert(0, str(Path(__file__).parent))
from mash_nb_scorer import (
    load_tables as load_nb_tables,
    normalize_axiom_name,
    parse_sparse_line,
    read_problem_formulas,
    score_all_axioms as score_mash_nb_all,
)

DATASET_DIR = Path("/home/zar/claude/atps/datasets/extended_mptp5k")
CHAINY_VAL_DIR = DATASET_DIR / "chainy" / "val"
FEATURES_VAL_DIR = DATASET_DIR / "features_chainy_val"
MODELS_DIR = DATASET_DIR / "models"
TABLES_FILE = MODELS_DIR / "partitioned_tables.pkl"

CONJ_ROLES = {"conjecture", "negated_conjecture"}
AXIOM_ROLES = {"axiom", "hypothesis", "definition"}


# -- PLN Evidence Operations (matching EvidenceQuantale.lean exactly) ----------

def evidence_power(pos, neg, w):
    """Evidence.power: coordinatewise exponentiation.
    Lean: EvidenceQuantale.lean line 762
    odds(power(e,w)) = odds(e)^w  [toOdds_power_rpow]
    """
    if w == 0:
        return (1.0, 1.0)  # power e 0 = (1, 1)
    return (max(pos, 1e-30) ** w, max(neg, 1e-30) ** w)


def evidence_hplus(e1, e2):
    """Evidence revision (hplus): coordinatewise addition.
    Lean: Evidence.hplus_def — (pos₁+pos₂, neg₁+neg₂)
    Uniquely forced by external Bayesianity + total additivity.
    """
    return (e1[0] + e2[0], e1[1] + e2[1])


def evidence_tensor(e1, e2):
    """Evidence tensor: coordinatewise multiplication.
    Lean: Evidence.tensor_def — (pos₁*pos₂, neg₁*neg₂)
    Sequential composition in the evidence quantale.
    """
    return (e1[0] * e2[0], e1[1] * e2[1])


def evidence_normalize(e, t):
    """Normalize evidence to have total = t, preserving strength.
    Lean: normalizeEvidence_toStrength — strength is invariant.
    """
    total = e[0] + e[1]
    if total <= 0 or t <= 0:
        return (0.0, t)  # degenerate: all negative
    s = e[0] / total  # strength = pos/total
    return (s * t, (1 - s) * t)


def evidence_to_strength(e):
    """Project evidence to strength = pos/total.
    Lean: Evidence.toStrength
    """
    total = e[0] + e[1]
    if total <= 0:
        return 0.0
    return e[0] / total


# -- NB Likelihood as Evidence ------------------------------------------------

def nb_likelihood_evidence(goal_features, axiom, sfreq, tfreq, idf,
                           extended_features=None):
    """Convert NB log-likelihood into evidence (pos, neg) via exponentiation.

    The MaSh NB score is a log-odds: log(P(useful|features)/P(not useful|features)).
    We convert to evidence: if log-odds > 0, more positive; if < 0, more negative.

    For PLN compatibility, we use the IDF-weighted feature overlap as evidence:
    each shared feature contributes power(feature_evidence, idf_weight) via tensor.
    """
    t_phi = tfreq.get(axiom, 0)
    if t_phi <= 0:
        return (0.001, 1.0)  # weak negative evidence

    t_phi_f = float(t_phi)
    s_phi = sfreq.get(axiom, {})

    # Extended features
    if extended_features is not None:
        f_bar_phi = extended_features.get(axiom, set())
    else:
        f_bar_phi = set(s_phi.keys())

    # Shared features: F(goal) ∩ F̄(axiom)
    shared = goal_features & f_bar_phi
    goal_only = goal_features - f_bar_phi

    if not shared and not goal_only:
        return (0.5, 0.5)  # uninformative

    # Build evidence from shared features via tensor composition
    # Each feature contributes evidence(sf/t, 1 - sf/t) regraduated by IDF
    evidence = (1.0, 1.0)  # start with unit evidence

    for f in shared:
        idf_f = idf.get(f, 1.0)
        sf = s_phi.get(f, 0)
        if sf <= 0:
            sf = 0.5  # Laplace smoothing
        # Feature evidence: (shared_freq/total, 1 - shared_freq/total)
        feat_strength = min(float(sf) / t_phi_f, 0.999)
        feat_ev = (feat_strength, 1.0 - feat_strength)
        # Regraduation by IDF weight: power(feat_ev, idf_f)
        # Lean: toLogOdds_power_mul — log-odds scale linearly
        regraduated = evidence_power(feat_ev[0], feat_ev[1], idf_f)
        evidence = evidence_tensor(evidence, regraduated)

    # Penalty for goal-only features (evidence toward negative)
    n_goal_only = len(goal_only)
    if n_goal_only > 0:
        # Small negative evidence per missing feature
        penalty_per = (0.3, 0.7)
        total_penalty = evidence_power(penalty_per[0], penalty_per[1], min(n_goal_only, 20))
        evidence = evidence_tensor(evidence, total_penalty)

    return evidence


# -- Data Loading -------------------------------------------------------------

def load_partitioned_tables(path=None):
    """Load cluster tables from pickle."""
    p = Path(path) if path else TABLES_FILE
    with open(p, "rb") as f:
        return pickle.load(f)


def load_val_problem(problem_name):
    """Load conjecture features and axiom candidates from one val problem."""
    pfile = CHAINY_VAL_DIR / problem_name
    vfile = FEATURES_VAL_DIR / f"{problem_name}.vec"
    if not pfile.exists() or not vfile.exists():
        return None, None, None

    formulas = read_problem_formulas(pfile)
    with open(vfile) as vf:
        vec_lines = [line for line in vf if line.strip()]

    aligned = min(len(formulas), len(vec_lines))
    gamma_features = None
    axiom_map = {}  # normalized_name -> original_name

    for idx in range(aligned):
        fname, role = formulas[idx]
        if role in CONJ_ROLES:
            gamma_features = parse_sparse_line(vec_lines[idx])
        elif role in AXIOM_ROLES:
            norm = normalize_axiom_name(fname)
            if norm not in axiom_map:
                axiom_map[norm] = fname

    return gamma_features, axiom_map, pfile


def goal_to_sparse_vector(goal_features, total_dim, article_name, article_to_idx,
                          original_dim):
    """Convert goal features to sparse vector matching cluster centroids."""
    rows, cols, vals = [], [], []
    for f in goal_features:
        if f < total_dim:
            rows.append(0)
            cols.append(f)
            vals.append(1.0)
    # Article one-hot
    if article_name and article_name in article_to_idx:
        rows.append(0)
        cols.append(original_dim + article_to_idx[article_name])
        vals.append(1.0)

    return csr_matrix((vals, (rows, cols)), shape=(1, total_dim), dtype=np.float32)


def extract_article_from_problem(problem_file):
    """Extract Mizar article name from problem file header."""
    try:
        with open(problem_file) as f:
            for line in f:
                line = line.strip()
                if line.startswith("% Mizar problem:"):
                    parts = line.split(":", 1)[1].strip().split(",")
                    if len(parts) >= 2:
                        return parts[1].strip()
                if not line.startswith("%"):
                    break
    except Exception:
        pass
    return None


# -- PLN Scoring Pipeline -----------------------------------------------------

def compute_cluster_similarities(goal_vec, centroids, top_k=10):
    """Compute cosine similarity to each cluster centroid, return top-k."""
    from sklearn.metrics.pairwise import cosine_similarity

    sims = cosine_similarity(goal_vec, centroids).flatten()
    # Top-k clusters by similarity
    top_indices = np.argsort(sims)[::-1][:top_k]
    return [(int(idx), float(sims[idx])) for idx in top_indices if sims[idx] > 0]


def score_one_problem(goal_features, axiom_map, problem_file,
                      tables, nb_tables, args):
    """PLN-native scoring for one problem.

    Returns list of (original_axiom_name, score) sorted descending.
    """
    cluster_evidence = tables["cluster_evidence"]
    global_prior = tables["global_prior"]
    centroids = tables["cluster_centroids"]
    article_to_idx = tables["article_to_idx"]
    original_dim = tables["original_feature_dim"]
    total_dim = tables["total_feature_dim"]

    sfreq, tfreq, idf_weights, extended_features, sigma = nb_tables

    t_P = args.t_prior
    t_L = args.t_lik

    # Extract article for this problem
    article = extract_article_from_problem(problem_file)

    # Build goal vector for cluster similarity
    goal_vec = goal_to_sparse_vector(
        goal_features, total_dim, article, article_to_idx, original_dim
    )

    # Step 1: Find nearest clusters
    cluster_sims = compute_cluster_similarities(goal_vec, centroids, args.top_clusters)

    if args.verbose:
        print(f"  Top clusters: {[(c, f'{s:.3f}') for c, s in cluster_sims[:5]]}")

    # Step 2: Collect all MaSh NB scores, then rescale to preserve ranking
    from mash_nb_scorer import mash_nb_score, as_weighted_features
    weighted_feats = as_weighted_features(goal_features)
    sigma_params = sigma if isinstance(sigma, dict) else {
        "sigma1": 30.0, "sigma2": 5.0, "sigma3": 0.2, "sigma4": -18.0,
    }

    # 2a: Collect raw NB scores for all candidates
    raw_nb = {}
    for norm_name in axiom_map:
        raw_nb[norm_name] = mash_nb_score(
            norm_name, weighted_feats, sfreq, tfreq, idf_weights,
            extended_features=extended_features,
            **sigma_params,
        )

    # 2b: Rescale NB scores to a PLN-compatible log-odds range.
    # Raw MaSh NB scores span ~[-5000, +100] — far too wide for exp().
    # We affine-rescale so the per-problem median maps to 0 (neutral odds)
    # and the interquartile range maps to [-2, +2] (moderate evidence).
    # This is a change of units (toLogOdds_power_mul justifies linear
    # rescaling of log-odds), not a change of ranking.
    if raw_nb:
        nb_vals = sorted(raw_nb.values())
        n = len(nb_vals)
        median = nb_vals[n // 2]
        q1 = nb_vals[n // 4] if n >= 4 else nb_vals[0]
        q3 = nb_vals[3 * n // 4] if n >= 4 else nb_vals[-1]
        iqr = q3 - q1
        if iqr > 0:
            scale = 4.0 / iqr  # maps IQR to [-2, +2]
        else:
            # All scores identical — use fallback scale
            rng = nb_vals[-1] - nb_vals[0]
            scale = 4.0 / rng if rng > 0 else 1.0
        shift = median
    else:
        scale, shift = 1.0, 0.0

    # Step 3: PLN scoring for each candidate axiom
    scores = {}
    for norm_name in axiom_map:
        # --- Prior: Global + Partitioned Local ---

        # Global prior evidence
        gp = global_prior.get(norm_name, (0.001, 1.0))

        # Partitioned local prior: sum of regraduated per-cluster evidence
        local_prior = (0.0, 0.0)
        for cid, sim in cluster_sims:
            cev = cluster_evidence.get(cid, {})
            if norm_name in cev:
                pos, neg = cev[norm_name]
                # PLN power regraduation by similarity
                # odds(power(e, sim)) = odds(e)^sim
                regraduated = evidence_power(pos, neg, sim)
                local_prior = evidence_hplus(local_prior, regraduated)

        # Revise global + local (hplus)
        prior = evidence_hplus(gp, local_prior)

        # --- Likelihood: MaSh NB score → evidence ---
        # Rescaled log-odds: linear transform preserves ranking and is
        # justified by toLogOdds_power_mul (log-odds scale linearly under power).
        scaled_score = (raw_nb[norm_name] - shift) * scale
        # Clamp to [-20, +20] — now actually effective since scores are rescaled
        scaled_score = max(min(scaled_score, 20.0), -20.0)
        odds = math.exp(scaled_score)
        lik = (odds, 1.0)

        # --- Normalize + Tensor ---
        norm_prior = evidence_normalize(prior, t_P)
        norm_lik = evidence_normalize(lik, t_L)
        posterior = evidence_tensor(norm_prior, norm_lik)

        # Score = toStrength(posterior)
        score = evidence_to_strength(posterior)
        scores[norm_name] = score

    # Sort by score descending
    ranked = sorted(scores.items(), key=lambda x: -x[1])

    # Map back to original axiom names
    result = []
    for norm_name, sc in ranked:
        if norm_name in axiom_map:
            result.append((axiom_map[norm_name], sc))

    return result


# -- Main ---------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="PLN partitioned Prior-NB selector")
    parser.add_argument("--top-k", type=int, default=256, help="Number of premises to select")
    parser.add_argument("--output", required=True, help="Output selections JSON")
    parser.add_argument("--t-prior", type=float, default=100.0,
                        help="Prior normalization total (default: 100)")
    parser.add_argument("--t-lik", type=float, default=100.0,
                        help="Likelihood normalization total (default: 100)")
    parser.add_argument("--top-clusters", type=int, default=10,
                        help="Number of nearest clusters to use (default: 10)")
    parser.add_argument("--smoke-test", action="store_true",
                        help="Run on first 5 problems only")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--max-problems", type=int, default=None)
    parser.add_argument("--tables", type=str, default=None,
                        help="Path to partitioned_tables.pkl (default: models/partitioned_tables.pkl)")
    args = parser.parse_args()

    print("Loading partitioned cluster tables...")
    tables = load_partitioned_tables(args.tables)
    print(f"  {tables['num_clusters']} clusters, "
          f"{len(tables['all_axioms'])} axioms, "
          f"features: {tables['total_feature_dim']}")

    print("Loading MaSh NB tables...")
    nb_tables = load_nb_tables()
    sfreq, tfreq, idf, ext_feat, sigma = nb_tables
    print(f"  {len(tfreq)} axioms, {len(idf)} IDF features")

    print(f"Parameters: t_P={args.t_prior}, t_L={args.t_lik}, "
          f"top_clusters={args.top_clusters}, top_k={args.top_k}")

    # Get validation problems
    val_problems = sorted(p.name for p in CHAINY_VAL_DIR.iterdir() if p.is_file())
    if args.smoke_test:
        val_problems = val_problems[:5]
    elif args.max_problems:
        val_problems = val_problems[:args.max_problems]
    print(f"Processing {len(val_problems)} validation problems...")

    selections = {}
    t0 = time.time()
    n_done = 0
    n_nodata = 0

    for pname in val_problems:
        gamma_features, axiom_map, pfile = load_val_problem(pname)
        if gamma_features is None or not axiom_map:
            if args.verbose:
                print(f"  SKIP {pname}: no features or axioms")
            selections[pname] = []
            n_nodata += 1
            continue

        if args.verbose:
            print(f"  {pname}: {len(gamma_features)} features, {len(axiom_map)} axioms")

        ranked = score_one_problem(
            gamma_features, axiom_map, pfile, tables, nb_tables, args
        )

        selections[pname] = [name for name, _ in ranked[:args.top_k]]
        n_done += 1

        if n_done % 50 == 0:
            elapsed = time.time() - t0
            rate = n_done / elapsed if elapsed > 0 else 0
            print(f"  [{n_done}/{len(val_problems)}] {rate:.1f} problems/s")

    elapsed = time.time() - t0
    print(f"\nDone: {n_done} problems scored, {n_nodata} skipped ({elapsed:.1f}s)")

    # Save
    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(selections, f)

    print(f"Saved selections to {out_path}")

    # Quick coverage stats
    nonempty = sum(1 for v in selections.values() if v)
    avg_sel = (sum(len(v) for v in selections.values()) / max(nonempty, 1)
               if nonempty > 0 else 0)
    print(f"  {nonempty} problems with selections, avg {avg_sel:.0f} premises/problem")


if __name__ == "__main__":
    main()
