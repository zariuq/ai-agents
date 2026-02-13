#!/usr/bin/env python3
"""
Build partitioned cluster tables for PLN-native premise selection.

Clusters training problems by feature similarity (k-means on augmented feature
vectors where article identity is an additional binary feature). For each cluster
and each axiom, stores evidence counts: (used_count, total_proved - used_count).

This is the data preparation step for the PLN partitioned prior architecture:
  LocalEvidence(C_j, a) = Evidence(used_j(a), total_j - used_j(a))

Usage:
  python3 scripts/build_partitioned_tables.py [--num-clusters 50]
"""

import argparse
import json
import pickle
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np
from scipy.sparse import csr_matrix, hstack

sys.path.insert(0, str(Path(__file__).parent))
from mash_nb_scorer import (
    normalize_axiom_name,
    parse_sparse_line,
    read_problem_formulas,
)

DATASET_DIR = Path("/home/zar/claude/atps/datasets/extended_mptp5k")
CHAINY_TRAIN_DIR = DATASET_DIR / "chainy" / "train"
FEATURES_TRAIN_DIR = DATASET_DIR / "features_chainy"
DEPS_FILE = DATASET_DIR / "deps" / "bushy_train_deps.jsonl"
MODELS_DIR = DATASET_DIR / "models"

CONJ_ROLES = {"conjecture", "negated_conjecture"}


def extract_article_name(problem_file):
    """Extract Mizar article name from problem file header comment."""
    try:
        with open(problem_file) as f:
            for line in f:
                line = line.strip()
                if line.startswith("% Mizar problem:"):
                    # Format: % Mizar problem: FACTNAME,ARTICLENAME,LINENUM,THEOREMNUM
                    parts = line.split(":", 1)[1].strip().split(",")
                    if len(parts) >= 2:
                        return parts[1].strip()
                if not line.startswith("%"):
                    break
    except Exception:
        pass
    return None


def load_training_data():
    """Load proved training problems with conjecture features and used axioms."""
    # Load proof dependencies
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
            article = extract_article_name(prob_file)
            training.append({
                "problem": pname,
                "gamma_features": gamma_features,
                "used_axioms": used_set,
                "article": article,
            })

    return training


def build_feature_matrix(training_data):
    """Build sparse feature matrix with article one-hot features appended.

    Returns (sparse_matrix, feature_dim_original, article_to_idx).
    """
    # Find max feature index
    max_feat = 0
    for entry in training_data:
        if entry["gamma_features"]:
            max_feat = max(max_feat, max(entry["gamma_features"]))
    original_dim = max_feat + 1

    # Build article vocabulary
    articles = sorted({e["article"] for e in training_data if e["article"] is not None})
    article_to_idx = {art: i for i, art in enumerate(articles)}
    n_articles = len(articles)

    # Build sparse matrix: rows = training problems, cols = original features + article one-hots
    n = len(training_data)
    total_dim = original_dim + n_articles

    rows, cols, vals = [], [], []
    for i, entry in enumerate(training_data):
        # Original features
        for f in entry["gamma_features"]:
            rows.append(i)
            cols.append(f)
            vals.append(1.0)
        # Article one-hot
        art = entry.get("article")
        if art is not None and art in article_to_idx:
            rows.append(i)
            cols.append(original_dim + article_to_idx[art])
            vals.append(1.0)

    matrix = csr_matrix(
        (vals, (rows, cols)),
        shape=(n, total_dim),
        dtype=np.float32,
    )

    return matrix, original_dim, article_to_idx


def cluster_training_data(feature_matrix, num_clusters):
    """Cluster training problems by feature similarity using MiniBatchKMeans."""
    from sklearn.cluster import MiniBatchKMeans

    n = feature_matrix.shape[0]
    k = min(num_clusters, n)

    kmeans = MiniBatchKMeans(
        n_clusters=k,
        batch_size=min(1024, n),
        random_state=42,
        n_init=3,
        max_iter=100,
    )
    labels = kmeans.fit_predict(feature_matrix)

    return labels, kmeans.cluster_centers_


def build_cluster_evidence(training_data, labels):
    """Build per-cluster, per-axiom evidence counts.

    Returns:
      cluster_evidence: dict[cluster_id -> dict[axiom -> (pos_count, neg_count)]]
      cluster_sizes: dict[cluster_id -> int] (number of proved problems in cluster)
    """
    cluster_problems = defaultdict(list)
    for i, entry in enumerate(training_data):
        cluster_problems[labels[i]].append(entry)

    cluster_evidence = {}
    cluster_sizes = {}
    all_axioms = set()

    for cid, problems in cluster_problems.items():
        n_proved = len(problems)
        cluster_sizes[cid] = n_proved

        # Count axiom usage within this cluster
        axiom_used = Counter()
        for p in problems:
            for a in p["used_axioms"]:
                axiom_used[a] += 1
                all_axioms.add(a)

        # Evidence: (used_count, total_proved - used_count)
        cluster_evidence[cid] = {}
        for a, cnt in axiom_used.items():
            pos = cnt
            neg = max(0, n_proved - cnt)
            cluster_evidence[cid][a] = (pos, neg)

    return cluster_evidence, cluster_sizes, all_axioms


def build_global_prior(training_data):
    """Build global prior evidence from all training data.

    Returns dict[axiom -> (pos_count, neg_count)].
    """
    n_total = len(training_data)
    axiom_used = Counter()
    for entry in training_data:
        for a in entry["used_axioms"]:
            axiom_used[a] += 1

    global_prior = {}
    for a, cnt in axiom_used.items():
        global_prior[a] = (cnt, max(0, n_total - cnt))

    return global_prior


def main():
    parser = argparse.ArgumentParser(description="Build partitioned cluster tables")
    parser.add_argument("--num-clusters", type=int, default=50,
                        help="Number of k-means clusters (default: 50)")
    parser.add_argument("--output", type=str, default=None,
                        help="Output pickle path (default: models/partitioned_tables.pkl)")
    args = parser.parse_args()

    MODELS_DIR.mkdir(parents=True, exist_ok=True)
    output_path = Path(args.output) if args.output else MODELS_DIR / "partitioned_tables.pkl"

    print(f"Loading training data from {DEPS_FILE}...")
    t0 = time.time()
    training_data = load_training_data()
    print(f"  Loaded {len(training_data)} proved training problems ({time.time()-t0:.1f}s)")

    if not training_data:
        print("ERROR: No training data loaded. Check paths.")
        sys.exit(1)

    print(f"Building augmented feature matrix...")
    t0 = time.time()
    feature_matrix, original_dim, article_to_idx = build_feature_matrix(training_data)
    total_dim = feature_matrix.shape[1]
    n_articles = len(article_to_idx)
    print(f"  Matrix: {feature_matrix.shape[0]} x {total_dim} "
          f"(original: {original_dim}, articles: {n_articles}) ({time.time()-t0:.1f}s)")

    print(f"Clustering into {args.num_clusters} clusters...")
    t0 = time.time()
    labels, centroids = cluster_training_data(feature_matrix, args.num_clusters)
    n_actual_clusters = len(set(labels))
    print(f"  {n_actual_clusters} non-empty clusters ({time.time()-t0:.1f}s)")

    # Cluster size distribution
    cluster_counts = Counter(labels)
    sizes = sorted(cluster_counts.values(), reverse=True)
    print(f"  Cluster sizes: max={sizes[0]}, min={sizes[-1]}, "
          f"median={sizes[len(sizes)//2]}")

    print(f"Building per-cluster evidence tables...")
    t0 = time.time()
    cluster_evidence, cluster_sizes, all_axioms = build_cluster_evidence(training_data, labels)
    print(f"  {len(all_axioms)} axioms across {len(cluster_evidence)} clusters ({time.time()-t0:.1f}s)")

    print(f"Building global prior...")
    global_prior = build_global_prior(training_data)
    print(f"  {len(global_prior)} axioms with non-zero global prior")

    # Save tables
    tables = {
        "cluster_centroids": centroids,        # numpy array (k x total_dim)
        "cluster_evidence": cluster_evidence,   # dict[cluster -> dict[axiom -> (pos, neg)]]
        "cluster_sizes": cluster_sizes,         # dict[cluster -> int]
        "global_prior": global_prior,           # dict[axiom -> (pos, neg)]
        "all_axioms": all_axioms,               # set of all axiom names
        "article_to_idx": article_to_idx,       # dict[article_name -> index]
        "original_feature_dim": original_dim,   # int
        "total_feature_dim": total_dim,         # int
        "num_clusters": n_actual_clusters,       # int
        "labels": labels,                       # numpy array of cluster assignments
    }

    with open(output_path, "wb") as f:
        pickle.dump(tables, f, protocol=4)

    fsize = output_path.stat().st_size / (1024 * 1024)
    print(f"\nSaved to {output_path} ({fsize:.1f} MB)")
    print(f"Summary: {len(training_data)} problems -> {n_actual_clusters} clusters "
          f"-> {len(all_axioms)} axioms")


if __name__ == "__main__":
    main()
