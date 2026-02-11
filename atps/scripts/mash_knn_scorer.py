#!/usr/bin/env python3
"""
MaSh/Mizar-style internal k-NN scoring.

Core mechanics mirror Isabelle's MaSh internal k-NN implementation:
  - tfidf-weighted feature overlap with power tau1=6
  - dependency spreading factor tau2=2.7
  - variable-k growth until enough nonzero recommendations

Tables are produced by mash_knn_build_tables.py.
"""

import json
import math
import pickle
import re
import sys
from pathlib import Path

DATASET_DIR = Path("/home/zar/claude/atps/datasets/extended_mptp5k")
MODELS_DIR = DATASET_DIR / "models"
FORMULA_RE = re.compile(r"^(fof|cnf)\(([^,]+),\s*([^,]+),")
AXIOM_ROLES = {"axiom", "hypothesis", "definition"}
CONJ_ROLES = {"conjecture", "negated_conjecture"}


def normalize_axiom_name(name):
    """Normalize prior_<article>__<fact> to <fact>."""
    if name.startswith("prior_"):
        after = name[len("prior_") :]
        parts = after.split("__", 1)
        if len(parts) == 2:
            return parts[1]
    return name


def parse_sparse_line(line):
    """Parse 'idx:val ...' into set of non-zero feature indices."""
    features = set()
    for item in line.strip().split():
        if ":" not in item:
            continue
        idx, val = item.split(":", 1)
        if float(val) != 0.0:
            features.add(int(idx))
    return features


def read_problem_formulas(problem_file):
    """Return ordered list of (name, role)."""
    formulas = []
    with open(problem_file) as f:
        for raw in f:
            line = raw.strip()
            if not line or line.startswith("%"):
                continue
            m = FORMULA_RE.match(line)
            if m:
                formulas.append((m.group(2).strip(), m.group(3).strip()))
    return formulas


def as_weighted_features(features):
    """Convert set[int] to list[(int, float)] with unit weights."""
    return [(f, 1.0) for f in features]


def load_tables():
    """Load k-NN tables from pickle."""
    path = MODELS_DIR / "mash_knn_tables.pkl"
    if not path.exists():
        raise FileNotFoundError(f"{path} not found. Run mash_knn_build_tables.py first.")
    with open(path, "rb") as f:
        tables = pickle.load(f)
    return tables


def compute_recommendations(goal_features, tables, max_suggs):
    """
    Compute MaSh k-NN recommendation scores for all known facts.

    Returns list[float] indexed by fact index.
    """
    fact_names = tables["fact_names"]
    idf = tables["idf"]
    example_name_idx = tables["example_name_idx"]
    example_dep_idxs = tables["example_dep_idxs"]
    feat_examples = tables["feat_examples"]
    constants = tables["constants"]

    tau_power = float(constants.get("tau_power", 6.0))
    deps_factor = float(constants.get("deps_factor", 2.7))
    initial_k = int(constants.get("initial_k", 0))
    age = float(constants.get("age_init", 500000000.0))
    age_step = float(constants.get("age_step", 10000.0))

    num_examples = len(example_name_idx)

    overlaps = [0.0] * num_examples
    for feat, feat_weight in goal_features:
        tfidf = idf.get(feat)
        if tfidf is None:
            continue
        sw = feat_weight * tfidf
        w6 = sw ** tau_power
        for ex_idx in feat_examples.get(feat, []):
            overlaps[ex_idx] += w6

    # Descending by overlap (nearest first).
    nearest_examples = sorted(range(num_examples), key=lambda i: overlaps[i], reverse=True)

    recommends = [0.0] * len(fact_names)
    no_recommends = 0
    k = 0

    def inc_recommend(v, fact_idx):
        nonlocal no_recommends
        ov = recommends[fact_idx]
        if ov <= 0.0:
            no_recommends += 1
            recommends[fact_idx] = age + ov
        else:
            recommends[fact_idx] = v + ov

    def do_k(k_value):
        if k_value >= num_examples:
            return False

        ex_idx = nearest_examples[k_value]
        o2 = overlaps[ex_idx]
        inc_recommend(o2, example_name_idx[ex_idx])

        deps = example_dep_idxs[ex_idx]
        dep_count = len(deps)
        if dep_count > 0:
            spread = deps_factor * o2 / float(dep_count)
            for dep_idx in deps:
                inc_recommend(spread, dep_idx)

        return True

    # Equivalent to Isabelle's while1 with initial_k=0: always process first neighbor.
    while k != initial_k + 1:
        if not do_k(k):
            break
        k += 1

    # Variable-k growth until enough nonzero recommendations are available.
    while no_recommends < max_suggs:
        if not do_k(k):
            break
        k += 1
        age -= age_step

    return recommends


def score_all_axioms(candidate_axioms, gamma_features, tables, max_suggs=256):
    """Score and sort candidate axioms descending by MaSh k-NN score."""
    fact_index = tables["fact_index"]
    weighted_goal = as_weighted_features(gamma_features)
    recommends = compute_recommendations(weighted_goal, tables, max_suggs=max_suggs)

    scored = []
    for ax in candidate_axioms:
        idx = fact_index.get(ax)
        if idx is None:
            scored.append((ax, -1e30))
        else:
            scored.append((ax, recommends[idx]))

    scored.sort(key=lambda x: -x[1])
    return scored


def load_problem_goal_and_axioms(problem_name, problem_dir, features_dir):
    """Load conjecture features and normalized candidate axioms for one problem."""
    pfile = problem_dir / problem_name
    vfile = features_dir / f"{problem_name}.vec"
    if not pfile.exists() or not vfile.exists():
        return None, None

    formulas = read_problem_formulas(pfile)
    with open(vfile) as vf:
        vec_lines = [line for line in vf if line.strip()]

    aligned = min(len(formulas), len(vec_lines))
    if aligned == 0:
        return None, None

    gamma_features = None
    candidates = []
    for idx in range(aligned):
        fname, role = formulas[idx]
        if role in CONJ_ROLES:
            gamma_features = parse_sparse_line(vec_lines[idx])
        elif role in AXIOM_ROLES:
            candidates.append(normalize_axiom_name(fname))

    dedup = list(dict.fromkeys(candidates))
    return gamma_features, dedup


def smoke_test():
    """
    Validate on a few proved chainy training problems.

    Expected: used axioms should score higher than unused on average.
    """
    print("=" * 70)
    print("SMOKE TEST: MASH K-NN SCORER")
    print("=" * 70)

    tables = load_tables()
    print(f"  Loaded tables: facts={len(tables['fact_names'])}, examples={len(tables['example_name_idx'])}")
    print(f"  Constants: {tables.get('constants', {})}")

    deps_file = DATASET_DIR / "deps" / "chainy_train_deps.jsonl"
    train_dir = DATASET_DIR / "chainy" / "train"
    features_dir = DATASET_DIR / "features_chainy"

    examples = []
    with open(deps_file) as f:
        for line in f:
            d = json.loads(line)
            if not d.get("proved", False):
                continue
            examples.append(d)
            if len(examples) >= 8:
                break

    print(f"\n  Testing on {len(examples)} proved chainy training problems:\n")

    total_used = 0.0
    total_unused = 0.0
    n_used = 0
    n_unused = 0

    for dep in examples:
        pname = dep["problem_name"]
        gamma, candidate_axioms = load_problem_goal_and_axioms(pname, train_dir, features_dir)
        if gamma is None or not candidate_axioms:
            print(f"  SKIP {pname}: missing aligned features/formulas")
            continue

        used = {normalize_axiom_name(a) for a in dep.get("used_axioms", [])}
        scored = score_all_axioms(candidate_axioms, gamma, tables, max_suggs=256)

        used_scores = [sc for ax, sc in scored if ax in used]
        unused_scores = [sc for ax, sc in scored if ax not in used]

        if not used_scores or not unused_scores:
            print(f"  SKIP {pname}: insufficient positives/negatives")
            continue

        avg_used = sum(used_scores) / len(used_scores)
        avg_unused = sum(unused_scores) / len(unused_scores)
        total_used += sum(used_scores)
        total_unused += sum(unused_scores)
        n_used += len(used_scores)
        n_unused += len(unused_scores)

        print(f"  {pname}:")
        print(f"    Used ({len(used_scores)}): avg score = {avg_used:.2f}")
        print(f"    Unused ({len(unused_scores)}): avg score = {avg_unused:.2f}")
        print("    Top 5 ranked:")
        for ax, sc in scored[:5]:
            mark = " *" if ax in used else ""
            print(f"      {ax}: {sc:.2f}{mark}")

    if n_used > 0 and n_unused > 0:
        g_used = total_used / n_used
        g_unused = total_unused / n_unused
        print("\n  OVERALL:")
        print(f"    Avg used score:   {g_used:.2f}")
        print(f"    Avg unused score: {g_unused:.2f}")
        if g_used > g_unused:
            print("    PASS: used axioms score higher on average")
        else:
            print("    WARN: used axioms do not score higher on average")
    else:
        print("\n  WARN: smoke test did not collect enough comparable examples")


if __name__ == "__main__":
    if "--smoke-test" in sys.argv:
        smoke_test()
    else:
        print("Usage: python3 mash_knn_scorer.py --smoke-test")
        print("Or import and call score_all_axioms(...).")
