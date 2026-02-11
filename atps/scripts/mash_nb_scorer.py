#!/usr/bin/env python3
"""
MaSh internal Naive Bayes scoring (source-faithful).

Implements the internal Isabelle/Sledgehammer MaSh path:
  - MaSh.naive_bayes
  - constants: init=30, pos=5, tau=0.2, def=-18

This scorer consumes tables created by mash_nb_build_tables.py.
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
        after = name[len("prior_"):]
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


def mash_nb_score(
    phi,
    goal_features,
    sfreq,
    tfreq,
    idf,
    extended_features=None,
    sigma1=30.0,
    sigma2=5.0,
    sigma3=0.2,
    sigma4=-18.0,
):
    """
    Source-faithful MaSh NB score (Blanchette et al. 2016, Section 3.3).

    Uses extended features F̄(φ) = F(φ) ∪ features of facts proved using φ.

    score(φ, γ) = σ₁ ln t(φ)
      + Σ_{f ∈ F(γ) ∩ F̄(φ)} w(f) · ln(σ₂ · s(φ,f) / t(φ))
      + σ₃ · Σ_{f ∈ F̄(φ) - F(γ)} w(f) · ln(1 - (s(φ,f)-1) / t(φ))
      + σ₄ · Σ_{f ∈ F(γ) - F̄(φ)} w(f)

    Args:
      phi: candidate fact name
      goal_features: iterable of (feature_idx, feature_weight)
      sfreq: dict[fact][feature] -> int
      tfreq: dict[fact] -> int
      idf: dict[feature] -> float
      extended_features: dict[fact] -> set of feature indices (F̄)
    """
    t_phi = tfreq.get(phi, 0)
    if t_phi <= 0:
        return -1e30

    t_phi_f = float(t_phi)
    s_phi = sfreq.get(phi, {})

    # F̄(φ): extended features if available, else fall back to sfreq keys
    if extended_features is not None:
        f_bar_phi = extended_features.get(phi, set())
    else:
        f_bar_phi = set(s_phi.keys())

    # Build goal feature set for set operations
    goal_set = set()
    goal_weights = {}
    for f, fw0 in goal_features:
        goal_set.add(f)
        goal_weights[f] = fw0

    shared = goal_set & f_bar_phi       # F(γ) ∩ F̄(φ)
    axiom_only = f_bar_phi - goal_set   # F̄(φ) - F(γ)
    goal_only = goal_set - f_bar_phi    # F(γ) - F̄(φ)

    # Term 1: Prior (global axiom popularity)
    score = sigma1 * math.log(t_phi_f)

    # Term 2: Shared features boost
    for f in shared:
        idf_f = idf.get(f)
        if idf_f is None:
            continue
        fw0 = goal_weights.get(f, 1.0)
        sf = s_phi.get(f, 0)
        if sf == 0:
            sf = 0.5  # Laplace smoothing
        arg = sigma2 * float(sf) / t_phi_f
        score += fw0 * idf_f * math.log(max(arg, 1e-300))

    # Term 3: Axiom-only features (slight penalty)
    term3 = 0.0
    for f in axiom_only:
        idf_f = idf.get(f)
        if idf_f is None:
            continue
        sf = s_phi.get(f, 0)
        arg = 1.0 - float(sf - 1) / t_phi_f
        term3 += idf_f * math.log(max(arg, 1e-300))
    score += sigma3 * term3

    # Term 4: Goal-only features (big penalty)
    term4 = 0.0
    for f in goal_only:
        idf_f = idf.get(f)
        if idf_f is None:
            continue
        fw0 = goal_weights.get(f, 1.0)
        term4 += fw0 * idf_f
    score += sigma4 * term4

    return score


def score_all_axioms(
    candidate_axioms,
    gamma_features,
    sfreq,
    tfreq,
    idf,
    extended_features=None,
    sigma1=30.0,
    sigma2=5.0,
    sigma3=0.2,
    sigma4=-18.0,
):
    """Score and sort candidate axioms descending by score."""
    weighted = as_weighted_features(gamma_features)
    scored = []
    for phi in candidate_axioms:
        sc = mash_nb_score(
            phi,
            weighted,
            sfreq,
            tfreq,
            idf,
            extended_features=extended_features,
            sigma1=sigma1,
            sigma2=sigma2,
            sigma3=sigma3,
            sigma4=sigma4,
        )
        scored.append((phi, sc))
    scored.sort(key=lambda x: -x[1])
    return scored


def load_tables():
    """Load MaSh tables from pickle."""
    path = MODELS_DIR / "mash_nb_tables.pkl"
    if not path.exists():
        raise FileNotFoundError(f"{path} not found. Run mash_nb_build_tables.py first.")
    with open(path, "rb") as f:
        tables = pickle.load(f)
    sfreq = tables.get("sfreq", tables.get("s", {}))
    tfreq = tables.get("tfreq", tables.get("t", {}))
    idf = tables.get("idf", tables.get("w", {}))
    extended_features = tables.get("extended_features", None)
    sigma = tables.get(
        "sigma",
        {"sigma1": 30.0, "sigma2": 5.0, "sigma3": 0.2, "sigma4": -18.0},
    )
    return sfreq, tfreq, idf, extended_features, sigma


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

    # preserve order, remove duplicates
    dedup = list(dict.fromkeys(candidates))
    return gamma_features, dedup


def smoke_test():
    """
    Validate on a few chainy training proofs.

    Expected: used axioms should score higher than unused on average.
    """
    print("=" * 70)
    print("SMOKE TEST: MASH INTERNAL NB SCORER")
    print("=" * 70)

    sfreq, tfreq, idf, extended_features, sigma = load_tables()
    print(f"  Loaded tables: tfreq={len(tfreq)} facts, idf={len(idf)} features")
    print(f"  Extended features F̄: {len(extended_features) if extended_features else 'None'}")
    print(f"  Sigma: {sigma}")

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
        scored = score_all_axioms(candidate_axioms, gamma, sfreq, tfreq, idf,
                                  extended_features=extended_features, **sigma)

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
        print("Usage: python3 mash_nb_scorer.py --smoke-test")
        print("Or import and call mash_nb_score / score_all_axioms.")
