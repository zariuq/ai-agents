#!/usr/bin/env python3
"""
PLN-style mixture-local prior + NB-likelihood selector (selection only).

Architecture (non-alias, staged):
  Stage A: build multiple local prior experts from neighbor bins
  Stage B: pool normalized local experts via evidence add (hplus semantics)
  Stage C: tensor-compose pooled prior with likelihood-only NB evidence

The ranking signal is posterior strength:
  strength = post_pos / (post_pos + post_neg)

This script is intentionally pure-Python for speed and auditability.
"""

import argparse
import json
import math
import os
import sys
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent
sys.path.insert(0, str(SCRIPT_DIR))
from mash_nb_scorer import (
    load_tables as load_nb_tables,
    mash_nb_score,
    normalize_axiom_name,
    parse_sparse_line,
    read_problem_formulas,
    score_all_axioms as score_mash_nb_all,
)

DATASET_DIR = Path("/home/zar/claude/atps/datasets/extended_mptp5k")
CHAINY_TRAIN_DIR = DATASET_DIR / "chainy" / "train"
CHAINY_VAL_DIR = DATASET_DIR / "chainy" / "val"
FEATURES_TRAIN_DIR = DATASET_DIR / "features_chainy"
FEATURES_VAL_DIR = DATASET_DIR / "features_chainy_val"
DEFAULT_DEPS_FILE = DATASET_DIR / "deps" / "pooled_train_deps_allruns.jsonl"

AXIOM_ROLES = {"axiom", "hypothesis", "definition"}
CONJ_ROLES = {"conjecture", "negated_conjecture"}


def _fmt(x):
    return f"{float(x):.8g}"


def parse_float_csv(csv_value):
    vals = []
    for raw in csv_value.split(","):
        raw = raw.strip()
        if not raw:
            continue
        vals.append(float(raw))
    return vals


def parse_int_csv(csv_value):
    vals = []
    for raw in csv_value.split(","):
        raw = raw.strip()
        if not raw:
            continue
        vals.append(int(raw))
    return vals


def normalize_to_total(pos, neg, target_total):
    """Preserve strength while setting total evidence mass."""
    if target_total <= 0.0:
        return 0.0, 0.0
    total = pos + neg
    if total <= 0.0:
        half = 0.5 * target_total
        return half, half
    s = pos / total
    return s * target_total, (1.0 - s) * target_total


def evidence_strength(pos, neg):
    total = pos + neg
    if total <= 0.0:
        return 0.5
    return pos / total


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
        if role in CONJ_ROLES:
            gamma_features = parse_sparse_line(vec_lines[idx])
        elif role in AXIOM_ROLES:
            norm = normalize_axiom_name(fname)
            if norm not in axiom_map:
                axiom_map[norm] = fname

    return gamma_features, axiom_map


def load_training_index(deps_file):
    """
    Build training examples with an inverted feature index for fast overlap lookup.
    """
    deps_by_name = {}
    with open(deps_file) as f:
        for line in f:
            rec = json.loads(line)
            pname = rec.get("problem_name")
            used = rec.get("used_axioms", [])
            if not pname or not used:
                continue
            deps_by_name.setdefault(pname, set()).update(normalize_axiom_name(a) for a in used)

    train_examples = []
    feat_to_examples = {}

    for pname, used_set in deps_by_name.items():
        pfile = CHAINY_TRAIN_DIR / pname
        vec_file = FEATURES_TRAIN_DIR / f"{pname}.vec"
        if not pfile.exists() or not vec_file.exists():
            continue

        formulas = read_problem_formulas(pfile)
        with open(vec_file) as vf:
            vec_lines = [line for line in vf if line.strip()]
        aligned = min(len(formulas), len(vec_lines))
        if aligned == 0:
            continue

        gamma = None
        for idx in range(aligned):
            _fname, role = formulas[idx]
            if role in CONJ_ROLES:
                gamma = parse_sparse_line(vec_lines[idx])
                break
        if not gamma:
            continue

        ex_idx = len(train_examples)
        train_examples.append(
            {
                "problem": pname,
                "features": gamma,
                "used_axioms": used_set,
            }
        )
        for feat in gamma:
            feat_to_examples.setdefault(feat, []).append(ex_idx)

    return train_examples, feat_to_examples


def find_neighbors(goal_features, feat_to_examples, idf, overlap_power=1.0, max_neighbors=256):
    """
    Compute weighted overlap neighbors using feature postings.
    Returns list[(example_idx, overlap_score)] sorted descending.
    """
    overlaps = {}
    for feat in goal_features:
        posting = feat_to_examples.get(feat)
        if not posting:
            continue
        base_w = float(idf.get(feat, 1.0))
        w = base_w ** overlap_power if overlap_power != 1.0 else base_w
        for ex_idx in posting:
            overlaps[ex_idx] = overlaps.get(ex_idx, 0.0) + w

    ranked = [(idx, ov) for idx, ov in overlaps.items() if ov > 0.0]
    ranked.sort(key=lambda x: -x[1])
    return ranked[:max_neighbors]


def build_bin_slices(bin_edges, neighbors):
    """
    Interpret bin_edges as cumulative cutoffs and return disjoint slices.
    Example: [4,16,64] -> [0:4], [4:16], [16:64]
    """
    slices = []
    start = 0
    n = len(neighbors)
    for edge in bin_edges:
        stop = min(edge, n)
        if stop > start:
            slices.append((start, stop))
        start = stop
    if start < n:
        slices.append((start, n))
    return slices


def local_prior_by_mixture_bins(
    candidates,
    train_examples,
    neighbors,
    bin_edges,
    bin_lambdas,
    local_total_scale,
    sim_kappa,
    neg_weight,
    alpha,
    beta,
):
    """
    Stage A + B:
      - Build local experts from bins
      - Pool normalized experts via evidence addition
    """
    candidate_set = set(candidates)
    bin_ranges = build_bin_slices(bin_edges, neighbors)

    # Extend lambdas if needed.
    if not bin_lambdas:
        bin_lambdas = [1.0]
    if len(bin_lambdas) < len(bin_ranges):
        bin_lambdas = bin_lambdas + [bin_lambdas[-1]] * (len(bin_ranges) - len(bin_lambdas))

    # Precompute per-bin positive masses and total similarity mass.
    per_bin = []
    for b_idx, (start, stop) in enumerate(bin_ranges):
        pos_mass = {}
        total_mass = 0.0
        for n_idx in range(start, stop):
            ex_idx, overlap = neighbors[n_idx]
            sim = overlap / (overlap + sim_kappa) if sim_kappa > 0.0 else 1.0
            if sim <= 0.0:
                continue
            total_mass += sim
            used = train_examples[ex_idx]["used_axioms"]
            for ax in used:
                if ax in candidate_set:
                    pos_mass[ax] = pos_mass.get(ax, 0.0) + sim

        t_bin = local_total_scale * bin_lambdas[b_idx] * total_mass
        per_bin.append(
            {
                "pos_mass": pos_mass,
                "total_mass": total_mass,
                "t_bin": t_bin,
                "start": start,
                "stop": stop,
            }
        )

    pooled_prior = {}
    for ax in candidates:
        p_sum = 0.0
        n_sum = 0.0
        for b in per_bin:
            t_bin = b["t_bin"]
            if t_bin <= 0.0:
                continue
            pos_raw = b["pos_mass"].get(ax, 0.0)
            neg_raw = max(b["total_mass"] - pos_raw, 0.0) * neg_weight

            pos = pos_raw + alpha
            neg = neg_raw + beta
            np, nn = normalize_to_total(pos, neg, t_bin)
            p_sum += np
            n_sum += nn

        pooled_prior[ax] = (p_sum, n_sum)

    return pooled_prior, per_bin


def add_global_prior(
    pooled_prior,
    candidates,
    tfreq,
    t_global,
    global_neg_prior,
    global_alpha,
):
    """Optional global prior expert, normalized to t_global per candidate."""
    if t_global <= 0.0:
        return pooled_prior

    out = {}
    for ax in candidates:
        p0, n0 = pooled_prior.get(ax, (0.0, 0.0))
        gpos = float(tfreq.get(ax, 0.0)) + global_alpha
        gneg = global_neg_prior
        gp, gn = normalize_to_total(gpos, gneg, t_global)
        out[ax] = (p0 + gp, n0 + gn)
    return out


def likelihood_evidence_by_nb_scores(
    candidates,
    goal_features,
    sfreq,
    tfreq,
    idf,
    extended_features,
    sigma,
    t_lik,
    iqr_target,
    score_clip,
):
    """
    Stage C (likelihood only):
      - Use MaSh NB score with prior term removed (sigma1 = 0)
      - Robust per-problem affine scaling
      - Convert to odds evidence and normalize to fixed total t_lik
    """
    weighted_goal = [(f, 1.0) for f in goal_features]
    raw = {}
    for ax in candidates:
        raw[ax] = mash_nb_score(
            ax,
            weighted_goal,
            sfreq,
            tfreq,
            idf,
            extended_features=extended_features,
            sigma1=0.0,
            sigma2=float(sigma.get("sigma2", 5.0)),
            sigma3=float(sigma.get("sigma3", 0.2)),
            sigma4=float(sigma.get("sigma4", -18.0)),
        )

    finite_vals = sorted(v for v in raw.values() if v > -1e29)
    if finite_vals:
        n = len(finite_vals)
        median = finite_vals[n // 2]
        q1 = finite_vals[n // 4]
        q3 = finite_vals[(3 * n) // 4]
        iqr = q3 - q1
        scale = (iqr_target / iqr) if iqr > 0.0 else 1.0
        shift = median
    else:
        scale = 1.0
        shift = 0.0

    out = {}
    for ax in candidates:
        rv = raw[ax]
        if rv <= -1e29:
            scaled = -score_clip
        else:
            scaled = (rv - shift) * scale
            if scaled > score_clip:
                scaled = score_clip
            elif scaled < -score_clip:
                scaled = -score_clip

        odds = math.exp(scaled)
        s = odds / (odds + 1.0)
        lp = s * t_lik
        ln = (1.0 - s) * t_lik
        out[ax] = (lp, ln, rv, scaled)

    return out


def score_problem(
    pname,
    gamma_features,
    candidates,
    train_examples,
    feat_to_examples,
    nb_tables,
    args,
):
    sfreq, tfreq, idf, extended_features, sigma = nb_tables

    # Optional prefilter (ranking-only speedup).
    if len(candidates) > args.prefilter_k:
        pre_scored = score_mash_nb_all(
            candidates,
            gamma_features,
            sfreq,
            tfreq,
            idf,
            extended_features=extended_features,
            **sigma,
        )
        candidates = [ax for ax, _ in pre_scored[: args.prefilter_k]]

    # Stage A: neighbors and local experts.
    neighbors = find_neighbors(
        goal_features=gamma_features,
        feat_to_examples=feat_to_examples,
        idf=idf,
        overlap_power=args.overlap_power,
        max_neighbors=args.max_neighbors,
    )

    pooled_prior, bin_info = local_prior_by_mixture_bins(
        candidates=candidates,
        train_examples=train_examples,
        neighbors=neighbors,
        bin_edges=args.bin_edges,
        bin_lambdas=args.bin_lambdas,
        local_total_scale=args.local_total_scale,
        sim_kappa=args.sim_kappa,
        neg_weight=args.neg_weight,
        alpha=args.local_alpha,
        beta=args.local_beta,
    )

    # Optional global prior expert.
    pooled_prior = add_global_prior(
        pooled_prior=pooled_prior,
        candidates=candidates,
        tfreq=tfreq,
        t_global=args.t_global,
        global_neg_prior=args.global_neg_prior,
        global_alpha=args.global_alpha,
    )

    # Stage C: likelihood-only NB evidence.
    lik = likelihood_evidence_by_nb_scores(
        candidates=candidates,
        goal_features=gamma_features,
        sfreq=sfreq,
        tfreq=tfreq,
        idf=idf,
        extended_features=extended_features,
        sigma=sigma,
        t_lik=args.t_lik,
        iqr_target=args.lik_iqr_target,
        score_clip=args.lik_score_clip,
    )

    scored = []
    for ax in candidates:
        ppos, pneg = pooled_prior.get(ax, (0.0, 0.0))
        # Fallback to neutral prior if no evidence mass arrived.
        if (ppos + pneg) <= 0.0:
            ppos, pneg = 0.5, 0.5

        lpos, lneg, raw_nb, scaled_nb = lik[ax]

        # Tensor composition.
        post_pos = ppos * lpos
        post_neg = pneg * lneg
        s = evidence_strength(post_pos, post_neg)

        # Confidence-style support diagnostic (not ranking target by default).
        support = (ppos + pneg) / ((ppos + pneg) + args.support_kappa)

        if args.rank_mode == "strength_support":
            rank_score = s + args.support_tiebreak * support
        else:
            rank_score = s

        scored.append((ax, rank_score, s, support, raw_nb, scaled_nb))

    scored.sort(key=lambda x: -x[1])

    debug = {
        "neighbor_count": len(neighbors),
        "bin_info": [
            {
                "range": [b["start"], b["stop"]],
                "total_mass": b["total_mass"],
                "t_bin": b["t_bin"],
            }
            for b in bin_info
        ],
    }
    return scored, debug


def main():
    parser = argparse.ArgumentParser(
        description="PLN-style mixture-local prior + NB-likelihood selector"
    )
    parser.add_argument("--split", choices=["train", "val"], default="val")
    parser.add_argument("--top-k", type=int, default=256)
    parser.add_argument("--output", required=True, help="Output selections JSON")
    parser.add_argument("--max-problems", type=int, default=None)
    parser.add_argument("--problems", nargs="*", help="Specific problem names to process")
    parser.add_argument("--smoke-test", action="store_true")

    parser.add_argument("--nb-tables", type=str, default=None,
                        help="Optional path to MaSh NB tables pickle")
    parser.add_argument("--deps-file", type=str, default=str(DEFAULT_DEPS_FILE),
                        help="JSONL dependencies file for local prior experts")

    parser.add_argument("--prefilter-k", type=int, default=1536)
    parser.add_argument("--max-neighbors", type=int, default=256)
    parser.add_argument("--bin-edges", type=str, default="4,16,64,256",
                        help="Cumulative bin edges, e.g. 4,16,64,256")
    parser.add_argument("--bin-lambdas", type=str, default="1,1,1,1",
                        help="Per-bin reliability multipliers")
    parser.add_argument("--local-total-scale", type=float, default=1.0,
                        help="Global scale for local bin totals")
    parser.add_argument("--overlap-power", type=float, default=1.0,
                        help="Power on IDF overlap contribution")
    parser.add_argument("--sim-kappa", type=float, default=5.0,
                        help="Similarity map: sim=ov/(ov+sim_kappa)")
    parser.add_argument("--neg-weight", type=float, default=0.08,
                        help="Weak negative evidence factor for local bins")
    parser.add_argument("--local-alpha", type=float, default=0.5)
    parser.add_argument("--local-beta", type=float, default=0.5)

    parser.add_argument("--t-global", type=float, default=1.0,
                        help="Normalized total for optional global prior expert")
    parser.add_argument("--global-neg-prior", type=float, default=1000.0)
    parser.add_argument("--global-alpha", type=float, default=1.0)

    parser.add_argument("--t-lik", type=float, default=100.0,
                        help="Normalized likelihood total")
    parser.add_argument("--lik-iqr-target", type=float, default=4.0,
                        help="IQR target for per-problem affine score scaling")
    parser.add_argument("--lik-score-clip", type=float, default=20.0)

    parser.add_argument("--rank-mode", choices=["strength", "strength_support"],
                        default="strength")
    parser.add_argument("--support-kappa", type=float, default=100.0)
    parser.add_argument("--support-tiebreak", type=float, default=1e-6)
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()

    if args.smoke_test:
        args.max_problems = 5
        args.split = "val"

    args.bin_edges = parse_int_csv(args.bin_edges)
    args.bin_lambdas = parse_float_csv(args.bin_lambdas)
    if not args.bin_edges:
        raise ValueError("bin-edges cannot be empty")
    if not args.bin_lambdas:
        raise ValueError("bin-lambdas cannot be empty")

    deps_file = Path(args.deps_file)
    if not deps_file.exists():
        raise FileNotFoundError(f"deps file not found: {deps_file}")

    sfreq, tfreq, idf, extended_features, sigma = load_nb_tables(args.nb_tables)
    nb_tables = (sfreq, tfreq, idf, extended_features, sigma)
    print(f"Loaded NB tables: {len(tfreq)} axioms, {len(idf)} features")

    print(f"Loading local-prior index from: {deps_file}")
    t_index0 = time.time()
    train_examples, feat_to_examples = load_training_index(deps_file)
    print(
        f"Loaded {len(train_examples)} training examples, "
        f"{len(feat_to_examples)} indexed features ({time.time() - t_index0:.1f}s)"
    )

    if args.split == "train":
        problems_dir = CHAINY_TRAIN_DIR
        features_dir = FEATURES_TRAIN_DIR
    else:
        problems_dir = CHAINY_VAL_DIR
        features_dir = FEATURES_VAL_DIR

    if args.problems:
        problems = sorted(args.problems)
    else:
        problems = sorted(p.name for p in problems_dir.iterdir() if p.is_file())
    if args.max_problems:
        problems = problems[: args.max_problems]

    print(
        f"Split: {args.split}, problems: {len(problems)}, top-k: {args.top_k}, "
        f"prefilter-k: {args.prefilter_k}"
    )
    print(
        f"Bins: edges={args.bin_edges}, lambdas={args.bin_lambdas}, "
        f"local-scale={_fmt(args.local_total_scale)}, neg-weight={_fmt(args.neg_weight)}"
    )

    selections = {}
    t0 = time.time()
    no_features = 0
    failures = 0

    for i, pname in enumerate(problems):
        if i == 0 or (i + 1) % 25 == 0:
            print(f"  {i+1}/{len(problems)} ({time.time()-t0:.0f}s, failures: {failures})", flush=True)

        pfile = problems_dir / pname
        gamma_features, axiom_map = load_problem_features(pname, pfile, features_dir)
        if gamma_features is None or not axiom_map:
            no_features += 1
            selections[pname] = []
            continue

        candidates = list(axiom_map.keys())
        try:
            scored, debug = score_problem(
                pname=pname,
                gamma_features=gamma_features,
                candidates=candidates,
                train_examples=train_examples,
                feat_to_examples=feat_to_examples,
                nb_tables=nb_tables,
                args=args,
            )
        except Exception as e:
            failures += 1
            print(f"  WARN {pname}: {e}")
            selections[pname] = []
            continue

        selections[pname] = [axiom_map[ax] for ax, *_ in scored[: args.top_k]]

        if args.verbose and i < 3:
            top_dbg = scored[:5]
            print(f"    {pname}: neighbors={debug['neighbor_count']} top5={[(x[0], _fmt(x[2]), _fmt(x[3])) for x in top_dbg]}")

    out_path = Path(args.output)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(selections, f)

    elapsed = time.time() - t0
    print(
        f"Done in {elapsed:.0f}s. no_features={no_features}, failures={failures}, "
        f"saved={out_path}"
    )


if __name__ == "__main__":
    main()
