#!/usr/bin/env python3
"""
Build source-faithful MaSh internal Naive Bayes tables.

This follows Isabelle's internal implementation in:
  src/HOL/Tools/Sledgehammer/sledgehammer_mash.ML
    - MaSh.learn_facts
    - MaSh.naive_bayes

Key constants and mechanics mirrored from Isabelle:
  nb_def_prior_weight = 1000
  init_val = 30, pos_weight = 5, tau = 0.2, def_val = -18

Differences vs the previous script:
  - Uses BOTH bushy + chainy dependency files.
  - Preserves duplicate proof events across files.
  - Stores tfreq/sfreq/dffreq tables (Isabelle-style), not only s/t.
  - Builds a proof DAG (dep -> theorem) and one-hop extended features F̄ for logging.
"""

import json
import math
import pickle
import re
from collections import Counter, defaultdict
from pathlib import Path

DATASET_DIR = Path("/home/zar/claude/atps/datasets/extended_mptp5k")
CHAINY_TRAIN_DIR = DATASET_DIR / "chainy" / "train"
FEATURES_DIR = DATASET_DIR / "features_chainy"
DEPS_FILES = [
    DATASET_DIR / "deps" / "bushy_train_deps.jsonl",
    DATASET_DIR / "deps" / "chainy_train_deps.jsonl",
]
MODELS_DIR = DATASET_DIR / "models"
OUT_TABLES = MODELS_DIR / "mash_nb_tables.pkl"
OUT_META = MODELS_DIR / "mash_nb_tables_meta.json"

FORMULA_RE = re.compile(r"^(fof|cnf)\(([^,]+),\s*([^,]+),")
AXIOM_ROLES = {"axiom", "hypothesis", "definition"}
CONJ_ROLES = {"conjecture", "negated_conjecture"}

# Constants from Isabelle's MaSh.learn_facts / MaSh.naive_bayes
NB_DEF_PRIOR_WEIGHT = 1000
SIGMA = {"sigma1": 30.0, "sigma2": 5.0, "sigma3": 0.2, "sigma4": -18.0}


def normalize_name(name):
    """Normalize prior_<article>__<fact> to <fact>."""
    if name.startswith("prior_"):
        after = name[len("prior_"):]
        parts = after.split("__", 1)
        if len(parts) == 2:
            return parts[1]
    return name


def parse_sparse_line(line):
    """Parse 'idx:val idx:val ...' into a set of non-zero feature indices."""
    features = set()
    for item in line.strip().split():
        if ":" not in item:
            continue
        idx, val = item.split(":", 1)
        if float(val) != 0.0:
            features.add(int(idx))
    return features


def read_problem_formulas(problem_file):
    """Return ordered list of (name, role) for all fof/cnf formulas."""
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


def parse_training_features():
    """
    Parse all chainy training problems and associated .vec files.

    Returns:
      fact_features: fact -> union(feature indices)
      problem_conj_features: problem_name -> conjecture feature set
      problem_conj_name: problem_name -> normalized conjecture name
    """
    fact_features = defaultdict(set)
    problem_conj_features = {}
    problem_conj_name = {}

    problem_files = sorted([p for p in CHAINY_TRAIN_DIR.iterdir() if p.is_file()])
    n_skipped = 0

    for i, pfile in enumerate(problem_files):
        if (i + 1) % 500 == 0:
            print(f"  parsed {i+1}/{len(problem_files)} training problems...", flush=True)

        pname = pfile.name
        vec_file = FEATURES_DIR / f"{pname}.vec"
        if not vec_file.exists():
            n_skipped += 1
            continue

        formulas = read_problem_formulas(pfile)
        with open(vec_file) as vf:
            vec_lines = [line for line in vf if line.strip()]

        aligned = min(len(formulas), len(vec_lines))
        if aligned == 0:
            n_skipped += 1
            continue

        conj_features = None
        conj_name = None
        for idx in range(aligned):
            fname, role = formulas[idx]
            feats = parse_sparse_line(vec_lines[idx])
            if role in AXIOM_ROLES:
                fact_features[normalize_name(fname)] |= feats
            elif role in CONJ_ROLES:
                conj_features = feats
                conj_name = normalize_name(fname)
                fact_features[conj_name] |= feats

        if conj_features is not None and conj_name is not None:
            problem_conj_features[pname] = conj_features
            problem_conj_name[pname] = conj_name

    return fact_features, problem_conj_features, problem_conj_name, len(problem_files), n_skipped


def load_dependency_events(problem_conj_features, problem_conj_name):
    """
    Load dependency events from both bushy and chainy deps files.

    Each proved row contributes one event:
      event = (problem_name, theorem_name, conjecture_features, normalized_deps, source_file)
    """
    events = []
    by_problem = Counter()
    file_counts = {}
    n_total_rows = 0
    n_proved = 0
    n_matched = 0

    for dep_file in DEPS_FILES:
        file_events = 0
        with open(dep_file) as f:
            for line in f:
                n_total_rows += 1
                dep = json.loads(line)
                if not dep.get("proved", False):
                    continue
                n_proved += 1
                pname = dep["problem_name"]
                if pname not in problem_conj_features or pname not in problem_conj_name:
                    continue
                n_matched += 1
                theorem = problem_conj_name[pname]
                gamma_features = problem_conj_features[pname]
                deps = [normalize_name(a) for a in dep.get("used_axioms", [])]
                events.append((pname, theorem, gamma_features, deps, dep_file.name))
                by_problem[pname] += 1
                file_events += 1
        file_counts[dep_file.name] = file_events

    duplicates = sum(1 for _, c in by_problem.items() if c > 1)
    return events, {
        "rows_total": n_total_rows,
        "proved_total": n_proved,
        "proved_matched": n_matched,
        "events_by_file": file_counts,
        "events_total": len(events),
        "unique_problems": len(by_problem),
        "duplicate_problem_events": duplicates,
    }


def main():
    MODELS_DIR.mkdir(parents=True, exist_ok=True)

    print("=" * 70)
    print("BUILDING SOURCE-FAITHFUL MASH NB TABLES")
    print("=" * 70)

    print("\nStep 1: Parse chainy training formulas + features...", flush=True)
    (
        fact_features,
        problem_conj_features,
        problem_conj_name,
        n_problem_files,
        n_skipped,
    ) = parse_training_features()
    print(f"  training problems parsed: {n_problem_files} ({n_skipped} skipped)")
    print(f"  facts with features: {len(fact_features)}")
    print(f"  problems with conjecture features: {len(problem_conj_features)}")

    print("\nStep 2: Load bushy+chainy dependency events...", flush=True)
    events, event_meta = load_dependency_events(problem_conj_features, problem_conj_name)
    print(f"  events total: {event_meta['events_total']}")
    print(f"  unique problems with events: {event_meta['unique_problems']}")
    print(f"  duplicate problem events: {event_meta['duplicate_problem_events']}")
    for fname, cnt in event_meta["events_by_file"].items():
        print(f"    {fname}: {cnt} events")

    print("\nStep 3: Initialize Isabelle-style tfreq/sfreq...", flush=True)
    tfreq = defaultdict(int)                       # fact -> int
    sfreq = defaultdict(lambda: defaultdict(int))  # fact -> feature -> int

    # One self-prior update per known fact (Isabelle: add_th nb_def_prior_weight th).
    for fact, feats in fact_features.items():
        tfreq[fact] += NB_DEF_PRIOR_WEIGHT
        for feat in feats:
            sfreq[fact][feat] += NB_DEF_PRIOR_WEIGHT

    print(f"  initialized facts: {len(tfreq)}")

    print("\nStep 4: Apply dependency events (duplicates preserved)...", flush=True)
    dep_to_theorems = defaultdict(set)
    theorem_to_deps = defaultdict(list)
    unseen_dep_facts = 0

    for idx, (pname, theorem, gamma_features, deps, _src) in enumerate(events):
        if (idx + 1) % 500 == 0:
            print(f"  applied {idx+1}/{len(events)} events...", flush=True)

        theorem_to_deps[theorem].append(list(deps))
        for dep in deps:
            dep_to_theorems[dep].add(theorem)

            # Robustness: include dependencies absent from feature extraction.
            if dep not in tfreq:
                tfreq[dep] += NB_DEF_PRIOR_WEIGHT
                unseen_dep_facts += 1

            tfreq[dep] += 1
            sf = sfreq[dep]
            for feat in gamma_features:
                sf[feat] += 1

    print(f"  facts with tfreq entries: {len(tfreq)}")
    print(f"  facts with sfreq entries: {len(sfreq)}")
    if unseen_dep_facts > 0:
        print(f"  WARNING: unseen deps added with empty features: {unseen_dep_facts}")

    print("\nStep 5: Build extended features F̄(φ) = F(φ) ∪ features of theorems proved using φ...", flush=True)
    extended_features = {}
    for fact, feats in fact_features.items():
        ext = set(feats)
        for theorem in dep_to_theorems.get(fact, ()):
            ext |= fact_features.get(theorem, set())
        extended_features[fact] = ext

    n_extended = sum(1 for f in extended_features if len(extended_features[f]) > len(fact_features.get(f, set())))
    print(f"  extended feature sets built: {len(extended_features)}")
    print(f"  facts where F̄ > F: {n_extended}")

    print("\nStep 6: Compute IDF from F̄ (paper p.226: w(f,Φ) = ln(|Φ|/|{φ: f∈F̄(φ)}|))...", flush=True)
    dffreq = defaultdict(int)
    for fact, ext_feats in extended_features.items():
        for feat in ext_feats:
            dffreq[feat] += 1

    num_facts = len(tfreq)
    idf = {}
    for feat, df in dffreq.items():
        if df > 0:
            idf[feat] = math.log(num_facts / df)

    print(f"  num_facts: {num_facts}")
    print(f"  num_features (idf from F̄): {len(idf)}")
    if idf:
        print(f"  idf range: [{min(idf.values()):.3f}, {max(idf.values()):.3f}]")

    print("\nStep 7: Save tables + metadata...", flush=True)
    sfreq_dict = {fact: dict(feats) for fact, feats in sfreq.items()}
    fact_features_dict = {fact: set(feats) for fact, feats in fact_features.items()}
    extended_features_dict = {fact: set(feats) for fact, feats in extended_features.items()}
    dep_to_theorems_dict = {dep: sorted(list(ths)) for dep, ths in dep_to_theorems.items()}

    tables = {
        "tfreq": dict(tfreq),
        "sfreq": sfreq_dict,
        "dffreq": dict(dffreq),
        "idf": idf,
        "fact_features": fact_features_dict,
        "extended_features": extended_features_dict,
        "dep_to_theorems": dep_to_theorems_dict,
        "sigma": SIGMA,
        "nb_def_prior_weight": NB_DEF_PRIOR_WEIGHT,
        # Backward-compat aliases for older scripts.
        "t": dict(tfreq),
        "s": sfreq_dict,
        "w": idf,
        "axiom_features": fact_features_dict,
    }

    meta = {
        "builder": "mash_nb_build_tables.py",
        "source_style": "isabelle_internal_nb",
        "deps_files": [p.name for p in DEPS_FILES],
        "event_meta": event_meta,
        "training_problems_total": n_problem_files,
        "training_problems_skipped": n_skipped,
        "facts_with_features": len(fact_features),
        "num_facts_tfreq": len(tfreq),
        "num_features_idf": len(idf),
        "num_dep_edges": sum(len(v) for v in dep_to_theorems.values()),
        "constants": {
            "nb_def_prior_weight": NB_DEF_PRIOR_WEIGHT,
            "sigma1_init_val": SIGMA["sigma1"],
            "sigma2_pos_weight": SIGMA["sigma2"],
            "sigma3_tau": SIGMA["sigma3"],
            "sigma4_def_val": SIGMA["sigma4"],
        },
    }

    with open(OUT_TABLES, "wb") as f:
        pickle.dump(tables, f)
    with open(OUT_META, "w") as f:
        json.dump(meta, f, indent=2, sort_keys=True)

    print(f"  tables: {OUT_TABLES} ({OUT_TABLES.stat().st_size / (1024 * 1024):.1f} MB)")
    print(f"  meta:   {OUT_META}")

    print("\n" + "=" * 70)
    print("MASH NB TABLE BUILD COMPLETE")
    print("=" * 70)
    print(f"  tfreq facts: {len(tfreq)}")
    print(f"  sfreq entries: {sum(len(v) for v in sfreq_dict.values())}")
    print(f"  dffreq entries: {len(dffreq)}")
    print(f"  next: python3 scripts/mash_nb_scorer.py --smoke-test")


if __name__ == "__main__":
    main()
