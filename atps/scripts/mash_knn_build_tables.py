#!/usr/bin/env python3
"""
Build MaSh/Mizar-style k-NN tables for premise selection.

Algorithmic source:
  - Isabelle Sledgehammer MaSh internal k-NN (sledgehammer_mash.ML)
  - Mizar40/Mizar60 practice of training from large proof-dependency data

This builder intentionally preserves duplicate proof events from both deps files,
so multiple proofs for the same theorem contribute multiple k-NN examples.
"""

import json
import math
import pickle
import re
import argparse
from collections import Counter, defaultdict
from pathlib import Path

DATASET_DIR = Path("/home/zar/claude/atps/datasets/extended_mptp5k")
CHAINY_TRAIN_DIR = DATASET_DIR / "chainy" / "train"
FEATURES_DIR = DATASET_DIR / "features_chainy"
DEFAULT_DEPS_FILES = [
    DATASET_DIR / "deps" / "bushy_train_deps.jsonl",
    DATASET_DIR / "deps" / "chainy_train_deps.jsonl",
]
MODELS_DIR = DATASET_DIR / "models"
DEFAULT_OUT_TABLES = MODELS_DIR / "mash_knn_tables.pkl"
DEFAULT_OUT_META = MODELS_DIR / "mash_knn_tables_meta.json"

FORMULA_RE = re.compile(r"^(fof|cnf)\(([^,]+),\s*([^,]+),")
AXIOM_ROLES = {"axiom", "hypothesis", "definition"}
CONJ_ROLES = {"conjecture", "negated_conjecture"}

# Constants from Isabelle MaSh k-NN internals.
KNN_CONSTANTS = {
    "tau_power": 6.0,
    "deps_factor": 2.7,
    "initial_k": 0,
    "age_init": 500000000.0,
    "age_step": 10000.0,
}


def normalize_name(name):
    """Normalize prior_<article>__<fact> to <fact>."""
    if name.startswith("prior_"):
        after = name[len("prior_") :]
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
    Parse chainy training formulas and .vec feature files.

    Returns:
      fact_features: fact -> set(feature idx)
      problem_conj_name: problem_name -> normalized conjecture name
      problem_conj_features: problem_name -> set(feature idx)
    """
    fact_features = defaultdict(set)
    problem_conj_name = {}
    problem_conj_features = {}

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

        conj_name = None
        conj_features = None
        for idx in range(aligned):
            name, role = formulas[idx]
            feats = parse_sparse_line(vec_lines[idx])
            if role in AXIOM_ROLES:
                fact_features[normalize_name(name)] |= feats
            elif role in CONJ_ROLES:
                conj_name = normalize_name(name)
                conj_features = feats
                fact_features[conj_name] |= feats

        if conj_name is not None and conj_features is not None:
            problem_conj_name[pname] = conj_name
            problem_conj_features[pname] = conj_features

    return fact_features, problem_conj_name, problem_conj_features, len(problem_files), n_skipped


def load_dependency_events(problem_conj_name, deps_files):
    """
    Load proved dependency events from both deps files, preserving duplicates.

    Returns events list entries:
      (problem_name, theorem_name, normalized_deps, source_file)
    """
    events = []
    by_problem = Counter()
    file_counts = {}
    n_total_rows = 0
    n_proved = 0
    n_matched = 0

    for dep_file in deps_files:
        file_events = 0
        with open(dep_file) as f:
            for line in f:
                n_total_rows += 1
                dep = json.loads(line)
                if not dep.get("proved", False):
                    continue
                n_proved += 1

                pname = dep["problem_name"]
                theorem = problem_conj_name.get(pname)
                if theorem is None:
                    continue

                n_matched += 1
                used = [normalize_name(a) for a in dep.get("used_axioms", [])]
                events.append((pname, theorem, used, dep_file.name))
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


def dedup_keep_order(items):
    seen = set()
    out = []
    for x in items:
        if x in seen:
            continue
        seen.add(x)
        out.append(x)
    return out


def main():
    parser = argparse.ArgumentParser(description="Build MaSh k-NN tables")
    parser.add_argument(
        "--deps-files",
        nargs="+",
        default=[str(p) for p in DEFAULT_DEPS_FILES],
        help="Dependency JSONL files (duplicates across files are preserved)",
    )
    parser.add_argument(
        "--out-tables",
        default=str(DEFAULT_OUT_TABLES),
        help="Output pickle path for k-NN tables",
    )
    parser.add_argument(
        "--out-meta",
        default=str(DEFAULT_OUT_META),
        help="Output JSON path for k-NN metadata",
    )
    args = parser.parse_args()

    deps_files = [Path(p) for p in args.deps_files]
    missing = [str(p) for p in deps_files if not p.exists()]
    if missing:
        raise FileNotFoundError(f"Missing deps files: {missing}")

    out_tables = Path(args.out_tables)
    out_meta = Path(args.out_meta)
    out_tables.parent.mkdir(parents=True, exist_ok=True)
    out_meta.parent.mkdir(parents=True, exist_ok=True)
    MODELS_DIR.mkdir(parents=True, exist_ok=True)

    print("=" * 70)
    print("BUILDING MASH K-NN TABLES")
    print("=" * 70)

    print("\nStep 1: Parse chainy training formulas + features...", flush=True)
    (
        fact_features,
        problem_conj_name,
        _problem_conj_features,
        n_problem_files,
        n_skipped,
    ) = parse_training_features()
    print(f"  training problems parsed: {n_problem_files} ({n_skipped} skipped)")
    print(f"  facts with features: {len(fact_features)}")

    print("\nStep 2: Load bushy+chainy dependency events...", flush=True)
    events, event_meta = load_dependency_events(problem_conj_name, deps_files)
    print(f"  events total: {event_meta['events_total']}")
    print(f"  unique problems with events: {event_meta['unique_problems']}")
    print(f"  duplicate problem events: {event_meta['duplicate_problem_events']}")
    for fname, cnt in event_meta["events_by_file"].items():
        print(f"    {fname}: {cnt} events")

    print("\nStep 3: Build fact universe, extended features F̄, and IDF...", flush=True)
    all_facts = set(fact_features.keys())
    dep_to_theorems = defaultdict(set)
    for _pname, theorem, deps, _src in events:
        all_facts.add(theorem)
        all_facts.update(deps)
        for dep in deps:
            dep_to_theorems[dep].add(theorem)

    fact_names = sorted(all_facts)
    fact_index = {name: i for i, name in enumerate(fact_names)}

    # Build F̄(φ) = F(φ) ∪ features of theorems proved using φ
    extended_features = {}
    for fact in fact_names:
        ext = set(fact_features.get(fact, set()))
        for theorem in dep_to_theorems.get(fact, ()):
            ext |= fact_features.get(theorem, set())
        extended_features[fact] = ext

    n_extended = sum(1 for f in fact_names if len(extended_features[f]) > len(fact_features.get(f, set())))
    print(f"  facts where F̄ > F: {n_extended}")

    # IDF from F̄ (paper p.226: w(f,Φ) = ln(|Φ|/|{φ: f∈F̄(φ)}|))
    dffreq = defaultdict(int)
    for fact in fact_names:
        for feat in extended_features.get(fact, set()):
            dffreq[feat] += 1

    num_facts = len(fact_names)
    idf = {}
    for feat, df in dffreq.items():
        if df > 0:
            idf[feat] = math.log(num_facts / df)

    print(f"  num facts: {num_facts}")
    print(f"  num features (idf from F̄): {len(dffreq)}")

    print("\nStep 4: Build k-NN learn examples (duplicates preserved)...", flush=True)
    theorem_dep_events = defaultdict(list)
    for _pname, theorem, deps, _src in events:
        theorem_dep_events[theorem].append(dedup_keep_order(deps))

    example_name_idx = []
    example_feat_idxs = []
    example_dep_idxs = []

    # Each fact gets at least one example; facts with multiple proofs add extra examples.
    for i, fact in enumerate(fact_names):
        if (i + 1) % 2000 == 0:
            print(f"  built examples for {i+1}/{len(fact_names)} facts...", flush=True)

        feats = sorted(fact_features.get(fact, set()))
        dep_lists = theorem_dep_events.get(fact)

        if dep_lists:
            for deps in dep_lists:
                dep_idxs = [fact_index[d] for d in deps if d in fact_index]
                example_name_idx.append(fact_index[fact])
                example_feat_idxs.append(feats)
                example_dep_idxs.append(dep_idxs)
        else:
            example_name_idx.append(fact_index[fact])
            example_feat_idxs.append(feats)
            example_dep_idxs.append([])

    print(f"  examples total: {len(example_name_idx)}")
    print(f"  examples from duplicate proofs: {len(example_name_idx) - len(fact_names)}")

    print("\nStep 5: Build feature -> example inverted index...", flush=True)
    feat_examples = defaultdict(list)
    for ex_idx, feats in enumerate(example_feat_idxs):
        for feat in feats:
            feat_examples[feat].append(ex_idx)

    print(f"  inverted-index features: {len(feat_examples)}")

    print("\nStep 6: Save tables + metadata...", flush=True)
    tables = {
        "fact_names": fact_names,
        "fact_index": fact_index,
        "dffreq": dict(dffreq),
        "idf": idf,
        "example_name_idx": example_name_idx,
        "example_feat_idxs": example_feat_idxs,
        "example_dep_idxs": example_dep_idxs,
        "feat_examples": {feat: exs for feat, exs in feat_examples.items()},
        "constants": KNN_CONSTANTS,
    }

    meta = {
        "builder": "mash_knn_build_tables.py",
        "source_style": "mash_knn_mizar60_multi_proof",
        "deps_files": [str(p) for p in deps_files],
        "event_meta": event_meta,
        "training_problems_total": n_problem_files,
        "training_problems_skipped": n_skipped,
        "num_facts": len(fact_names),
        "num_features": len(dffreq),
        "num_examples": len(example_name_idx),
        "num_examples_with_deps": sum(1 for deps in example_dep_idxs if deps),
        "constants": KNN_CONSTANTS,
    }

    with open(out_tables, "wb") as f:
        pickle.dump(tables, f)
    with open(out_meta, "w") as f:
        json.dump(meta, f, indent=2, sort_keys=True)

    print(f"  tables: {out_tables} ({out_tables.stat().st_size / (1024 * 1024):.1f} MB)")
    print(f"  meta:   {out_meta}")

    print("\n" + "=" * 70)
    print("MASH K-NN TABLE BUILD COMPLETE")
    print("=" * 70)
    print(f"  facts: {len(fact_names)}")
    print(f"  examples: {len(example_name_idx)}")
    print(f"  next: python3 scripts/mash_knn_scorer.py --smoke-test")


if __name__ == "__main__":
    main()
