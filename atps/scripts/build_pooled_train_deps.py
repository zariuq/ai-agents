#!/usr/bin/env python3
"""
Build pooled train dependency events from base deps + all train proof runs.

This intentionally preserves duplicate events across sources (no dedup), so
downstream learners can exploit more supervision signal.
"""

import argparse
import json
import re
from pathlib import Path

DATASET_DIR = Path("/home/zar/claude/atps/datasets/extended_mptp5k")
DEFAULT_BASE_DEPS = [
    DATASET_DIR / "deps" / "bushy_train_deps.jsonl",
    DATASET_DIR / "deps" / "chainy_train_deps.jsonl",
]
DEFAULT_PROBLEMS_DIR = DATASET_DIR / "chainy" / "train"
DEFAULT_OUTPUT = DATASET_DIR / "deps" / "pooled_train_deps_allruns.jsonl"
DEFAULT_META = DATASET_DIR / "deps" / "pooled_train_deps_allruns_meta.json"

FILE_REF_RE = re.compile(r"file\('[^']*',\s*(\w+)\)")
FORMULA_RE = re.compile(r"^(fof|cnf)\(([^,]+),\s*([^,]+),")
AXIOM_ROLES = {"axiom", "hypothesis", "definition"}


def parse_proof_axioms(proof_output):
    used = set()
    lines = []
    for line in proof_output.split("\n"):
        s = line.strip()
        if not s or s.startswith("%"):
            continue
        lines.append(s)
    text = " ".join(lines)
    formulas = re.split(r"(?=(?:fof|cnf)\()", text)

    for formula in formulas:
        formula = formula.strip()
        if not formula:
            continue
        m_file = FILE_REF_RE.search(formula)
        if not m_file:
            continue
        m_formula = FORMULA_RE.match(formula)
        if not m_formula:
            continue
        role = m_formula.group(3).strip()
        if role in AXIOM_ROLES:
            used.add(m_file.group(1))
    return used


def parse_available_axioms(problem_file):
    axioms = set()
    with open(problem_file) as f:
        for raw in f:
            line = raw.strip()
            m = FORMULA_RE.match(line)
            if not m:
                continue
            role = m.group(3).strip()
            if role in AXIOM_ROLES:
                axioms.add(m.group(2).strip())
    return axioms


def collect_base_events(dep_files):
    events = []
    stats = {"rows": 0, "proved_rows": 0, "kept": 0}
    for dep_file in dep_files:
        with open(dep_file) as f:
            for line in f:
                stats["rows"] += 1
                rec = json.loads(line)
                if not rec.get("proved", False):
                    continue
                stats["proved_rows"] += 1
                problem_name = rec.get("problem_name")
                if not problem_name:
                    continue
                out = dict(rec)
                out["source_kind"] = "base_deps"
                out["source_name"] = dep_file.name
                out["source_path"] = str(dep_file)
                events.append(out)
                stats["kept"] += 1
    return events, stats


def collect_proof_events(proof_dirs, problems_dir):
    events = []
    per_dir = {}
    cache_available = {}
    total = {
        "proof_files": 0,
        "proved_files": 0,
        "with_file_refs": 0,
        "kept": 0,
        "missing_problem_file": 0,
    }

    for proof_dir in proof_dirs:
        dstat = {
            "proof_files": 0,
            "proved_files": 0,
            "with_file_refs": 0,
            "kept": 0,
            "missing_problem_file": 0,
        }
        for proof_file in sorted(proof_dir.glob("*.out")):
            total["proof_files"] += 1
            dstat["proof_files"] += 1
            txt = proof_file.read_text(errors="ignore")
            proved = ("Proof found" in txt) or ("SZS status Theorem" in txt)
            if not proved:
                continue
            total["proved_files"] += 1
            dstat["proved_files"] += 1

            used_axioms = parse_proof_axioms(txt)
            if not used_axioms:
                continue
            total["with_file_refs"] += 1
            dstat["with_file_refs"] += 1

            problem_name = proof_file.stem
            pfile = problems_dir / problem_name
            if not pfile.exists():
                total["missing_problem_file"] += 1
                dstat["missing_problem_file"] += 1
                continue

            if problem_name not in cache_available:
                cache_available[problem_name] = sorted(parse_available_axioms(pfile))
            available = cache_available[problem_name]

            rec = {
                "problem": f"train/{problem_name}",
                "problem_name": problem_name,
                "proved": True,
                "used_axioms": sorted(used_axioms),
                "available_axioms": available,
                "num_used": len(used_axioms),
                "num_available": len(available),
                "source_kind": "proof_dir",
                "source_name": proof_dir.name,
                "source_path": str(proof_dir),
            }
            events.append(rec)
            total["kept"] += 1
            dstat["kept"] += 1

        per_dir[proof_dir.name] = dstat
    return events, total, per_dir


def main():
    parser = argparse.ArgumentParser(
        description="Pool train dependency events from base deps + proof runs"
    )
    parser.add_argument(
        "--base-deps-files",
        nargs="+",
        default=[str(p) for p in DEFAULT_BASE_DEPS],
        help="Base deps JSONL files (default: bushy+chainy train deps)",
    )
    parser.add_argument(
        "--proof-dirs",
        nargs="+",
        default=[
            str(p)
            for p in sorted(DATASET_DIR.glob("proofs_*_train_5s"))
            if p.is_dir()
        ],
        help="Train proof dirs to extract used axioms from",
    )
    parser.add_argument(
        "--problems-dir",
        default=str(DEFAULT_PROBLEMS_DIR),
        help="Problem files directory for available-axiom extraction",
    )
    parser.add_argument("--output", default=str(DEFAULT_OUTPUT), help="Output pooled deps JSONL")
    parser.add_argument("--meta-output", default=str(DEFAULT_META), help="Output metadata JSON")
    args = parser.parse_args()

    base_dep_files = [Path(p) for p in args.base_deps_files]
    proof_dirs = [Path(p) for p in args.proof_dirs]
    problems_dir = Path(args.problems_dir)
    out_file = Path(args.output)
    meta_file = Path(args.meta_output)

    missing_base = [str(p) for p in base_dep_files if not p.exists()]
    if missing_base:
        raise FileNotFoundError(f"Missing base deps files: {missing_base}")
    missing_proof = [str(p) for p in proof_dirs if not p.exists()]
    if missing_proof:
        raise FileNotFoundError(f"Missing proof dirs: {missing_proof}")
    if not problems_dir.exists():
        raise FileNotFoundError(f"Problems dir missing: {problems_dir}")

    print("Collecting base deps events...")
    base_events, base_stats = collect_base_events(base_dep_files)
    print(
        f"  base events: kept={base_stats['kept']} "
        f"(rows={base_stats['rows']}, proved={base_stats['proved_rows']})"
    )

    print("Extracting events from proof dirs...")
    proof_events, proof_total, proof_per_dir = collect_proof_events(proof_dirs, problems_dir)
    print(
        f"  proof events: kept={proof_total['kept']} "
        f"(proof_files={proof_total['proof_files']}, proved_files={proof_total['proved_files']}, "
        f"with_file_refs={proof_total['with_file_refs']})"
    )

    pooled = base_events + proof_events
    out_file.parent.mkdir(parents=True, exist_ok=True)
    with open(out_file, "w") as f:
        for rec in pooled:
            f.write(json.dumps(rec) + "\n")

    # Quick coverage metrics
    problems = set()
    src_counter = {}
    for rec in pooled:
        pname = rec.get("problem_name")
        if pname:
            problems.add(pname)
        src = rec.get("source_name", "unknown")
        src_counter[src] = src_counter.get(src, 0) + 1

    meta = {
        "output": str(out_file),
        "total_events": len(pooled),
        "unique_problem_names": len(problems),
        "base_dep_files": [str(p) for p in base_dep_files],
        "proof_dirs": [str(p) for p in proof_dirs],
        "problems_dir": str(problems_dir),
        "base_stats": base_stats,
        "proof_total": proof_total,
        "proof_per_dir": proof_per_dir,
        "events_by_source_name": src_counter,
    }
    with open(meta_file, "w") as f:
        json.dump(meta, f, indent=2, sort_keys=True)

    print(f"Saved pooled deps: {out_file}")
    print(f"Saved metadata:   {meta_file}")
    print(f"  total events: {len(pooled)}")
    print(f"  unique problems: {len(problems)}")


if __name__ == "__main__":
    main()
