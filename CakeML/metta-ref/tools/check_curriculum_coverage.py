#!/usr/bin/env python3
import argparse
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MATRIX = ROOT / "notes" / "curriculum_coverage.tsv"
HEADER = [
    "capacity",
    "status",
    "layer",
    "hol_refs",
    "cake_refs",
    "test_refs",
    "oracle_refs",
    "gate_refs",
    "gap",
]
TEXT_REF_KINDS = {"hol", "test", "oracle", "tool", "note"}
ALLOWED_STATUSES = {
    "proved-hol",
    "proved-bridge-slice",
    "partial-verified",
    "tested-only",
    "tested-oracle",
}


def rel_path(path_text):
    path = ROOT / path_text
    try:
        path.resolve().relative_to(ROOT.resolve())
    except ValueError:
        raise ValueError(f"reference escapes project root: {path_text}")
    return path


def split_refs(field):
    if field == "-" or field == "":
        return []
    return [ref for ref in field.split(";") if ref]


def check_make_target(target, errors):
    makefile = ROOT / "Makefile"
    text = makefile.read_text()
    if re.search(rf"^\.PHONY:.*(?:^| ){re.escape(target)}(?: |$)", text, re.M):
        return 1
    if re.search(rf"^{re.escape(target)}\s*:", text, re.M):
        return 1
    errors.append(f"make:{target}: target not found in {makefile.relative_to(ROOT)}")
    return 0


def check_reference(ref, errors):
    try:
        kind, rest = ref.split(":", 1)
    except ValueError:
        errors.append(f"{ref}: expected kind:path:needle, file:path, or make:target")
        return 0

    if kind == "make":
        return check_make_target(rest, errors)

    if kind == "file":
        path = rel_path(rest)
        if path.exists():
            return 1
        errors.append(f"{ref}: file not found")
        return 0

    if kind not in TEXT_REF_KINDS:
        errors.append(f"{ref}: unknown reference kind {kind}")
        return 0

    try:
        path_text, needle = rest.split(":", 1)
    except ValueError:
        errors.append(f"{ref}: expected {kind}:path:needle")
        return 0

    path = rel_path(path_text)
    if not path.exists():
        errors.append(f"{ref}: file not found")
        return 0

    text = path.read_text()
    if needle not in text:
        errors.append(f"{ref}: needle not found")
        return 0

    return 1


def read_matrix(path):
    lines = path.read_text().splitlines()
    if not lines:
        raise ValueError(f"{path}: empty matrix")
    header = lines[0].split("\t")
    if header != HEADER:
        raise ValueError(f"{path}: unexpected header {header}")
    rows = []
    for lineno, line in enumerate(lines[1:], start=2):
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) != len(HEADER):
            raise ValueError(
                f"{path}:{lineno}: expected {len(HEADER)} tab-separated fields, "
                f"got {len(fields)}"
            )
        row = dict(zip(HEADER, fields))
        row["_lineno"] = str(lineno)
        rows.append(row)
    return rows


def check_matrix(path):
    rows = read_matrix(path)
    errors = []
    refs_checked = 0
    capacities = set()

    for row in rows:
        capacity = row["capacity"]
        if capacity in capacities:
            errors.append(f"{path}:{row['_lineno']}: duplicate capacity {capacity}")
        capacities.add(capacity)

        if row["status"] not in ALLOWED_STATUSES:
            errors.append(
                f"{path}:{row['_lineno']}: unknown status {row['status']}"
            )

        if row["gap"] in {"", "-"}:
            errors.append(f"{path}:{row['_lineno']}: gap field must be honest text")

        for column in ("hol_refs", "cake_refs", "test_refs", "oracle_refs", "gate_refs"):
            for ref in split_refs(row[column]):
                refs_checked += check_reference(ref, errors)

    if errors:
        for error in errors:
            print(error, file=sys.stderr)
        return 1

    print(
        f"curriculum coverage matrix checked: "
        f"{len(rows)} capacities, {refs_checked} references"
    )
    return 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--matrix", default=str(DEFAULT_MATRIX))
    args = parser.parse_args()

    if not args.check:
        parser.error("expected --check")

    try:
        return check_matrix(Path(args.matrix))
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
