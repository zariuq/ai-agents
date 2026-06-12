#!/usr/bin/env python3
import argparse
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
HOL_SOURCE = ROOT / "hol" / "metta_m1Script.sml"
TARGETS = [
    ROOT / "sml" / "metta_m1.sml",
    ROOT / "cml" / "metta_m1.cml",
]

BLOCK_MARKERS = {
    "pre": {
        "begin": "(* BEGIN GENERATED PRE_EVAL_FRAGMENTS *)",
        "end": "(* END GENERATED PRE_EVAL_FRAGMENTS *)",
    },
    "post": {
        "begin": "(* BEGIN GENERATED POST_EVAL_FRAGMENTS *)",
        "end": "(* END GENERATED POST_EVAL_FRAGMENTS *)",
    },
}

# Lint manifest only: the bodies inside the marked SML/CakeML blocks are not
# generated here and this file is not a semantic source of truth.
FRAGMENT_MANIFEST = [
    {
        "block": "pre",
        "name": "eval_return_fragment",
        "args": ["atom"],
        "class": "exploratory-only",
        "backing": "numeric translated helper + CF wrapper; marked block still string-world",
    },
    {
        "block": "post",
        "name": "eval_add_fragment",
        "args": ["fuel", "space", "atom"],
        "class": "exploratory-only",
        "backing": "translated/CF primitive-values helpers only",
    },
    {
        "block": "post",
        "name": "eval_eval_fragment",
        "args": ["fuel", "space", "atom"],
        "class": "exploratory-only",
    },
    {
        "block": "post",
        "name": "eval_chain_fragment",
        "args": ["fuel", "space", "atom"],
        "class": "exploratory-only",
        "backing": "translated chain payload helpers only",
    },
    {
        "block": "post",
        "name": "eval_case_fragment",
        "args": ["fuel", "space", "atom"],
        "class": "exploratory-only",
    },
    {
        "block": "post",
        "name": "m1_typed_eval",
        "args": ["fuel", "space", "atom"],
        "export": False,
        "hol_fragment": False,
        "class": "exploratory-only",
    },
    {
        "block": "post",
        "name": "eval_typed_fragment",
        "args": ["fuel", "space", "atom"],
        "class": "exploratory-only",
    },
    {
        "block": "post",
        "name": "eval_evalc_fragment",
        "args": ["fuel", "space", "atom"],
        "class": "exploratory-only",
    },
    {
        "block": "post",
        "name": "eval_vec_cons_fragment",
        "args": ["space", "atom"],
        "class": "exploratory-only",
    },
]


def extract_block(text, name, path):
    begin = BLOCK_MARKERS[name]["begin"]
    end = BLOCK_MARKERS[name]["end"]
    try:
        start = text.index(begin) + len(begin)
        stop = text.index(end, start)
    except ValueError as exc:
        raise ValueError(f"{path}: missing generated {name} markers") from exc
    block = text[start:stop]
    if block.startswith("\n"):
        block = block[1:]
    if block.endswith("\n"):
        block = block[:-1]
    return block


def specs_for_block(name):
    return [spec for spec in FRAGMENT_MANIFEST if spec["block"] == name]


def has_fun_signature(block, spec):
    args = r"\s+".join(map(re.escape, spec["args"]))
    pattern = rf"(?m)^fun\s+{re.escape(spec['name'])}\s+{args}\s*="
    return re.search(pattern, block) is not None


def check_block_manifest(path, block_name, block):
    failures = 0
    for spec in specs_for_block(block_name):
        if not has_fun_signature(block, spec):
            failures += 1
            print(
                f"{path}: marked {block_name} block missing "
                f"{spec['name']} {' '.join(spec['args'])}",
                file=sys.stderr,
            )
        if spec.get("export", True):
            export_spec = {
                "name": f"export_{spec['name']}",
                "args": spec["args"],
            }
            if not has_fun_signature(block, export_spec):
                failures += 1
                print(
                    f"{path}: marked {block_name} block missing "
                    f"{export_spec['name']} {' '.join(export_spec['args'])}",
                    file=sys.stderr,
                )
    return failures


def check():
    failures = 0
    hol_fragments = derive_hol_fragments()
    for path in TARGETS:
        text = path.read_text()
        marked_blocks = ""
        for name in BLOCK_MARKERS:
            actual = extract_block(text, name, path)
            marked_blocks += actual + "\n"
            failures += check_block_manifest(path, name, actual)
        for fragment in hol_fragments:
            for fun_name in (fragment, f"export_{fragment}"):
                if f"fun {fun_name} " not in marked_blocks:
                    failures += 1
                    print(
                        f"{path}: marked blocks do not expose HOL fragment {fun_name}",
                        file=sys.stderr,
                    )
    failures += check_hol_manifest(hol_fragments)
    failures += check_lint_manifest(hol_fragments)
    return failures


def derive_hol_fragments():
    text = HOL_SOURCE.read_text()
    fragments = []
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("Definition eval_") and line.endswith("_def:"):
            name = line.removeprefix("Definition ").removesuffix("_def:")
            if name.endswith("_fragment") and name not in fragments:
                fragments.append(name)
    return fragments


def check_hol_manifest(fragments):
    text = HOL_SOURCE.read_text()
    failures = 0
    for fragment in fragments:
        required = [
            f"Definition export_{fragment}_def:",
            f"Theorem import_export_{fragment}:",
        ]
        if fragment == "eval_typed_fragment":
            required.append(
                "Theorem eval_typed_fragment_agrees_with_typed_eval_m1_rec:"
            )
        else:
            required.append(f"Theorem {fragment}_agrees_with_eval_m1_rec:")
        for needle in required:
            if needle not in text:
                failures += 1
                print(
                    f"{HOL_SOURCE}: HOL fragment manifest missing {needle}",
                    file=sys.stderr,
                )
    return failures


def check_lint_manifest(hol_fragments):
    manifested = [
        spec["name"]
        for spec in FRAGMENT_MANIFEST
        if spec.get("hol_fragment", True)
    ]
    failures = 0
    for fragment in hol_fragments:
        if fragment not in manifested:
            failures += 1
            print(
                f"{HOL_SOURCE}: lint manifest missing {fragment}",
                file=sys.stderr,
            )
    for fragment in manifested:
        if fragment not in hol_fragments:
            failures += 1
            print(
                f"{fragment}: lint manifest has no HOL definition",
                file=sys.stderr,
            )
    return failures


def emit_hol_manifest():
    for fragment in derive_hol_fragments():
        print(fragment)


def emit_lint_manifest():
    for spec in FRAGMENT_MANIFEST:
        marker = "HOL" if spec.get("hol_fragment", True) else "extra"
        export = "export" if spec.get("export", True) else "no-export"
        backing = spec.get("backing", "no CakeML proof for marked block")
        print(
            f"{spec['block']}\t{spec['name']}\t"
            f"{' '.join(spec['args'])}\t{marker}\t{export}\t"
            f"{spec['class']}\t{backing}"
        )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--emit", choices=sorted(BLOCK_MARKERS))
    parser.add_argument("--emit-hol-manifest", action="store_true")
    parser.add_argument("--emit-lint-manifest", action="store_true")
    args = parser.parse_args()

    if args.emit_hol_manifest:
        emit_hol_manifest()
        return 0
    if args.emit_lint_manifest:
        emit_lint_manifest()
        return 0
    if args.emit:
        for spec in specs_for_block(args.emit):
            export = " + export" if spec.get("export", True) else ""
            print(f"{spec['name']} {' '.join(spec['args'])}{export}")
        return 0
    if args.write:
        print(
            "semantic fragment generation is disabled; "
            "this tool is lint/manifest-only",
            file=sys.stderr,
        )
        return 1
    if args.check:
        failures = check()
        if failures:
            return 1
        print("fragment export blocks satisfy HOL/lint manifest")
        return 0

    parser.print_help()
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
