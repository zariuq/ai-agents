#!/usr/bin/env python3
"""
ALIAS wrapper for the proof-driven Best-PLN draft selector.

It reuses the optimized kNN-prior + NB-likelihood pipeline, but points PeTTa
to `demos/pln_best_selector_draft.metta` and enables NB-likelihood merge by
default (matching the Best-PLN draft composition).

Usage example:
  python3 scripts/select_pln_best_draft.py --top-k 256 --output selections.json
"""

import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


BASE = Path(__file__).with_name("select_pln_knn_prior_nb_opt.py")
BEST_SELECTOR = "demos/pln_best_selector_draft.metta"
ALIAS_LABEL = "pln_best_draft_alias"


def _find_arg_value(argv: list[str], key: str) -> str | None:
    for i, tok in enumerate(argv):
        if tok == key and i + 1 < len(argv):
            return argv[i + 1]
        if tok.startswith(key + "="):
            return tok.split("=", 1)[1]
    return None


def _with_alias_labeled_output(argv: list[str]) -> list[str]:
    out = _find_arg_value(argv, "--output")
    if not out:
        return argv

    p = Path(out)
    stem = p.stem
    suffix = p.suffix
    if "alias" in stem:
        return argv

    # If caller asked for pln_best_draft output, force an explicit alias label.
    if "pln_best_draft" in stem:
        new_stem = stem.replace("pln_best_draft", ALIAS_LABEL)
    else:
        new_stem = f"{stem}_{ALIAS_LABEL}"
    new_out = str(p.with_name(new_stem + suffix))

    patched: list[str] = []
    i = 0
    while i < len(argv):
        tok = argv[i]
        if tok == "--output" and i + 1 < len(argv):
            patched.extend([tok, new_out])
            i += 2
            continue
        if tok.startswith("--output="):
            patched.append(f"--output={new_out}")
            i += 1
            continue
        patched.append(tok)
        i += 1

    print(
        f"[ALIAS] rewrote --output to explicit alias label: {new_out}",
        file=sys.stderr,
    )
    return patched


def _write_alias_sidecar(argv: list[str], return_code: int) -> None:
    out = _find_arg_value(argv, "--output")
    if not out:
        return
    out_path = Path(out)
    sidecar = out_path.with_suffix(out_path.suffix + ".alias_meta.json")
    payload = {
        "is_alias": True,
        "alias_label": ALIAS_LABEL,
        "alias_script": str(Path(__file__).name),
        "alias_of_script": str(BASE.name),
        "alias_of_petta_selector": BEST_SELECTOR,
        "forced_flags": ["--merge-nb", f"--petta-selector={BEST_SELECTOR}"],
        "output_path": str(out_path),
        "exit_code": return_code,
        "utc_timestamp": datetime.now(timezone.utc).isoformat(),
    }
    sidecar.parent.mkdir(parents=True, exist_ok=True)
    with open(sidecar, "w") as f:
        json.dump(payload, f, indent=2)
    print(f"[ALIAS] wrote metadata: {sidecar}", file=sys.stderr)


def main() -> int:
    argv = sys.argv[1:]

    # Enforce Best-PLN defaults unless caller overrides explicitly.
    if "--merge-nb" not in argv:
        argv = ["--merge-nb"] + argv
    if "--petta-selector" not in argv:
        argv = ["--petta-selector", BEST_SELECTOR] + argv
    argv = _with_alias_labeled_output(argv)

    print(
        "[ALIAS] select_pln_best_draft.py is a wrapper over "
        "select_pln_knn_prior_nb_opt.py",
        file=sys.stderr,
    )

    cmd = [sys.executable, str(BASE)] + argv
    rc = subprocess.call(cmd)
    _write_alias_sidecar(argv, rc)
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
