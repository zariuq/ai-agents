#!/usr/bin/env python3
"""
Lightweight grammar/precedence extractor for Megalodon.

Because the upstream repository ships generated `parser.ml` but not the original
`parser.mly`, we scrape the available sources to build a machine-readable
summary that downstream generators/fuzzers can consume. The goal is not to
replace the parser but to surface:
  * token constructors and payloads,
  * docitem / tactic constructors (from syntax.mli),
  * built-in operator precedence seeds (`penv_*` tables).

This keeps the bridge scripts in sync with Megalodon's evolving grammar without
hand-transcribing it.
"""
from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass, asdict
import os
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

HERE = Path(__file__).resolve().parent


def _guess_workspace_root() -> Path:
    """
    Heuristic to locate the workspace root.
    We expect the structure:
        <workspace>/
          megalodon/
          metta-tools/megalodon-bridge/tools/extract_grammar.py
    """
    # Prefer an explicit override.
    root_from_env = Path(
        os.environ.get("MEGALODON_WORKSPACE", HERE.parents[2])
    ).resolve()
    if (root_from_env / "megalodon").exists():
        return root_from_env
    # Fall back to walking up until we see megalodon/
    for ancestor in HERE.parents:
        candidate = ancestor / "megalodon"
        if candidate.exists():
            return ancestor
    # Default to current working directory if nothing else matches.
    return Path.cwd()


REPO_ROOT = _guess_workspace_root()


# --- Helpers ---------------------------------------------------------------

_TYPE_DEF_RE = re.compile(r"^type\s+(?P<name>[a-zA-Z0-9_']+)\s*=\s*(?P<body>.*)$")


@dataclass
class Constructor:
    name: str
    payload: Optional[str]


def _collect_type_constructors(lines: List[str], start_idx: int) -> Tuple[str, List[Constructor], int]:
    """
    Parse a simple OCaml variant type definition starting at `lines[start_idx]`.

    We only handle the style used in Megalodon sources:
        type token =
          | STRING of string
          | LPAREN
    Parsing stops when we hit a non-constructor line.
    """
    header = lines[start_idx]
    m = _TYPE_DEF_RE.match(header.strip())
    if not m:
        raise ValueError(f"Expected type definition at line {start_idx+1}: {header}")
    type_name = m.group("name")
    remainder = m.group("body").strip()
    constructors: List[Constructor] = []

    cons_re = re.compile(
        r"^\|?\s*(?P<name>[A-Za-z0-9_']+)"
        r"(?:\s+of\s+(?P<payload>.+))?$"
    )

    def add_constructor(chunk: str) -> None:
        chunk = chunk.strip()
        if not chunk or chunk == "|":
            return
        if chunk.startswith("|"):
            chunk = chunk[1:].strip()
        m = cons_re.match(chunk)
        if not m:
            return
        constructors.append(
            Constructor(name=m.group("name"), payload=m.group("payload"))
        )

    if remainder:
        # Handle inline constructor after '=' on the same line.
        add_constructor(remainder)

    i = start_idx + 1
    while i < len(lines):
        raw = lines[i]
        stripped = raw.strip()
        if stripped.startswith("|"):
            add_constructor(stripped)
            i += 1
            continue
        if stripped == "":
            # Allow a single blank line but stop if the following is not a constructor.
            # This keeps us from consuming subsequent 'let' bindings.
            if i + 1 < len(lines) and lines[i + 1].strip().startswith("|"):
                i += 1
                continue
            break
        # Any other starter means we've reached the end of the type block.
        break
    return type_name, constructors, i


def parse_type_block(text: str, type_names: Iterable[str]) -> Dict[str, List[Constructor]]:
    """Extract constructors for the requested type names from the source text."""
    lines = text.splitlines()
    wanted = set(type_names)
    found: Dict[str, List[Constructor]] = {}
    i = 0
    while i < len(lines) and wanted:
        m = _TYPE_DEF_RE.match(lines[i].strip())
        if m and m.group("name") in wanted:
            tname, cons, next_i = _collect_type_constructors(lines, i)
            found[tname] = cons
            wanted.discard(tname)
            i = next_i
        else:
            i += 1
    return found


def _collect_hashtbl_entries(text: str) -> Dict[str, List[Dict[str, object]]]:
    """
    Scrape initial precedence/binder tables from parser.ml.
    We care about:
      * penv_preop
      * penv_postinfop
      * penv_binder
      * rightinfixpriorities / disallowedprefixpriorities / disallowedrightinfixpriorities
    """
    entries: Dict[str, List[Dict[str, object]]] = {}

    # penv_postinfop / penv_preop / penv_binder with string keys
    re_string_entry = re.compile(
        r'Hashtbl\.add\s+'
        r'(?P<table>penv_preop|penv_postinfop|penv_binder)\s+'
        r'"(?P<name>[^"]+)"\s+'
        r'(?P<value>\([^)]*\)|[A-Z][A-Za-z0-9_]*)'
    )
    for m in re_string_entry.finditer(text):
        table = m.group("table")
        entries.setdefault(table, []).append(
            {"name": m.group("name"), "value": m.group("value")}
        )

    # rightinfixpriorities / disallowed* priorities with integer keys
    re_int_entry = re.compile(
        r'Hashtbl\.add\s+'
        r'(?P<table>rightinfixpriorities|disallowedprefixpriorities|disallowedrightinfixpriorities)\s+'
        r'(?P<value>\d+)\s+\(\)'
    )
    for m in re_int_entry.finditer(text):
        table = m.group("table")
        entries.setdefault(table, []).append({"value": int(m.group("value"))})

    return entries


# --- CLI -------------------------------------------------------------------


def build_spec(parser_path: Path, syntax_path: Path) -> Dict[str, object]:
    parser_text = parser_path.read_text(encoding="utf-8")
    syntax_text = syntax_path.read_text(encoding="utf-8")

    types_to_capture = ["token", "docitem", "pftacitem"]
    type_info = parse_type_block(parser_text, types_to_capture[:1])
    type_info.update(parse_type_block(syntax_text, types_to_capture[1:]))

    precedence_info = _collect_hashtbl_entries(parser_text)

    return {
        "source": {
            "parser": str(parser_path),
            "syntax": str(syntax_path),
        },
        "tokens": [asdict(c) for c in type_info.get("token", [])],
        "docitems": [asdict(c) for c in type_info.get("docitem", [])],
        "pftacitems": [asdict(c) for c in type_info.get("pftacitem", [])],
        "precedence_seeds": precedence_info,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Extract a grammar summary from Megalodon sources.")
    parser.add_argument(
        "--parser",
        type=Path,
        default=REPO_ROOT / "megalodon" / "src" / "parser.ml",
        help="Path to parser.ml (generated parser).",
    )
    parser.add_argument(
        "--syntax",
        type=Path,
        default=REPO_ROOT / "megalodon" / "src" / "syntax.mli",
        help="Path to syntax.mli containing AST definitions.",
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        help="Optional path to write JSON output. Prints to stdout if omitted.",
    )
    args = parser.parse_args()

    spec = build_spec(args.parser, args.syntax)
    payload = json.dumps(spec, indent=2, sort_keys=True)
    if args.output:
        args.output.write_text(payload + "\n", encoding="utf-8")
    else:
        print(payload)


if __name__ == "__main__":
    main()
