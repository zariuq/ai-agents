#!/usr/bin/env python3
"""
Whitespace-insensitive S-expression comparator.

Use this to spot structural drift between `mg_to_metta(original)` and
`mg_to_metta(round_trip)` outputs.
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path
from typing import List, Tuple, Union

SExpr = Union[str, List["SExpr"]]


def tokenize(text: str) -> List[str]:
    return re.findall(r'\(|\)|"[^"]*"|[^\s()]+', text)


def parse(tokens: List[str], idx: int = 0) -> Tuple[SExpr, int]:
    if idx >= len(tokens):
        raise ValueError("Unexpected end of tokens")
    tok = tokens[idx]
    if tok == "(":
        items: List[SExpr] = []
        i = idx + 1
        while i < len(tokens) and tokens[i] != ")":
            node, i = parse(tokens, i)
            items.append(node)
        if i >= len(tokens):
            raise ValueError("Unmatched '('")
        return items, i + 1
    if tok == ")":
        raise ValueError("Unmatched ')'")
    return tok, idx + 1


def parse_sexpr(text: str) -> SExpr:
    tokens = tokenize(text)
    nodes: List[SExpr] = []
    idx = 0
    while idx < len(tokens):
        node, idx = parse(tokens, idx)
        nodes.append(node)
    if not nodes:
        raise ValueError("Empty S-expression input")
    if len(nodes) == 1:
        return nodes[0]
    return nodes


def diff(a: SExpr, b: SExpr, path: str = "root") -> List[str]:
    if isinstance(a, list) and isinstance(b, list):
        issues: List[str] = []
        if len(a) != len(b):
            issues.append(f"{path}: length mismatch {len(a)} != {len(b)}")
        for i, (ai, bi) in enumerate(zip(a, b)):
            issues.extend(diff(ai, bi, f"{path}/{i}"))
        return issues
    if isinstance(a, list) != isinstance(b, list):
        return [f"{path}: type mismatch ({type(a).__name__} vs {type(b).__name__})"]
    if a != b:
        return [f"{path}: atom mismatch '{a}' != '{b}'"]
    return []


def main() -> None:
    parser = argparse.ArgumentParser(description="Compare two S-expression files.")
    parser.add_argument("a", type=Path)
    parser.add_argument("b", type=Path)
    args = parser.parse_args()

    sexpr_a = parse_sexpr(args.a.read_text(encoding="utf-8"))
    sexpr_b = parse_sexpr(args.b.read_text(encoding="utf-8"))

    issues = diff(sexpr_a, sexpr_b)
    if not issues:
        print("Structures match.")
    else:
        print("Differences:")
        for line in issues:
            print(f"- {line}")


if __name__ == "__main__":
    main()
