#!/usr/bin/env python3
"""
Generate Megalodon `.mg` files for bridge fuzzing.

Design goals:
  * No external deps required; integrates with Hypothesis if available.
  * Targets syntactic coverage first (definitions, parameters, operators,
    admitted theorems).
  * Keeps constructs simple so the Megalodon kernel is likely to accept them.
"""
from __future__ import annotations

import argparse
import json
import os
import random
import string
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional, Sequence

HERE = Path(__file__).resolve().parent
DEFAULT_SPEC = HERE / "grammar_snapshot.json"

try:
    from hypothesis import strategies as st  # type: ignore
except ImportError:  # pragma: no cover - optional dependency
    st = None


# --- Core term/model -------------------------------------------------------


RESERVED = {
    "fun",
    "forall",
    "set",
    "prop",
    "if",
    "then",
    "else",
    "at",
    "let",
    "in",
    "match",
    "with",
    "fix",
    "end",
    "Section",
    "End",
}


def _id_alphabet() -> str:
    return string.ascii_lowercase + string.ascii_uppercase


def fresh_name(rng: random.Random, prefix: str = "") -> str:
    base = prefix or rng.choice(_id_alphabet())
    suffix = "".join(rng.choices(string.ascii_lowercase, k=rng.randint(0, 3)))
    candidate = base + suffix
    if candidate in RESERVED:
        candidate = candidate + rng.choice(string.ascii_lowercase)
    return candidate


@dataclass
class Term:
    kind: str
    name: Optional[str] = None
    children: Optional[List["Term"]] = None

    def render(self) -> str:
        if self.kind == "var":
            return self.name or "x"
        if self.kind == "arrow":
            a, b = self.children or (Term("var", "A"), Term("var", "B"))
            return f"{_paren(a.render())} -> {_paren(b.render())}"
        if self.kind == "forall":
            v, tp, body = self.children or (
                Term("var", "x"),
                Term("var", "A"),
                Term("var", "B"),
            )
            return f"forall {v.render()}:{tp.render()}, {body.render()}"
        if self.kind == "fun":
            v, body = self.children or (Term("var", "x"), Term("var", "x"))
            return f"fun {v.render()} => {body.render()}"
        if self.kind == "app":
            a, b = self.children or (Term("var", "f"), Term("var", "x"))
            return f"{_paren(a.render())} {_paren(b.render())}"
        if self.kind == "if":
            c, t, e = self.children or (
                Term("var", "c"),
                Term("var", "t"),
                Term("var", "e"),
            )
            return f"if {c.render()} then {t.render()} else {e.render()}"
        return self.name or "x"


def _paren(s: str) -> str:
    if " " in s or "->" in s or "," in s:
        return f"({s})"
    return s


def _choose_existing(rng: random.Random, pool: Sequence[str], default: str) -> str:
    return rng.choice(list(pool)) if pool else default


def random_type(rng: random.Random, pool: List[str], depth: int = 3) -> Term:
    if depth <= 0:
        return Term("var", _choose_existing(rng, pool, "prop"))
    choice = rng.choice(["var", "arrow", "forall"])
    if choice == "var":
        return Term("var", _choose_existing(rng, pool, "prop"))
    if choice == "arrow":
        return Term(
            "arrow",
            children=[
                random_type(rng, pool, depth - 1),
                random_type(rng, pool, depth - 1),
            ],
        )
    vname = fresh_name(rng)
    v = Term("var", vname)
    extended = pool + [vname]
    return Term("forall", children=[v, random_type(rng, pool, depth - 1), random_type(rng, extended, depth - 1)])


def random_expr(rng: random.Random, pool: List[str], depth: int = 3) -> Term:
    if depth <= 0:
        return Term("var", _choose_existing(rng, pool, "x"))
    choice = rng.choice(["var", "fun", "app", "if"])
    if choice == "var":
        return Term("var", _choose_existing(rng, pool, "x"))
    if choice == "fun":
        vname = fresh_name(rng)
        v = Term("var", vname)
        return Term("fun", children=[v, random_expr(rng, pool + [vname], depth - 1)])
    if choice == "app":
        return Term(
            "app",
            children=[
                random_expr(rng, pool, depth - 1),
                random_expr(rng, pool, depth - 1),
            ],
        )
    return Term(
        "if",
        children=[
            random_expr(rng, pool, depth - 1),
            random_expr(rng, pool, depth - 1),
            random_expr(rng, pool, depth - 1),
        ],
    )


# --- Document builders -----------------------------------------------------


def definition_block(rng: random.Random, name: str, pool: List[str]) -> str:
    tp = random_type(rng, pool, depth=2).render()
    body = random_expr(rng, pool, depth=2).render()
    return f"Definition {name} : {tp} := {body}."


def parameter_block(rng: random.Random, name: str, pool: List[str]) -> str:
    tp = random_type(rng, pool, depth=2).render()
    return f"Parameter {name} : {tp}."


def theorem_block(rng: random.Random, name: str, pool: List[str], admit: bool = True) -> str:
    tp = random_type(rng, pool, depth=2).render()
    if admit:
        return f"Theorem {name} : {tp}.\nAdmitted."
    proof = random_expr(rng, pool, depth=2).render()
    return f"Theorem {name} : {tp}.\nexact ({proof}).\nQed."


def infix_block(rng: random.Random, name: str, target: str) -> str:
    prec = rng.choice([650, 700, 750, 800])
    assoc = rng.choice(["left", "right", "none"])
    return f"Infix {name} {prec} {assoc} := {target}."


def section_pair(rng: random.Random, pool: List[str]) -> str:
    sec = fresh_name(rng, prefix="Sec")
    local_pool = list(pool)
    pname = fresh_name(rng)
    local_pool.append(pname)
    items = [
        f"Section {sec}.",
        parameter_block(rng, pname, local_pool),
        definition_block(rng, fresh_name(rng), local_pool),
        f"End {sec}.",
    ]
    return "\n".join(items)


def build_doc(rng: random.Random, idx: int, spec: dict) -> str:
    header = [
        f"Title \"Fuzz case {idx}\".",
        f"Author \"Codex\".",
    ]
    blocks: List[str] = []
    pool: List[str] = ["prop", "set"]
    # Sprinkle a few declarations.
    for _ in range(rng.randint(1, 3)):
        pname = fresh_name(rng)
        blocks.append(parameter_block(rng, pname, pool))
        pool.append(pname)
    for _ in range(rng.randint(1, 3)):
        dname = fresh_name(rng)
        blocks.append(definition_block(rng, dname, pool))
        pool.append(dname)
    # Optional operator declaration referencing an existing def.
    if pool:
        target = rng.choice(pool)
        blocks.append(infix_block(rng, rng.choice(["/\\", "\\/"]), target))
    # Theorem with admitted proof to keep kernel happy.
    blocks.append(theorem_block(rng, fresh_name(rng, prefix="thm"), pool, admit=True))
    # Optional section to exercise scoping.
    if rng.random() < 0.5:
        blocks.append(section_pair(rng, pool))
    return "\n\n".join(header + blocks) + "\n"


# --- Hypothesis integration (optional) -------------------------------------


def _hypothesis_doc_strategy(spec: dict):  # pragma: no cover - used at runtime
    if st is None:
        raise RuntimeError("hypothesis is not installed; reinstall with `pip install hypothesis`.")
    rng = random.Random()

    def doc_from_seed(seed: int) -> str:
        rng.seed(seed)
        return build_doc(rng, seed, spec)

    return st.integers(min_value=0, max_value=1_000_000).map(doc_from_seed)


# --- CLI -------------------------------------------------------------------


def load_spec(path: Path) -> dict:
    if not path.exists():
        # Generate snapshot on the fly.
        from extract_grammar import build_spec  # local import to avoid overhead

        parser = Path(os.environ.get("MEGALODON_PARSER", Path(__file__).resolve().parents[3] / "megalodon" / "src" / "parser.ml"))
        syntax = Path(os.environ.get("MEGALODON_SYNTAX", Path(__file__).resolve().parents[3] / "megalodon" / "src" / "syntax.mli"))
        snapshot = build_spec(parser, syntax)
        path.write_text(json.dumps(snapshot, indent=2) + "\n", encoding="utf-8")
        return snapshot
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate Megalodon .mg fuzz corpus.")
    parser.add_argument("-n", "--count", type=int, default=5, help="How many files to generate.")
    parser.add_argument("-o", "--out-dir", type=Path, default=HERE / ".." / "tests" / "fuzz", help="Output directory.")
    parser.add_argument("--seed", type=int, default=None, help="RNG seed (defaults to random).")
    parser.add_argument("--use-hypothesis", action="store_true", help="Use Hypothesis to sample documents.")
    parser.add_argument("--spec", type=Path, default=DEFAULT_SPEC, help="Path to grammar snapshot JSON.")
    args = parser.parse_args()

    rng = random.Random(args.seed)
    spec = load_spec(args.spec)
    args.out_dir.mkdir(parents=True, exist_ok=True)

    if args.use_hypothesis:
        if st is None:
            raise SystemExit("hypothesis not installed; run without --use-hypothesis or install it.")
        strategy = _hypothesis_doc_strategy(spec)
        for i in range(args.count):
            doc = strategy.example()
            path = args.out_dir / f"fuzz_{i}.mg"
            path.write_text(doc, encoding="utf-8")
    else:
        for i in range(args.count):
            doc = build_doc(rng, i, spec)
            path = args.out_dir / f"fuzz_{i}.mg"
            path.write_text(doc, encoding="utf-8")


if __name__ == "__main__":
    main()
