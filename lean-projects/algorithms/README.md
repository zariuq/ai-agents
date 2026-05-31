# Algorithms — executable Lean (MeTTa runtime, GF parsing, graph & quantitative checkers)

`lean-projects/algorithms` is the lightweight, *executable*-Lean counterpart to
the Mettapedia OSLF semantic IL: where `Mettapedia/OSLF` proves language-level
properties, this project hosts runnable implementations — a MeTTa interpreter,
Grammatical Framework parsing, graph algorithms, and quantitative checkers.

Lean library: `«Algorithms»` (`Algorithms.lean` is the root aggregator).

## Modules

| Module | Where | Notes |
|--------|-------|-------|
| MeTTa runtime | `Algorithms/MeTTa/` (71) | a MeTTa parser + interpreter; the verified `Eval/` evaluator (16 files) supersedes the older `Simple/` evaluator |
| GF parsing | `Algorithms/GF/` (19), `GF.lean` | Grammatical Framework parsing |
| Graph algorithms | `Algorithms/Graph/` (2) | independent-set functions + checker |
| Quantitative checkers | `Algorithms/Quantitative/` (1) | finite L1-rational checker kernel (no Mathlib) |

## Build

```bash
cd lean-projects/algorithms
lake build
```

## Status

`sorry`-free and `axiom`-free across the 94 `.lean` files under `Algorithms/`.
Reproduce from this directory (prints nothing):

```bash
rg -n --glob '*.lean' '^\s*(sorry|admit)\b|^\s*(@\[[^]]*\]\s*)*axiom\s' Algorithms
```

Note: the older `Algorithms/MeTTa/Simple/` evaluator (≈80 `partial def`,
unverifiable totality) is **deprecated** (2026-03-22) and not built by default;
it is superseded by the verified `Eval/` architecture (0 `partial def`).

## See also

- `Mettapedia/OSLF/` (in the mettapedia project) — the OSLF semantic IL and
  language-property proofs this runtime corresponds to.
