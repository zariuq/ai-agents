# Computability & Algorithmic Information (Lean 4)

`Mettapedia/Computability` formalizes computability and algorithmic-information
notions used across Mettapedia: Hutter-style computability of semimeasures,
oracle and probabilistic Turing machines, Kolmogorov complexity, the
arithmetical hierarchy, and a large research lane on the P vs NP question.

## Components

| Area | Where | Notes |
|------|-------|-------|
| Hutter computability | `HutterComputability*.lean`, `CantorSpace.lean` | computability of semimeasures (closure, ℚ, ℝ≥0∞ variants) |
| Oracle Turing machines | `OracleTM*.lean` | oracle TMs (real / refined variants) |
| Probabilistic Turing machines | `ProbabilisticTM*.lean` | randomized computation |
| Kolmogorov complexity | `KolmogorovComplexity/` (4) | description-length complexity |
| Arithmetical hierarchy | `ArithmeticalHierarchy/` (5) | Σ/Π levels |
| P vs NP machinery | `PNP/` (73) | see below |

### `PNP/` — P vs NP research lane (73 files)

A large research development of obstruction-theoretic machinery around the
P vs NP question: encoded hypothesis classes, empirical-risk-minimization (ERM)
interfaces, compression / asymmetry-budget obstructions, and conditional-margin
lemmas (`AB`/`ZAB` candidate, recovery, and target routes). The results are
largely **conditional / hypothesis-relative** — this lane does **not** assert a
resolution of P vs NP. It is `sorry`- and `axiom`-free (uses `native_decide`
once).

## Status

`axiom`-free throughout. The 4 `sorry`s are in work-in-progress modules —
`OracleTM.lean` (1), `ProbabilisticTM.lean` (2), `ArithmeticalHierarchy/Level3.lean`
(1); the Hutter-computability core, Kolmogorov complexity, and the `PNP/` lane
are `sorry`-free. Reproduce from this directory:

```bash
# 4 sorry hits (OracleTM, ProbabilisticTM, ArithmeticalHierarchy/Level3):
rg -n --glob '*.lean' '^\s*(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
```
