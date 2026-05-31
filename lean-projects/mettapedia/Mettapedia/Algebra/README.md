# Algebra (Lean 4)

`Mettapedia/Algebra` collects order-theoretic and algebraic structures the
probability and PLN developments build on: ordered semigroups (the bridge from
Knuth–Skilling to quantales), a quantale "weakness" order, hyperstructures, the
split-complex numbers, and a two-dimensional classification.

## Files

| File | Contents |
|------|----------|
| `OrderedSemigroups.lean` | our interface over the vendored `OrderedSemigroups/` library (below) |
| `QuantaleWeakness.lean` | the quantale "weakness" preorder |
| `Hyperstructure.lean` | hyperstructure (multi-valued operation) exploration |
| `SplitComplex.lean` | split-complex numbers |
| `TwoDimClassification.lean` | two-dimensional algebra classification |
| `ReferenceClassQuality.lean` | reference-class quality structure |

## Vendored dependency

`OrderedSemigroups/` is a vendored copy of **Eric Paul's OrderedSemigroups** Lean
library (its own Lake project; <https://github.com/liluap/OrderedSemigroups>) —
not our work. The Knuth–Skilling Hölder-embedding proof path depends on it.

## Status

Our `Mettapedia/Algebra` files (6) are `sorry`-free and `axiom`-free. Reproduce
from this directory (the vendored `OrderedSemigroups/` Lake project is excluded
by `rg`'s defaults):

```bash
rg -n --glob '*.lean' '^\s*(sorry|admit)\b|^\s*(@\[[^]]*\]\s*)*axiom\s' .   # prints nothing
```
