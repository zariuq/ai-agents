# Probability Theory (Lean 4)

`Mettapedia/ProbabilityTheory` is the umbrella for Mettapedia's probability and
inference formalizations: the Knuth–Skilling foundations of inference, Cox's
theorem, Bayesian networks, imprecise / belief-function probability, the
probability "hypercube", and bridges to measure theory and Markov categories.

The flagship development is **Knuth–Skilling** (`KnuthSkilling/`, 162 files) —
see its own [README](KnuthSkilling/README.md).

## Topics

| Area | Where | Notes |
|------|-------|-------|
| Knuth–Skilling foundations of inference | `KnuthSkilling/` (162) | flagship; has its own README |
| Cox's theorem | `Cox/` (6), `Cox.lean` | product/sum-rule derivation |
| Bayesian networks | `BayesianNetworks/` (28) | local Markov, d-separation, inference |
| Probability hypercube | `Hypercube/` (23) | axis space: commutativity, distributivity, precision, ordering, additivity |
| Imprecise probability | `ImpreciseProbability/` (5), `BeliefFunctions/` | credal sets, belief functions |
| Higher-order probability | `HigherOrderProbability/` (6) | probabilities over probabilities |
| Free / quantum probability | `FreeProbability/` (2), `QuantumProbability/` | non-commutative probability |
| Optimal transport, Markov category | `OptimalTransport/`, `MarkovCategory/` | categorical / transport views |
| Bridges & unification | `MeasureBridge.lean`, `Unified*.lean`, `CommonFoundations.lean` | ties the strands together |

## Status

`axiom`-free throughout. The 7 `sorry`s are confined to work-in-progress /
exploratory files: `FreeProbability/Basic.lean` (1), and the **non-imported**
`KnuthSkilling/Exploration/` and `KnuthSkilling/Multiplicative/Scratch/`
exploratory files (6; see the Knuth–Skilling README). Reproduce from this
directory:

```bash
# all 7 sorry hits are in FreeProbability/Basic.lean or KnuthSkilling Exploration/Scratch:
rg -n --glob '*.lean' '^\s*(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
```

## See also

- [`KnuthSkilling/README.md`](KnuthSkilling/README.md) — foundations of inference (flagship).
- `Hypercube/` and the `Mettapedia/ProbabilityTheory/Hypercube/` weakness-order / quantale-semantics layer.
