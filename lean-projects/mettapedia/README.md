# Mettapedia - Encyclopedia of Formalized Mathematics

A comprehensive formalization of mathematics across multiple domains, inspired by Wikipedia's breadth and Metamath's rigor.

## Project Structure

```
Mettapedia/
├── ProbabilityTheory/   # K&S, Cox, Kolmogorov, Hypercube
├── InformationTheory/   # Shannon entropy, Faddeev axioms, KL divergence
├── Logic/               # PLN evidence theory, Solomonoff induction
├── UniversalAI/         # AIXI, Grain of Truth, multi-agent systems
├── Algebra/             # Ordered semigroups (Hölder/Alimov)
├── GraphTheory/         # [skeleton]
└── ...                  # Other domains [skeleton]
```

## Tools

- **Lean 4.25.0**: Theorem prover
- **LeanHammer**: ATP integration with Zipperposition prover
- **Mathlib v4.25.0**: Lean's standard math library

## Build

```bash
cd lean-projects/mettapedia
lake update && lake exe cache get   # First time only

export LAKE_JOBS=3
ulimit -Sv 6291456
nice -n 19 lake build Mettapedia.ProbabilityTheory.KnuthSkilling.FoundationsOfInference
```

## Knuth-Skilling Formalization

The **Knuth-Skilling Foundations of Inference** formalization is the most developed subproject,
with the core theorems (Appendices A, B, C) fully verified in Lean 4.

> **Note**: Main theorem statements and definitions have been reviewed by human; may still contain errors.
> Prose in accompanying papers may contain human or AI errors; formal claims are machine-checked.

### Papers

| Paper | Description |
|-------|-------------|
| `papers/ks-lean-overview.pdf` | Lean code walkthrough with line numbers |
| `papers/ks-math-foundations.pdf` | Mathematical foundations of the K&S representation theorem |
| `papers/ks-foi-review.pdf` | Review of K&S (2012) for Foundations of Information |

### Quick Start

```bash
# Main entrypoint (zero sorries)
lake build Mettapedia.ProbabilityTheory.KnuthSkilling.FoundationsOfInference

# Shore-Johnson (explicit import)
lake build Mettapedia.ProbabilityTheory.KnuthSkilling.ShoreJohnson.Main

# Shannon/Faddeev entropy
lake build Mettapedia.InformationTheory.ShannonEntropy.Main
```

For detailed K&S documentation, directory structure, and import rules, see:
**[ProbabilityTheory/KnuthSkilling/README.md](Mettapedia/ProbabilityTheory/KnuthSkilling/README.md)**

## Other Subprojects

| Subproject | Status | Location |
|------------|--------|----------|
| **Cox Theorem** | ✅ Verified | `ProbabilityTheory/Cox/` |
| **Shannon/Faddeev Entropy** | ✅ Verified | `InformationTheory/ShannonEntropy/` |
| **PLN Evidence Theory** | 🔬 Experimental | `Logic/` |
| **Universal AI (AIXI)** | 🔬 Experimental | `UniversalAI/` |
| Probability Hypercube | 🔬 Experimental | `ProbabilityTheory/Hypercube/` |
| Graph Theory | 📝 Skeleton | `GraphTheory/` |

## Related Work

This project is developed alongside work in **Megalodon** (Church-encoded HOL + ZF).
Both interactive theorem provers are used for different formalization experiments.

## References

### Probability Theory
- Knuth & Skilling, "Foundations of Inference" (2012)
- Cox, "Probability, Frequency and Reasonable Expectation" (1946)
- Kolmogorov, "Foundations of the Theory of Probability" (1933)

### Information Theory
- Shannon, "A Mathematical Theory of Communication" (1948)
- Faddeev, "On the concept of entropy" (1956)

### Probabilistic Logic
- Goertzel et al., "Probabilistic Logic Networks" (2008)
- Walley, "Statistical Reasoning with Imprecise Probabilities" (1991)

### Universal AI
- Hutter, "Universal Artificial Intelligence" (2005)
- Legg & Hutter, "Universal Intelligence" (2007)

## Contributing

1. **Avoid `sorry`**: Use explicit `sorry` with TODO comments when unavoidable
2. **No axioms**: Keep foundations explicit
3. **Document sources**: Include textbook references
4. **Test compilation**: Run `lake build` frequently

## License

TBD
