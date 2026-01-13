import Mettapedia.ProbabilityTheory.QuantumProbability.Basic

/-!
# Quantum Probability

This module provides a formalization of quantum probability as non-commutative
probability theory based on operator algebras.

## Files

- `Basic.lean`: Core definitions (quantum algebras, states, observables, uncertainty)

## Connection to Other Modules

- `Cox/`: Quantum probability violates Cox's commutativity assumption
- `KnuthSkilling/`: K&S assumes commutativity (implicitly via lattice structure)
- `Unified.lean`: Quantum sits at the (additive, non-commutative) vertex

## Key Insight

The fundamental difference from classical probability is that observables
(self-adjoint operators) do not commute: AB ≠ BA in general.

This leads to:
- Order-dependent sequential measurements
- Robertson uncertainty principle
- No joint probability distributions for incompatible observables

## References

- von Neumann, J. "Mathematical Foundations of Quantum Mechanics" (1932)
- Meyer, P.A. "Quantum Probability for Probabilists" (1993)
-/
