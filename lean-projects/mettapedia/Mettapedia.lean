/-
# Mettapedia - Encyclopedia of Formalized Mathematics

A comprehensive formalization of mathematics across multiple domains,
inspired by Wikipedia's breadth and Metamath's rigor.

## Project Structure

- **GraphTheory/**: Graph theory (Bondy & Murty, Diestel)
- **ProbabilityTheory/**: Probability theory (Kolmogorov, Billingsley, Durrett)
- **SetTheory/**: Set theory foundations
- **Combinatorics/**: Combinatorial mathematics
- **NumberTheory/**: Number theory
- **Topology/**: Topological spaces
- **Algebra/**: Algebraic structures
- **Logic/**: Mathematical logic
- **Analysis/**: Real and complex analysis

## Tools

- **LeanHammer**: ATP integration (Zipperposition prover)
- **Mathlib**: Lean's standard math library

-/

-- Graph Theory
import Mettapedia.GraphTheory.Basic

-- Probability Theory
import Mettapedia.ProbabilityTheory.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling

-- Measure Theory
import Mettapedia.MeasureTheory.FromSymmetry
