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
import Mettapedia.MeasureTheory.Integration

-- Quantum Theory
import Mettapedia.QuantumTheory.FromSymmetry

-- Algebra
import Mettapedia.Algebra.QuantaleWeakness

-- Category Theory (Hypercube/OSLF framework for quantales)
import Mettapedia.CategoryTheory.FuzzyFrame
import Mettapedia.CategoryTheory.LambdaTheory
import Mettapedia.CategoryTheory.PLNInstance
import Mettapedia.CategoryTheory.NativeTypeTheory
import Mettapedia.CategoryTheory.PLNTerms
import Mettapedia.CategoryTheory.ModalTypes
import Mettapedia.CategoryTheory.Hypercube
import Mettapedia.CategoryTheory.PLNSemiringQuantale

-- Logic
import Mettapedia.Logic.SolomonoffPrior
import Mettapedia.Logic.PLNDistributional
import Mettapedia.Logic.PLNTemporal
import Mettapedia.Logic.PLNDeduction
import Mettapedia.Logic.PLNFrechetBounds
import Mettapedia.Logic.PLNQuantaleConnection
import Mettapedia.Logic.PLNEnrichedCategory
import Mettapedia.Logic.PLNEvidence
import Mettapedia.Logic.PLNDeductionComposition
import Mettapedia.Logic.TemporalQuantale

-- Bridge (connects geometry to probability/logic)
import Mettapedia.Bridge.BitVectorEvidence

-- Examples
import Mettapedia.Examples.SymmetricMeasures
