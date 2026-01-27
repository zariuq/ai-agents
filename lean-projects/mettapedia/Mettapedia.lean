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
import Mettapedia.ProbabilityTheory.Cox
import Mettapedia.ProbabilityTheory.ImpreciseProbability
import Mettapedia.ProbabilityTheory.KnuthSkilling
import Mettapedia.ProbabilityTheory.OptimalTransport

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

-- Computability
import Mettapedia.Computability.KolmogorovComplexity.Basic
-- import Mettapedia.Computability.KolmogorovComplexity.Prefix  -- WIP (Phase 2)

-- Arithmetical Hierarchy (Grain of Truth - Phase 1)
import Mettapedia.Computability.ArithmeticalHierarchy.Basic
import Mettapedia.Computability.ArithmeticalHierarchy.Closure
import Mettapedia.Computability.ArithmeticalHierarchy.PolicyEncoding
import Mettapedia.Computability.ArithmeticalHierarchy.PolicyClasses

-- Logic
import Mettapedia.Logic.SolomonoffPrior
import Mettapedia.Logic.SolomonoffInduction
-- import Mettapedia.Logic.SolomonoffMeasure  -- WIP (outer measure construction is incomplete)
import Mettapedia.Logic.UniversalPrediction
import Mettapedia.Logic.PLNDistributional
import Mettapedia.Logic.PLNTemporal
import Mettapedia.Logic.PLNDeduction
import Mettapedia.Logic.PLNFrechetBounds
import Mettapedia.Logic.PLNQuantaleConnection
import Mettapedia.Logic.PLNEnrichedCategory
import Mettapedia.Logic.PLNEvidence
import Mettapedia.Logic.PLN_KS_Bridge
import Mettapedia.Logic.PLNDeductionComposition
import Mettapedia.Logic.TemporalQuantale

-- Universal AI (Hutter Chapters 2-7)
import Mettapedia.UniversalAI.SimplicityUncertainty
import Mettapedia.UniversalAI.BayesianAgents
import Mettapedia.UniversalAI.ProblemClasses
import Mettapedia.UniversalAI.TimeBoundedAIXI

-- Value Under Ignorance (Wyeth & Hutter 2025)
import Mettapedia.UniversalAI.ValueUnderIgnorance

-- Multi-Agent RL Framework (Grain of Truth - Phase 2)
import Mettapedia.UniversalAI.MultiAgent.JointActions
import Mettapedia.UniversalAI.MultiAgent.Environment
import Mettapedia.UniversalAI.MultiAgent.Policy
import Mettapedia.UniversalAI.MultiAgent.Value
import Mettapedia.UniversalAI.MultiAgent.BestResponse
import Mettapedia.UniversalAI.MultiAgent.Nash
import Mettapedia.UniversalAI.MultiAgent.Examples

-- Reflective Oracles (Grain of Truth - Core Infrastructure)
import Mettapedia.UniversalAI.ReflectiveOracles.Basic

-- Grain of Truth (Phase 4 - Infrastructure only)
import Mettapedia.UniversalAI.GrainOfTruth.Setup

-- Bridge (connects geometry to probability/logic)
import Mettapedia.Bridge.BitVectorEvidence

-- Examples
import Mettapedia.Examples.SymmetricMeasures
