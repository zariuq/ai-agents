/-
# Quantum Probability: Non-Commutative Probability Theory

Formalization of quantum probability as non-commutative probability theory,
based on von Neumann algebras and the algebraic approach to quantum mechanics.

## Key Insight: Commutativity Axis

In the hypercube of uncertainty theories:
- **Classical probability**: Commutative algebra of observables
- **Quantum probability**: Non-commutative algebra of observables

The fundamental new feature is **incompatible observables** (Heisenberg):
the algebra of measurements is non-commutative.

## Mathematical Structure

A **quantum probability space** is a pair (A, φ) where:
- A is a *-algebra (typically a von Neumann algebra or C*-algebra)
- φ : A → ℂ is a state (positive linear functional with φ(1) = 1)

**Random variables** are self-adjoint elements of A.
**Expectation** is E[X] = φ(X).

## Connection to Cox and K&S

Cox's theorem assumes commutativity: p(A∧B) = p(B∧A).
In quantum probability, measurements don't commute: A·B ≠ B·A.

## References

- von Neumann, J. "Mathematical Foundations of Quantum Mechanics" (1932)
- Meyer, P.A. "Quantum Probability for Probabilists" (1993)
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Complex.Basic

namespace Mettapedia.ProbabilityTheory.QuantumProbability

open scoped ComplexConjugate

/-!
## §1: Star Algebras (Foundation for Quantum Probability)
-/

/-- A star-algebra over ℂ: an algebra with an involution.
    In mathlib this is captured by `Star` and `StarRing`. Here we package
    the essential structure for quantum probability. -/
class QuantumAlgebra (A : Type*) extends Ring A, Algebra ℂ A, StarRing A, StarModule ℂ A

instance (A : Type*) [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] : QuantumAlgebra A where
  toRing := inferInstance
  toAlgebra := inferInstance
  toStarRing := inferInstance
  toStarModule := inferInstance

namespace QuantumAlgebra

variable {A : Type*} [QuantumAlgebra A]

/-- An element is self-adjoint if a* = a. These are the "observables". -/
def isSelfAdjoint (a : A) : Prop := star a = a

/-- The set of self-adjoint elements (observables). -/
def Observables (A : Type*) [QuantumAlgebra A] : Set A := { a | isSelfAdjoint a }

/-- Self-adjoint elements are closed under addition.
    (Requires star_add which needs StarAddMonoid structure) -/
theorem isSelfAdjoint_add {a b : A} (ha : isSelfAdjoint a) (hb : isSelfAdjoint b) :
    isSelfAdjoint (a + b) := by
  dsimp [isSelfAdjoint] at ha hb ⊢
  simp [ha, hb]

/-- The commutator [A, B] = AB - BA measures non-commutativity. -/
def commutator (a b : A) : A := a * b - b * a

/-- Commutator is anti-symmetric. -/
theorem commutator_antisymm (a b : A) : commutator a b = -commutator b a := by
  simp only [commutator, neg_sub]

/-- Elements commute iff their commutator is zero. -/
theorem commutes_iff_commutator_zero (a b : A) : a * b = b * a ↔ commutator a b = 0 := by
  simp only [commutator, sub_eq_zero]

end QuantumAlgebra

/-!
## §2: Quantum States
-/

/-- A state on a quantum algebra: positive linear functional with φ(1) = 1. -/
structure QuantumState (A : Type*) [QuantumAlgebra A] [One A] where
  /-- The linear functional -/
  φ : A →ₗ[ℂ] ℂ
  /-- Normalization: φ(1) = 1 -/
  normalized : φ 1 = 1
  /-- Compatibility with the involution: φ(a*) = conj(φ(a)). -/
  star_φ : ∀ a : A, φ (star a) = conj (φ a)
  /-- Positivity: φ(a* a) ≥ 0 for all a -/
  positive : ∀ a : A, 0 ≤ (φ (star a * a)).re

namespace QuantumState

variable {A : Type*} [QuantumAlgebra A] [One A]
variable (ρ : QuantumState A)

/-- Expectation of an observable. -/
def expectation (X : A) : ℂ := ρ.φ X

/-- For self-adjoint X, the expectation is real. -/
theorem expectation_real {X : A} (hX : QuantumAlgebra.isSelfAdjoint X) :
    (ρ.expectation X).im = 0 := by
  have hφ : ρ.φ (star X) = ρ.φ X := by
    simpa using congrArg (fun t : A => ρ.φ t) hX
  have h' : ρ.expectation X = conj (ρ.expectation X) := by
    have : ρ.φ X = conj (ρ.φ X) := hφ.symm.trans (ρ.star_φ X)
    simpa [expectation] using this
  have hconj : conj (ρ.expectation X) = ρ.expectation X := by
    simpa using h'.symm
  exact (Complex.conj_eq_iff_im).1 hconj

/-- Variance of an observable. -/
def variance (X : A) : ℝ :=
  (ρ.φ (star (X - ρ.expectation X • (1 : A)) * (X - ρ.expectation X • (1 : A)))).re

theorem variance_nonneg (X : A) : 0 ≤ ρ.variance X := by
  simpa [variance] using ρ.positive (X - ρ.expectation X • (1 : A))

end QuantumState

/-!
## §3: Quantum Probability Space
-/

/-- A quantum probability space: a *-algebra with a state. -/
structure QuantumProbabilitySpace where
  /-- The algebra of observables -/
  Algebra : Type*
  /-- Algebra structure -/
  [algInst : QuantumAlgebra Algebra]
  /-- Has a unit -/
  [oneInst : One Algebra]
  /-- The quantum state -/
  state : @QuantumState Algebra algInst oneInst

namespace QuantumProbabilitySpace

attribute [instance] QuantumProbabilitySpace.algInst QuantumProbabilitySpace.oneInst

variable (QPS : QuantumProbabilitySpace)

/-- The expectation functional. -/
def E : QPS.Algebra → ℂ := QPS.state.φ

/-- Two observables are compatible if they commute. -/
def areCompatible (X Y : QPS.Algebra) : Prop :=
  QuantumAlgebra.commutator X Y = (0 : QPS.Algebra)

/-- A quantum probability space is classical if all observables commute. -/
def isClassical : Prop :=
  ∀ X Y : QPS.Algebra, areCompatible QPS X Y

end QuantumProbabilitySpace

/-!
## §4: The Robertson Uncertainty Principle
-/

/-- The Robertson uncertainty inequality, expressed as a property of a state. -/
def RobertsonUncertainty {A : Type*} [QuantumAlgebra A] [One A]
    (ρ : QuantumState A) (X Y : A) : Prop :=
  ρ.variance X * ρ.variance Y ≥
    (Complex.normSq (ρ.expectation (QuantumAlgebra.commutator X Y))) / 4

/-- Commuting observables satisfy the Robertson inequality (trivial RHS). -/
theorem robertson_uncertainty_of_commutator_zero {A : Type*} [QuantumAlgebra A] [One A]
    (ρ : QuantumState A) (X Y : A) (hcomm : QuantumAlgebra.commutator X Y = 0) :
    RobertsonUncertainty ρ X Y := by
  have hRHS : (Complex.normSq (ρ.expectation (QuantumAlgebra.commutator X Y))) / 4 = 0 := by
    simp [QuantumState.expectation, hcomm]
  have hLHS : 0 ≤ ρ.variance X * ρ.variance Y :=
    mul_nonneg (ρ.variance_nonneg X) (ρ.variance_nonneg Y)
  -- `simp` converts the RHS to `0`.
  simpa [RobertsonUncertainty, hRHS] using hLHS

/-!
## §5: Connection to the Hypercube
-/

/-- The commutativity defect measures how far from classical. -/
def commutativityDefect {A : Type*} [QuantumAlgebra A] (X Y : A) : A :=
  QuantumAlgebra.commutator X Y

/-- Zero defect means classical (commutative) behavior. -/
theorem classical_iff_zero_defect {A : Type*} [QuantumAlgebra A] (X Y : A) :
    X * Y = Y * X ↔ commutativityDefect X Y = 0 :=
  QuantumAlgebra.commutes_iff_commutator_zero X Y

/-!
## §6: Finite-Dimensional Case (Matrix Algebras)
-/

/-- A finite-dimensional quantum system is described by n×n complex matrices. -/
abbrev MatrixAlgebra (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- A density matrix is a positive semidefinite matrix with trace 1. -/
structure DensityMatrix (n : ℕ) where
  /-- The matrix -/
  ρ : Matrix (Fin n) (Fin n) ℂ
  /-- Hermitian: ρ† = ρ -/
  hermitian : ρ.conjTranspose = ρ
  /-- Trace 1 -/
  trace_one : ρ.trace = 1
  /-- Positive semidefinite: ⟨v, ρv⟩ ≥ 0 for all v -/
  positive : ∀ v : Fin n → ℂ,
    0 ≤ (∑ i : Fin n, conj (v i) * (ρ.mulVec v) i).re

namespace DensityMatrix

variable {n : ℕ}

/-- Expectation of an observable in the density matrix state. -/
noncomputable def expectation (ρ : DensityMatrix n) (X : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (ρ.ρ * X).trace

/-- A pure state is a rank-1 density matrix: ρ = |ψ⟩⟨ψ|. -/
def isPure (ρ : DensityMatrix n) : Prop := (ρ.ρ * ρ.ρ).trace = 1

end DensityMatrix

/-!
## §7: Connection to Cox/K&S - The Commutativity Question

Cox's theorem assumes: p(A ∧ B | C) = p(B ∧ A | C)
In quantum mechanics: P_A · P_B ≠ P_B · P_A in general.

This is why quantum probability does NOT satisfy Cox's axioms.
-/

/-- The Cox-commutativity assumption fails in quantum mechanics.
    There exist quantum algebras with non-commuting observables. -/
theorem quantum_violates_cox_commutativity :
    ∃ (A : Type) (_ : QuantumAlgebra A) (X Y : A),
      QuantumAlgebra.commutator X Y ≠ 0 := by
  classical
  refine ⟨MatrixAlgebra 2, inferInstance, ?_, ?_, ?_⟩
  · exact Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)
  · exact Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ)
  intro h
  have h00 :
      (QuantumAlgebra.commutator
          (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))
          (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℂ)))
        (0 : Fin 2) (0 : Fin 2) = 0 := by
    simpa [MatrixAlgebra] using
      congrArg (fun M : MatrixAlgebra 2 => M (0 : Fin 2) (0 : Fin 2)) h
  have h10 : (1 : ℂ) = 0 := by
    -- Evaluate the (0,0) entry of the commutator explicitly.
    have h00' := h00
    simp [QuantumAlgebra.commutator] at h00'
  exact one_ne_zero h10

end Mettapedia.ProbabilityTheory.QuantumProbability
