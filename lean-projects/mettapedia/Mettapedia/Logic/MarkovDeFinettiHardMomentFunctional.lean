import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Algebra.Module.Basic
import Mettapedia.Logic.MarkovDeFinettiHardRepresentability
import Mettapedia.Logic.MarkovDeFinettiRecurrence
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti (Hard Direction) — Finite Moment Functional Setup

This file sets up the **finite constraint functional** for the Markov de Finetti hard direction.
It does **not** solve the Diaconis–Freedman core; instead it packages the finite constraints as
an explicit continuous map into a finite product space, so the remaining existence step can be
stated cleanly.

The goal is to reduce `finite_constraints_nonempty` to a single statement:

> the constraint vector `wμ` lies in the image of the continuous map
>   `π ↦ (∫ Wnn n e dπ)` for the finite set of indices `u`.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

open MeasureTheory

namespace MarkovDeFinettiHard

variable {k : ℕ}

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence

/-! ## Finite constraint vectors -/

/-- The constraint vector `wμ` restricted to a finite index set `u`. -/
def constraintVec (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    (Subtype (fun p : Nat × MarkovState k => p ∈ (u : Set (Nat × MarkovState k))) → ENNReal) :=
  fun p => wμ (k := k) μ p.1.1 p.1.2

/-- The evaluation vector of a candidate mixing measure `π` on the same finite index set `u`. -/
def evalVec (_μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    ProbabilityMeasure (MarkovParam k) →
      (Subtype (fun p : Nat × MarkovState k => p ∈ (u : Set (Nat × MarkovState k))) → ENNReal) :=
  fun π p => ∫⁻ θ, Wnn (k := k) p.1.1 p.1.2 θ ∂π

lemma evalVec_apply (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k))
    (π : ProbabilityMeasure (MarkovParam k))
    (p : Subtype (fun p : Nat × MarkovState k => p ∈ (u : Set (Nat × MarkovState k)))) :
    evalVec (k := k) μ u π p = ∫⁻ θ, Wnn (k := k) p.1.1 p.1.2 θ ∂π := rfl

/-! ## Constraint sets vs evaluation vectors -/

lemma mem_constraintSet_iff_evalVec_eq
    (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k))
    (π : ProbabilityMeasure (MarkovParam k)) :
    π ∈ (⋂ p ∈ u, constraintSet (k := k) μ p.1 p.2)
      ↔ evalVec (k := k) μ u π = constraintVec (k := k) μ u := by
  classical
  constructor
  · intro h
    funext p
    have hp : π ∈ constraintSet (k := k) μ p.1.1 p.1.2 := by
      have h' : π ∈ ⋂ p ∈ u, constraintSet (k := k) μ p.1 p.2 := h
      exact Set.mem_iInter₂.1 h' p.1 p.property
    simpa [constraintSet, evalVec, constraintVec] using hp.symm
  · intro h
    -- Show membership in every constraint set.
    refine Set.mem_iInter₂.2 ?_
    intro p hp
    have := congrArg (fun f => f ⟨p, hp⟩) h
    -- Expand definitions.
    simpa [constraintSet, evalVec, constraintVec] using this.symm

lemma finite_constraints_nonempty_iff
    (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    (⋂ p ∈ u, constraintSet (k := k) μ p.1 p.2).Nonempty
      ↔ ∃ π : ProbabilityMeasure (MarkovParam k),
          evalVec (k := k) μ u π = constraintVec (k := k) μ u := by
  constructor
  · intro h
    rcases h with ⟨π, hπ⟩
    refine ⟨π, ?_⟩
    exact (mem_constraintSet_iff_evalVec_eq (k := k) μ u π).1 hπ
  · rintro ⟨π, hπ⟩
    refine ⟨π, ?_⟩
    exact (mem_constraintSet_iff_evalVec_eq (k := k) μ u π).2 hπ

/-! ## Continuity of the finite evaluation map -/

lemma continuous_evalVec (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    Continuous (evalVec (k := k) μ u) := by
  classical
  -- Continuity of a finite product of continuous maps.
  -- `fun π => (fun p => ∫ Wnn p dπ)` is continuous because each component is continuous.
  -- We use `continuous_pi` for the finite index set `u`.
  refine continuous_pi ?_
  intro p
  -- Each component is the `Wnn`-integral, which is continuous on `ProbabilityMeasure`.
  simpa [evalVec] using (continuous_lintegral_Wnn (k := k) p.1.1 p.1.2)

/-! ## Moment polytope and compactness -/

/-- The finite **moment polytope** for index set `u`: image of `evalVec`. -/
def momentPolytope (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    Set (Subtype (fun p : Nat × MarkovState k => p ∈ (u : Set (Nat × MarkovState k))) → ENNReal) :=
  Set.range (evalVec (k := k) μ u)

lemma constraintVec_mem_momentPolytope_iff
    (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    constraintVec (k := k) μ u ∈ momentPolytope (k := k) μ u
      ↔ ∃ π : ProbabilityMeasure (MarkovParam k),
          evalVec (k := k) μ u π = constraintVec (k := k) μ u := by
  rfl

lemma isCompact_momentPolytope (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k)) :
    IsCompact (momentPolytope (k := k) μ u) := by
  -- Continuous image of a compact space.
  have hcont : Continuous (evalVec (k := k) μ u) := continuous_evalVec (k := k) μ u
  have hcompact : IsCompact (Set.univ : Set (ProbabilityMeasure (MarkovParam k))) := isCompact_univ
  -- `Set.range` is the image of `Set.univ`.
  simpa [momentPolytope, Set.image_univ] using hcompact.image hcont

/-! ## Affine closure under two-point mixtures (convexity lemma) -/

-- A two-point mixture of probability measures with ENNReal weights.
def mixProb (a b : ENNReal) (h : a + b = 1)
    (pi1 pi2 : ProbabilityMeasure (MarkovParam k)) : ProbabilityMeasure (MarkovParam k) :=
  ⟨a • (pi1 : Measure (MarkovParam k)) + b • (pi2 : Measure (MarkovParam k)), by
      -- Probability measure: total mass is `a + b = 1`.
      have h1 :
          (a • (pi1 : Measure (MarkovParam k)) + b • (pi2 : Measure (MarkovParam k))) Set.univ = 1 := by
        -- Use linearity of measures on `univ`.
        simp [Measure.add_apply, Measure.smul_apply, h]
      exact IsProbabilityMeasure.mk h1⟩

lemma evalVec_mix (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k))
    (a b : ENNReal) (h : a + b = 1)
    (pi1 pi2 : ProbabilityMeasure (MarkovParam k)) :
    evalVec (k := k) μ u (mixProb (k := k) a b h pi1 pi2)
      = fun p => a * evalVec (k := k) μ u pi1 p + b * evalVec (k := k) μ u pi2 p := by
  classical
  funext p
  -- Expand definitions and use linearity of the `lintegral`.
  simp [evalVec, mixProb, lintegral_add_measure, lintegral_smul_measure]

lemma momentPolytope_closed_under_mix
    (μ : PrefixMeasure (Fin k)) (u : Finset (Nat × MarkovState k))
    (a b : ENNReal) (h : a + b = 1)
    {x y :
      Subtype (fun p : Nat × MarkovState k => p ∈ (u : Set (Nat × MarkovState k))) → ENNReal}
    (hx : x ∈ momentPolytope (k := k) μ u)
    (hy : y ∈ momentPolytope (k := k) μ u) :
    (fun p => a * x p + b * y p) ∈ momentPolytope (k := k) μ u := by
  rcases hx with ⟨pi1, rfl⟩
  rcases hy with ⟨pi2, rfl⟩
  refine ⟨mixProb (k := k) a b h pi1 pi2, ?_⟩
  -- Use linearity of `evalVec` under mixtures.
  simp [evalVec_mix (k := k) (μ := μ) (u := u) a b h]

/-! ## Core finite satisfiability lemma (Diaconis–Freedman) -/

/--
The **finite satisfiability core**: for any finite index set `u`, the constraint vector `wμ`
lies in the moment polytope (the image of `evalVec`).

This is the precise finite-dimensional content of the Diaconis–Freedman hard direction.
It is isolated here as a single lemma so the rest of the proof can proceed by compactness.
-/
theorem constraintVec_mem_momentPolytope
    (μ : PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (u : Finset (Nat × MarkovState k)) :
    constraintVec (k := k) μ u ∈ momentPolytope (k := k) μ u := by
  -- TODO (Diaconis–Freedman 1980): finite satisfiability of Markov-exchangeable constraints.
  -- This is the substantive new content: show the finite moment vector is realized by some
  -- Markov parameter measure on `MarkovParam k`.
  --
  -- Expected approach: a finite-dimensional convexity/representation argument using evidence
  -- partitions (see MarkovDeFinettiEvidenceBasis), or a moment-functional/Riesz construction
  -- restricted to the finite subalgebra generated by the indices in `u`.
  sorry

end MarkovDeFinettiHard

end Mettapedia.Logic
