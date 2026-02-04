import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mettapedia.Logic.MarkovDeFinettiHardBase
import Mettapedia.Logic.MarkovDeFinettiEvidenceBasis
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure

/-!
# Markov de Finetti (Hard Direction) — Representability Infrastructure

This file does **not** prove the Diaconis–Freedman hard direction yet.

It packages the reusable, proof-friendly analytic lemmas needed to *state* the hard direction as a
representability problem on the compact space `MarkovParam k`:

* evidence polynomials `W n e` are continuous,
* it is convenient to also work with the `ℝ≥0`-valued version `Wnn n e`,
* the map `π ↦ ∫ Wnn n e dπ` is continuous on `ProbabilityMeasure (MarkovParam k)`,
  hence the corresponding moment constraints define closed sets.

The remaining hard content is the **existence** of a `π` satisfying *all* constraints; that is
still isolated as a single `sorry` in `Mettapedia.Logic.MarkovDeFinettiHard`.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators
open scoped NNReal ENNReal

open MeasureTheory

namespace MarkovDeFinettiHard

variable {k : ℕ}

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet

/-! ## `ℝ≥0`-valued evidence polynomials -/

/-- The `ℝ≥0`-valued version of the evidence polynomial `W`.

This is often more convenient for weak-* topology lemmas on `ProbabilityMeasure`, because Mathlib’s
continuity theorems are stated for `ℝ≥0`-valued continuous functions. -/
def Wnn (n : ℕ) (e : MarkovState k) : MarkovParam k → ℝ≥0 :=
  fun θ =>
    ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
      wordProbNN (k := k) θ (trajToList (k := k) xs)

@[simp] lemma Wnn_nonneg (n : ℕ) (e : MarkovState k) (θ : MarkovParam k) :
    0 ≤ Wnn (k := k) n e θ := by
  classical
  simp [Wnn]

@[simp] lemma coe_Wnn (n : ℕ) (e : MarkovState k) (θ : MarkovParam k) :
    (Wnn (k := k) n e θ : ℝ≥0∞) = W (k := k) n e θ := by
  classical
  -- Both sides are the same finite sum, just performed in different codomains.
  simp [Wnn, W, wordProb]

theorem continuous_Wnn (n : ℕ) (e : MarkovState k) :
    Continuous (fun θ : MarkovParam k => Wnn (k := k) n e θ) := by
  classical
  -- Finite sum of continuous `wordProbNN` terms.
  refine continuous_finset_sum (s :=
    (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e)) ?_
  intro xs hxs
  simpa [Wnn] using (continuous_wordProbNN (k := k) (xs := trajToList (k := k) xs))

/-! ## Continuity of `π ↦ ∫ Wnn n e dπ` on `ProbabilityMeasure` -/

theorem continuous_lintegral_Wnn (n : ℕ) (e : MarkovState k) :
    Continuous (fun π : ProbabilityMeasure (MarkovParam k) => ∫⁻ θ, Wnn (k := k) n e θ ∂π) := by
  classical
  -- Use Mathlib's weak-* continuity lemma for `ℝ≥0`-valued continuous functions.
  have hcont : Continuous (fun θ : MarkovParam k => Wnn (k := k) n e θ) :=
    continuous_Wnn (k := k) n e
  -- Package as a `ContinuousMap` to use the dedicated lemma.
  let f : C(MarkovParam k, ℝ≥0) := ⟨fun θ => Wnn (k := k) n e θ, hcont⟩
  simpa [f] using (ProbabilityMeasure.continuous_lintegral_continuousMap (X := MarkovParam k) f)

/-! ## Closed constraint sets (useful for compactness arguments) -/

/-- The (single) evidence constraint set at horizon `n` and evidence state `e`. -/
def constraintSet (μ : FiniteAlphabet.PrefixMeasure (Fin k)) (n : ℕ) (e : MarkovState k) :
    Set (ProbabilityMeasure (MarkovParam k)) :=
  {π | wμ (k := k) μ n e = ∫⁻ θ, Wnn (k := k) n e θ ∂π}

theorem isClosed_constraintSet (μ : FiniteAlphabet.PrefixMeasure (Fin k)) (n : ℕ) (e : MarkovState k) :
    IsClosed (constraintSet (k := k) μ n e) := by
  classical
  -- Preimage of a singleton under a continuous function.
  have hcont :
      Continuous (fun π : ProbabilityMeasure (MarkovParam k) => ∫⁻ θ, Wnn (k := k) n e θ ∂π) :=
    continuous_lintegral_Wnn (k := k) n e
  -- Rewrite the set as a fiber of the continuous map.
  have :
      constraintSet (k := k) μ n e =
        (fun π : ProbabilityMeasure (MarkovParam k) => ∫⁻ θ, Wnn (k := k) n e θ ∂π) ⁻¹'
          {wμ (k := k) μ n e} := by
    ext π
    simp [constraintSet, eq_comm]
  -- `{a}` is closed in `ℝ≥0∞` and continuity gives closedness of the preimage.
  simpa [this] using (isClosed_singleton.preimage hcont)

/-! ## Compactness reduction: from finite satisfiability to global satisfiability -/

/-- If every **finite** set of evidence constraints is satisfiable by some probability measure on
`MarkovParam k`, then there exists a probability measure satisfying **all** constraints.

This isolates the remaining hard content of the Markov de Finetti theorem into a single
finite-dimensional satisfiability statement. -/
theorem exists_probabilityMeasure_of_finite_constraints
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hfin :
      ∀ u : Finset (ℕ × MarkovState k),
        (⋂ p ∈ u, constraintSet (k := k) μ p.1 p.2).Nonempty) :
    ∃ π : ProbabilityMeasure (MarkovParam k),
      ∀ n : ℕ, ∀ e : MarkovState k, wμ (k := k) μ n e = ∫⁻ θ, Wnn (k := k) n e θ ∂π := by
  classical
  let t : (ℕ × MarkovState k) → Set (ProbabilityMeasure (MarkovParam k)) :=
    fun p => constraintSet (k := k) μ p.1 p.2
  have ht_closed : ∀ p, IsClosed (t p) := by
    intro p
    exact isClosed_constraintSet (k := k) (μ := μ) p.1 p.2
  -- `ProbabilityMeasure (MarkovParam k)` is compact since `MarkovParam k` is compact.
  have hs : IsCompact (Set.univ : Set (ProbabilityMeasure (MarkovParam k))) := isCompact_univ
  have hst :
      ∀ u : Finset (ℕ × MarkovState k),
        (Set.univ ∩ ⋂ p ∈ u, t p).Nonempty := by
    intro u
    simpa [t] using (hfin u)
  -- Compactness + finite intersection property ⇒ nonempty full intersection.
  rcases (hs.inter_iInter_nonempty t ht_closed hst) with ⟨π, hπ⟩
  refine ⟨π, ?_⟩
  intro n e
  -- Unpack membership in the intersection.
  have hAll : π ∈ ⋂ p, t p := hπ.2
  have hOne : π ∈ t (n, e) := (Set.mem_iInter.1 hAll (n, e))
  simpa [t, constraintSet] using hOne

end MarkovDeFinettiHard

end Mettapedia.Logic
