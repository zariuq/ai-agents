import Mettapedia.Logic.MarkovDeFinettiHard

/-!
# Markov de Finetti Hard Direction: Anchor-Theorem Adapter

This file provides a minimal adapter for using an external
successor-matrix/anchor-invariance theorem statement as an input hypothesis.
It does not add any axioms and does not replace the quantitative route-A
pipeline in `MarkovDeFinettiHard`.
-/

noncomputable section

namespace Mettapedia.Logic

open MeasureTheory

namespace MarkovDeFinettiHard

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence

variable {k : ℕ}

/-- External anchor-invariance theorem interface (e.g. successor-matrix style):
Markov exchangeability + recurrence imply a Markov-mixture representation. -/
def AnchorInvariantSuccessorMatrixTheorem (k : ℕ) : Prop :=
  ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k)),
    MarkovExchangeablePrefixMeasure (k := k) μ →
    MarkovRecurrentPrefixMeasure (k := k) μ →
      ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
        ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi

/-- Route-A large-`R` direct pattern-rate hypothesis on realizable short states,
factored out as a reusable proposition alias. -/
def LargeRPatternRateOnRealizableShortState (k : ℕ) : Prop :=
  ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
    e ∈ stateFinset k (Nat.succ n) →
      ∃ Clarge : ℝ, 0 ≤ Clarge ∧
        (∀ {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k),
          s ∈ stateFinset k N →
            0 < returnsToStart (k := k) s →
            (4 * (Nat.succ n) * (Nat.succ n)) < returnsToStart (k := k) s →
              (∑ p ∈ MarkovDeFinettiHardBEST.excursionPatternSet (k := k) (hN := hN) e s,
                |(MarkovDeFinettiHardBEST.wrPatternMass (k := k) hk n e s p).toReal -
                  (MarkovDeFinettiHardBEST.worPatternMass (k := k) (hN := hN) e s p).toReal|) ≤
                Clarge / (returnsToStart (k := k) s : ℝ))

/-- Adapter: if the anchor-invariance theorem is available as a hypothesis,
the hard-direction conclusion follows directly for the given `μ`. -/
theorem markovDeFinetti_hard_of_anchorInvariantSuccessorMatrix
    (hAnchor : AnchorInvariantSuccessorMatrixTheorem k)
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi :=
  hAnchor μ hμ hrec

/-- Adapter back to the existing quantitative route-A endpoint using the
factored large-`R` realizable-short-state hypothesis alias. -/
theorem markovDeFinetti_hard_of_largeRPatternRateOnRealizableShortState
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hlarge : LargeRPatternRateOnRealizableShortState k) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi :=
  markovDeFinetti_hard_of_largeR_patternRate_via_canonical_on_realizable_shortState_rowL1StartTarget
    (k := k) (μ := μ) hμ hrec hlarge

/-- Unified entrypoint:
either the anchor-invariance theorem or the quantitative large-`R` route-A
hypothesis yields the hard-direction conclusion. -/
theorem markovDeFinetti_hard_of_anchorInvariant_or_largeRPatternRate
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (h :
      AnchorInvariantSuccessorMatrixTheorem k ∨
        LargeRPatternRateOnRealizableShortState k) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  rcases h with hAnchor | hlarge
  · exact markovDeFinetti_hard_of_anchorInvariantSuccessorMatrix
      (k := k) hAnchor μ hμ hrec
  · exact markovDeFinetti_hard_of_largeRPatternRateOnRealizableShortState
      (k := k) (μ := μ) hμ hrec hlarge

end MarkovDeFinettiHard
end Mettapedia.Logic
