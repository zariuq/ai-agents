import Mettapedia.Logic.MarkovDeFinettiRecurrence
import Mettapedia.Logic.MarkovDeFinettiHardBase
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti Anchor Adapter (clean active module)

Minimal sound adapter for using an external anchor-invariance/successor-matrix
theorem as a hypothesis.
-/

noncomputable section

namespace Mettapedia.Logic

open MeasureTheory

namespace MarkovDeFinettiHard

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence

variable {k : ℕ}

/-- External anchor-invariance theorem interface:
Markov exchangeability + recurrence imply Markov-mixture representation. -/
def AnchorInvariantSuccessorMatrixTheorem (k : ℕ) : Prop :=
  ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k)),
    MarkovExchangeablePrefixMeasure (k := k) μ →
    MarkovRecurrentPrefixMeasure (k := k) μ →
      ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
        ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi

/-- Adapter theorem: consume an external anchor theorem hypothesis directly. -/
theorem markovDeFinetti_hard_of_anchorInvariantSuccessorMatrix
    (hAnchor : AnchorInvariantSuccessorMatrixTheorem k)
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi :=
  hAnchor μ hμ hrec

end MarkovDeFinettiHard
end Mettapedia.Logic
