import Mettapedia.Logic.MarkovDeFinettiRecurrence
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti (Recurrence Theorem Placeholder)

This file isolates the **recurrence implication** that is expected to complete the
Diaconis–Freedman hard direction:

> Markov exchangeability ⇒ recurrence (condition (4) in Diaconis–Freedman 1980).

We keep this as a **single explicit sorry** so it is surfaced by builds and easy to track.
No implicit axioms or “provable assumptions” are used elsewhere.
-/

noncomputable section

namespace Mettapedia.Logic

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence

variable {k : ℕ}

/-!
## TODO: Prove recurrence for Markov-exchangeable prefix measures

This is the missing implication that upgrades the hard direction to the full
Diaconis–Freedman statement. It should be proven by constructing an infinite‑path measure
extending the prefix measure and verifying the recurrence event holds a.s.

Until this proof is completed, `markovDeFinetti_hard` correctly *assumes* recurrence,
and this lemma remains the explicit TODO.
-/
theorem markov_exchangeable_implies_recurrent
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ) :
    MarkovRecurrentPrefixMeasure (k := k) μ := by
  -- TODO (Diaconis–Freedman 1980): construct an extension to infinite trajectories
  -- and prove the recurrence event has probability 1.
  sorry

end Mettapedia.Logic
