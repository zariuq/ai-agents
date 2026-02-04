import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure

/-!
# Markov de Finetti (Recurrence Assumption)

Diaconis–Freedman (1980) show that **Markov exchangeability** alone is not sufficient to
guarantee a mixture-of-Markov-chains representation unless one adds a **recurrence**
assumption (see their condition (4) and Theorem 7).

This file packages a *prefix-measure level* recurrence assumption in a way that can be
used by the hard-direction theorem:

* a prefix measure `μ` is **recurrent** if it extends to a probability measure on infinite
  trajectories and that extension returns to the initial state infinitely often (a.s.).

Important: this is **only a hypothesis**. We do **not** assume or postulate any theorem
that produces recurrence. Any future proof that a given class of prefix measures is
recurrent should live in a separate file and be stated as a theorem (not an axiom).
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical
open MeasureTheory

namespace MarkovDeFinettiRecurrence

variable {k : ℕ}

/-! ## Cylinder sets on infinite trajectories -/

/-- Cylinder set for a finite word `xs` in the space of infinite trajectories. -/
def cylinder (xs : List (Fin k)) : Set (ℕ → Fin k) :=
  { ω | ∀ i : Fin xs.length, ω i = xs.get i }

/-! ## Recurrence event -/

/-- The event that the trajectory returns to its initial state infinitely often. -/
def recurrentEvent : Set (ℕ → Fin k) :=
  { ω | Set.Infinite { n : ℕ | ω n = ω 0 } }

/-! ## Recurrence for prefix measures -/

/--
A prefix measure `μ` is **Markov-recurrent** if it extends to a probability measure on
infinite trajectories such that the recurrence event holds almost surely.

This mirrors Diaconis–Freedman’s recurrence condition (4):
`P{ X_n = X_0 for infinitely many n } = 1`.
-/
def MarkovRecurrentPrefixMeasure
    (μ : Mettapedia.Logic.UniversalPrediction.FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
    (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
    P (recurrentEvent (k := k)) = 1

end MarkovDeFinettiRecurrence

end Mettapedia.Logic
