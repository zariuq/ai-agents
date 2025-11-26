/-
# Probability Theory - Kolmogorov Foundations

Refactored to use mathlib's probability infrastructure.
We work with `Measure` and `ProbabilityMeasure` directly instead of bespoke
structures.
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Real.Basic

set_option linter.unusedSectionVars false

noncomputable section

namespace Mettapedia.ProbabilityTheory
open MeasureTheory
open Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Probability of the empty event for any measure. -/
theorem prob_empty (μ : Measure Ω) : μ ∅ = 0 := by
  simp

variable (μ : Measure Ω)

/-- Probability is monotone with respect to set inclusion (valid for any measure). -/
theorem prob_mono {A B : Set Ω} (hAB : A ⊆ B) : μ A ≤ μ B :=
  measure_mono hAB

/-- Union bound (sub-additivity) for any events. -/
theorem prob_union_le {A B : Set Ω} :
    μ (A ∪ B) ≤ μ A + μ B :=
  measure_union_le A B

variable (μ : Measure Ω) [IsProbabilityMeasure μ] [IsFiniteMeasure μ]

/-- Probability of the complement of a measurable event. -/
theorem prob_compl {A : Set Ω} (hA : MeasurableSet A) :
    μ Aᶜ = 1 - μ A := by
  have h := measure_compl (μ := μ) hA
  simpa [IsProbabilityMeasure.measure_univ (μ := μ)] using h

/-- Classical conditional probability (values in `ℝ`). -/
def condProb (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Set Ω) : ℝ :=
  if _ : μ B = 0 then 0 else μ.real (A ∩ B) / μ.real B

/-- Helper: real-valued measure of a set is nonzero if the measure is nonzero. -/
lemma measureReal_ne_zero_of_measure_ne_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Set Ω} (hA : μ A ≠ 0) : μ.real A ≠ 0 := by
  intro h
  have h' : μ A = 0 :=
    (measureReal_eq_zero_iff (μ := μ) (s := A)).1 h
  exact hA h'

/-- Product rule: `P(A ∩ B) = P(A | B) * P(B)` provided `P(B) ≠ 0`. -/
theorem product_rule {A B : Set Ω} (hB : μ B ≠ 0) :
    μ.real (A ∩ B) = condProb μ A B * μ.real B := by
  have hBreal : μ.real B ≠ 0 := measureReal_ne_zero_of_measure_ne_zero (μ := μ) hB
  calc
    μ.real (A ∩ B)
        = μ.real (A ∩ B) * (μ.real B / μ.real B) := by field_simp [hBreal]
    _ = (μ.real (A ∩ B) / μ.real B) * μ.real B := by ring
    _ = condProb μ A B * μ.real B := by simp [condProb, hB]

/-- Bayes' theorem in the two-event form. -/
theorem bayes {A B : Set Ω} (hA : μ A ≠ 0) (hB : μ B ≠ 0) :
    condProb μ A B = condProb μ B A * μ.real A / μ.real B := by
  have hAreal : μ.real A ≠ 0 := measureReal_ne_zero_of_measure_ne_zero (μ := μ) hA
  have hBreal : μ.real B ≠ 0 := measureReal_ne_zero_of_measure_ne_zero (μ := μ) hB
  calc
    condProb μ A B
        = μ.real (A ∩ B) / μ.real B := by simp [condProb, hB]
    _ = μ.real (A ∩ B) / μ.real A * μ.real A / μ.real B := by
          field_simp [hAreal, hBreal]
    _ = μ.real (B ∩ A) / μ.real A * μ.real A / μ.real B := by
          rw [inter_comm]
    _ = condProb μ B A * μ.real A / μ.real B := by
          simp [condProb, hA]

/-- Law of total probability for a binary partition, assuming both parts have positive measure. -/
theorem total_probability_binary {A B : Set Ω}
    (_hA : MeasurableSet A) (hB : MeasurableSet B)
    (hBpos : μ B ≠ 0) (hBcomplPos : μ Bᶜ ≠ 0) :
    μ.real A = condProb μ A B * μ.real B + condProb μ A Bᶜ * μ.real Bᶜ := by
  have hdecomp :=
    measureReal_inter_add_diff₀ (μ := μ) (s := A) (t := B) hB.nullMeasurableSet
      (h := by finiteness)
  have hcompl : A \ B = A ∩ Bᶜ := by
    ext x; constructor <;> intro hx <;> exact ⟨hx.1, hx.2⟩
  have h1 := product_rule (μ := μ) (A := A) (B := B) hBpos
  have h2 := product_rule (μ := μ) (A := A) (B := Bᶜ) hBcomplPos
  calc
    μ.real A
        = μ.real (A ∩ B) + μ.real (A ∩ Bᶜ) := by
            simpa [hcompl, add_comm] using hdecomp.symm
    _ = condProb μ A B * μ.real B + condProb μ A Bᶜ * μ.real Bᶜ := by
            simp [h1, h2]

end Mettapedia.ProbabilityTheory
