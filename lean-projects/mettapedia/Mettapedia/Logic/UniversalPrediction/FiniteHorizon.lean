import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mettapedia.Logic.UniversalPrediction.PrefixMeasure

/-!
# Finite-horizon expectations for prefix measures (Hutter 2005, Chapter 3)

Hutter's Chapter 3 states many bounds in terms of expectations under a true environment `μ`
over length-`n` prefixes, e.g.

`Dₙ := ∑_{x : 𝔹ⁿ} μ(x) log (μ(x)/ξ(x))`.

Rather than developing full measure theory on `𝔹^ℕ`, we use the induced finite-horizon
distribution `PrefixMeasure.prefixPMF` from `PrefixMeasure.lean` and define expectations as
finite sums.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical BigOperators

namespace FiniteHorizon

/-- Expectation of a real-valued function on length-`n` bitstrings under a prefix measure `μ`. -/
noncomputable def expect (μ : PrefixMeasure) (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ x : Fin n → Bool, (prefixPMF μ n x).toReal * f x

/-- Expectation of a real-valued function of the *prefix list* `x : BinString` of length `n`. -/
noncomputable def expectPrefix (μ : PrefixMeasure) (n : ℕ) (f : BinString → ℝ) : ℝ :=
  ∑ x : Fin n → Bool, (prefixPMF μ n x).toReal * f (List.ofFn x)

theorem sum_toReal_eq_one {α : Type*} [Fintype α] (p : PMF α) :
    (∑ a : α, (p a).toReal) = 1 := by
  classical
  have hsum : (∑ a : α, p a) = 1 := by
    simpa [tsum_fintype] using (p.tsum_coe : (∑' a : α, p a) = 1)
  have htoReal :
      ENNReal.toReal (∑ a : α, p a) = ∑ a : α, (p a).toReal := by
    simpa using
      (ENNReal.toReal_sum (s := (Finset.univ : Finset α)) (f := fun a => p a) (by
        intro a ha
        simpa using p.apply_ne_top a))
  calc
    (∑ a : α, (p a).toReal) = ENNReal.toReal (∑ a : α, p a) := by
      simpa using htoReal.symm
    _ = ENNReal.toReal (1 : ENNReal) := by simp [hsum]
    _ = 1 := by simp

theorem sum_prefixPMF_toReal (μ : PrefixMeasure) (n : ℕ) :
    (∑ x : Fin n → Bool, (prefixPMF μ n x).toReal) = 1 :=
  sum_toReal_eq_one (p := prefixPMF μ n)

/-- A `Semimeasure` dominates a probability measure only with constant `c ≤ 1`. -/
theorem dominates_const_le_one {μ : PrefixMeasure} {ξ : Semimeasure} {c : ENNReal}
    (hdom : Dominates ξ μ c) : c ≤ 1 := by
  have hle : c ≤ ξ [] := by
    simpa [μ.root_eq_one', mul_one] using hdom []
  exact hle.trans (semimeasure_le_one ξ [])

/-- Pointwise log-likelihood ratio bound from dominance:

if `ξ(x) ≥ c * μ(x)` with `c > 0`, then `log(μ(x)/ξ(x)) ≤ log(1/c)`. -/
theorem log_ratio_le_log_inv_of_dominates (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0) (x : BinString) :
    Real.log ((μ x).toReal / (ξ x).toReal) ≤ Real.log (1 / c.toReal) := by
  have hc1 : c ≤ 1 := dominates_const_le_one (μ := μ) (ξ := ξ) hdom
  have hcTop : c ≠ (⊤ : ENNReal) := ne_top_of_le_ne_top ENNReal.one_ne_top hc1
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hcTop
  have hcReal_le_one : c.toReal ≤ 1 := by
    have := ENNReal.toReal_mono (hb := ENNReal.one_ne_top) hc1
    simpa using this
  have hone_le : (1 : ℝ) ≤ 1 / c.toReal := by
    have := one_div_le_one_div_of_le hcpos hcReal_le_one
    simpa using this
  by_cases hμ0 : μ x = 0
  · have : (0 : ℝ) ≤ Real.log (1 / c.toReal) := Real.log_nonneg hone_le
    simpa [hμ0] using this
  · have hξ0 : ξ x ≠ 0 := by
      intro hξ0
      have : μ x = 0 := Dominates.eq_zero_of_eq_zero (h := hdom) hc0 x hξ0
      exact hμ0 this
    have hμTop : μ x ≠ (⊤ : ENNReal) := by
      simpa using (semimeasure_ne_top μ.toSemimeasure x)
    have hξTop : ξ x ≠ (⊤ : ENNReal) := semimeasure_ne_top ξ x
    have hμpos : 0 < (μ x).toReal := ENNReal.toReal_pos hμ0 hμTop
    have hξpos : 0 < (ξ x).toReal := ENNReal.toReal_pos hξ0 hξTop
    have hratio_pos : 0 < (μ x).toReal / (ξ x).toReal := div_pos hμpos hξpos
    have hdomReal : c.toReal * (μ x).toReal ≤ (ξ x).toReal := by
      have h := ENNReal.toReal_mono (hb := hξTop) (hdom x)
      simpa [ENNReal.toReal_mul, mul_assoc] using h
    have hμ_le : (μ x).toReal ≤ (1 / c.toReal) * (ξ x).toReal := by
      have hmul : (μ x).toReal * c.toReal ≤ (ξ x).toReal := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hdomReal
      have hdiv : (μ x).toReal ≤ (ξ x).toReal / c.toReal := (le_div_iff₀ hcpos).2 hmul
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
    have hratio_le : (μ x).toReal / (ξ x).toReal ≤ 1 / c.toReal :=
      (div_le_iff₀ hξpos).2 hμ_le
    exact Real.log_le_log hratio_pos hratio_le

/-- Finite-horizon “prefix relative entropy”:

`Dₙ(μ‖ξ) = ∑_{x : 𝔹ⁿ} μ(x) log (μ(x) / ξ(x))`.

Here `μ` is a *measure* on cylinders (`PrefixMeasure`) while `ξ` is only assumed to be a
`Semimeasure` (as in Hutter's setting). -/
noncomputable def relEntropy (μ : PrefixMeasure) (ξ : Semimeasure) (n : ℕ) : ℝ :=
  expectPrefix μ n (fun x => Real.log ((μ x).toReal / (ξ x).toReal))

/-- Dominance bound on the finite-horizon prefix relative entropy:

if `ξ(x) ≥ c * μ(x)` for all prefixes and some `c > 0`, then `Dₙ(μ‖ξ) ≤ log(1/c)`. -/
theorem relEntropy_le_log_inv_of_dominates (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0) (n : ℕ) :
    relEntropy μ ξ n ≤ Real.log (1 / c.toReal) := by
  classical
  unfold relEntropy expectPrefix
  have hterm :
      ∀ x : Fin n → Bool,
        (prefixPMF μ n x).toReal *
            Real.log ((μ (List.ofFn x)).toReal / (ξ (List.ofFn x)).toReal) ≤
          (prefixPMF μ n x).toReal * Real.log (1 / c.toReal) := by
    intro x
    have hlog :=
      log_ratio_le_log_inv_of_dominates (μ := μ) (ξ := ξ) (hdom := hdom) (hc0 := hc0)
        (x := List.ofFn x)
    exact mul_le_mul_of_nonneg_left hlog ENNReal.toReal_nonneg
  have hsum :
      (∑ x : Fin n → Bool,
            (prefixPMF μ n x).toReal *
              Real.log ((μ (List.ofFn x)).toReal / (ξ (List.ofFn x)).toReal)) ≤
          ∑ x : Fin n → Bool, (prefixPMF μ n x).toReal * Real.log (1 / c.toReal) := by
    simpa using
      (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → Bool))) (fun x hx => hterm x))
  have hweights : (∑ x : Fin n → Bool, (prefixPMF μ n x).toReal) = 1 :=
    sum_prefixPMF_toReal (μ := μ) (n := n)
  calc
    (∑ x : Fin n → Bool,
          (prefixPMF μ n x).toReal *
            Real.log ((μ (List.ofFn x)).toReal / (ξ (List.ofFn x)).toReal))
        ≤ ∑ x : Fin n → Bool, (prefixPMF μ n x).toReal * Real.log (1 / c.toReal) := hsum
    _ = (∑ x : Fin n → Bool, (prefixPMF μ n x).toReal) * Real.log (1 / c.toReal) := by
          simpa using
            (Finset.sum_mul (s := (Finset.univ : Finset (Fin n → Bool)))
              (f := fun x => (prefixPMF μ n x).toReal) (a := Real.log (1 / c.toReal))).symm
    _ = Real.log (1 / c.toReal) := by simp [hweights]

end FiniteHorizon

end Mettapedia.Logic.UniversalPrediction
