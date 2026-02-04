import Mettapedia.ProbabilityTheory.HigherOrderProbability.Basic
import Mettapedia.Logic.DeFinetti
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# De Finetti as Kyburg Flattening

This file packages the Bernoulli-mixture model from `Mettapedia.Logic.DeFinetti` as an instance of
Kyburg's higher-order probability structure (`ParametrizedDistribution`).

The key theorem is the singleton-level identification:

`flatten(pd_M n) {xs} = ENNReal.ofReal (M.prob xs)`.

This is the precise "De Finetti is Kyburg" bridge needed by the higher-order PLN story.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.ProbabilityTheory.HigherOrderProbability

open scoped BigOperators ENNReal ProbabilityTheory

open MeasureTheory ProbabilityTheory

namespace DeFinettiConnection

open Mettapedia.Logic.DeFinetti
open Mettapedia.Logic.Exchangeability

/-! ## Parameter space and mixing measure -/

abbrev Theta : Type := Set.Icc (0 : ℝ) 1

lemma measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1) := by
  simp [isClosed_Icc.measurableSet]

@[simp] lemma Theta.coe_mk (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((⟨x, hx⟩ : Theta) : ℝ) = x := rfl

/-- Pull a mixing measure supported on `[0,1]` back to the subtype `Theta = Icc 0 1`. -/
def mixingMeasureTheta (M : BernoulliMixture) : Measure Theta :=
  M.mixingMeasure.comap (fun θ : Theta => (θ : ℝ))

instance mixingMeasureTheta_isProbability (M : BernoulliMixture) :
    IsProbabilityMeasure (mixingMeasureTheta M) := by
  classical
  haveI : IsProbabilityMeasure M.mixingMeasure := M.isProbability
  -- Evaluate on `univ` by rewriting `comap` along the subtype coercion.
  have hIcc :
      mixingMeasureTheta M Set.univ = M.mixingMeasure (Set.Icc (0 : ℝ) 1) := by
    -- `comap_subtype_coe_apply` identifies the pullback with the image set.
    simpa [mixingMeasureTheta, Theta, measurableSet_Icc] using
      (comap_subtype_coe_apply (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc
        (μ := M.mixingMeasure) (t := (Set.univ : Set (Set.Icc (0 : ℝ) 1))))
  -- Since `M.mixingMeasure` is a probability measure supported on `Icc 0 1`,
  -- the measure of `Icc 0 1` is `1`.
  have hIcc_one : M.mixingMeasure (Set.Icc (0 : ℝ) 1) = 1 := by
    have hIcc_eq_univ : M.mixingMeasure (Set.Icc (0 : ℝ) 1) = M.mixingMeasure Set.univ := by
      simpa using
        (MeasureTheory.measure_of_measure_compl_eq_zero (μ := M.mixingMeasure) (s := Set.Icc (0 : ℝ) 1)
          M.support_unit)
    simpa [measure_univ] using hIcc_eq_univ
  -- Finish.
  refine ⟨?_⟩
  simp [hIcc, hIcc_one]

/-! ## Bernoulli product kernel as a Markov kernel -/

section Kernel

variable {n : ℕ}

private lemma theta_nonneg (θ : Theta) : 0 ≤ (θ : ℝ) := θ.2.1
private lemma theta_le_one (θ : Theta) : (θ : ℝ) ≤ 1 := θ.2.2
private lemma one_sub_theta_nonneg (θ : Theta) : 0 ≤ 1 - (θ : ℝ) :=
  sub_nonneg.2 (theta_le_one θ)

private lemma bernoulliPMF_nonneg (θ : Theta) (b : Bool) :
    0 ≤ bernoulliPMF (θ : ℝ) b := by
  cases b with
  | false =>
      simpa [bernoulliPMF] using one_sub_theta_nonneg (θ := θ)
  | true =>
      simpa [bernoulliPMF] using theta_nonneg (θ := θ)

/-- The `ENNReal` weight of a word `xs` under a parameter `θ`. -/
def weight (θ : Theta) (xs : Fin n → Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (bernoulliProductPMF (θ : ℝ) xs)

private lemma weight_cons (θ : Theta) (b : Bool) (xs : Fin n → Bool) :
    weight (n := n + 1) θ (Fin.cons b xs) =
      ENNReal.ofReal (bernoulliPMF (θ : ℝ) b) * weight (n := n) θ xs := by
  classical
  -- Split the product on `Fin (n+1)` into head and tail.
  have hprod :
      bernoulliProductPMF (θ : ℝ) (Fin.cons b xs) =
        bernoulliPMF (θ : ℝ) b * bernoulliProductPMF (θ : ℝ) xs := by
    unfold bernoulliProductPMF
    -- `Fin.prod_univ_succ` isolates the `0`-th coordinate.
    simpa using
      (Fin.prod_univ_succ (n := n)
        (f := fun i : Fin (n + 1) =>
          bernoulliPMF (θ : ℝ) ((Fin.cons b xs : Fin (n + 1) → Bool) i)))
  -- Move `ENNReal.ofReal` across multiplication; the head factor is nonnegative on `Theta`.
  have hnonneg : 0 ≤ bernoulliPMF (θ : ℝ) b := bernoulliPMF_nonneg (θ := θ) b
  simp [weight, hprod, ENNReal.ofReal_mul hnonneg]

private lemma ofReal_bernoulliPMF_add (θ : Theta) :
    ENNReal.ofReal (bernoulliPMF (θ : ℝ) true) + ENNReal.ofReal (bernoulliPMF (θ : ℝ) false) = 1 := by
  have hθ : 0 ≤ (θ : ℝ) := theta_nonneg θ
  have h1θ : 0 ≤ 1 - (θ : ℝ) := one_sub_theta_nonneg θ
  -- `bernoulliPMF θ true = θ`, `bernoulliPMF θ false = 1-θ`.
  have hsum : (θ : ℝ) + (1 - (θ : ℝ)) = (1 : ℝ) := by ring
  have : ENNReal.ofReal (θ : ℝ) + ENNReal.ofReal (1 - (θ : ℝ)) = 1 := by
    -- Rewrite the sum as `ofReal (θ + (1-θ))` and use `hsum`.
    calc
      ENNReal.ofReal (θ : ℝ) + ENNReal.ofReal (1 - (θ : ℝ))
          = ENNReal.ofReal ((θ : ℝ) + (1 - (θ : ℝ))) := by
              simpa using (ENNReal.ofReal_add hθ h1θ).symm
      _ = 1 := by simp [hsum]
  simpa [bernoulliPMF] using this

private lemma sum_weight_eq_one : ∀ (n : ℕ) (θ : Theta), (∑ xs : Fin n → Bool, weight (n := n) θ xs) = 1
  | 0, θ => by
      classical
      -- Only one word on `Fin 0`.
      simp [weight, bernoulliProductPMF]
  | Nat.succ n, θ => by
      classical
      -- Rewrite the sum over words using `Fin.consEquiv` (head bit + tail).
      -- `Fin.consEquiv` has type `Bool × (Fin n → Bool) ≃ (Fin (n+1) → Bool)`.
      have hs :
          (∑ xs : Fin (n + 1) → Bool, weight (n := n + 1) θ xs) =
            ∑ p : Bool × (Fin n → Bool), weight (n := n + 1) θ (Fin.cons p.1 p.2) := by
        -- Sum over an equivalence.
        simpa using
          (Fintype.sum_equiv (Fin.consEquiv (n := n) (α := fun _ : Fin (n + 1) => Bool))
              (fun p : Bool × (Fin n → Bool) => weight (n := n + 1) θ (Fin.cons p.1 p.2))
              (fun xs : Fin (n + 1) → Bool => weight (n := n + 1) θ xs)
              (fun _p => rfl)).symm
      -- Now split the product sum into head/tail.
      rw [hs]
      -- Turn the sum over pairs into an iterated sum.
      simp only [Fintype.sum_prod_type]
      -- Use the multiplicative factorization `weight_cons`.
      have htrue :
          (∑ xs : Fin n → Bool, weight (n := n + 1) θ (Fin.cons true xs)) =
            ENNReal.ofReal (bernoulliPMF (θ : ℝ) true) * (∑ xs : Fin n → Bool, weight (n := n) θ xs) := by
        -- Factor out the constant multiplier.
        have :
            (∑ xs : Fin n → Bool,
                ENNReal.ofReal (bernoulliPMF (θ : ℝ) true) * weight (n := n) θ xs) =
              ENNReal.ofReal (bernoulliPMF (θ : ℝ) true) * (∑ xs : Fin n → Bool, weight (n := n) θ xs) := by
          -- `∑ xs, ...` is a `Finset.univ` sum; use `Finset.mul_sum`.
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin n → Bool)))
              (f := fun xs : Fin n → Bool => weight (n := n) θ xs)
              (a := ENNReal.ofReal (bernoulliPMF (θ : ℝ) true))).symm
        simp [weight_cons, this]
      have hfalse :
          (∑ xs : Fin n → Bool, weight (n := n + 1) θ (Fin.cons false xs)) =
            ENNReal.ofReal (bernoulliPMF (θ : ℝ) false) * (∑ xs : Fin n → Bool, weight (n := n) θ xs) := by
        have :
            (∑ xs : Fin n → Bool,
                ENNReal.ofReal (bernoulliPMF (θ : ℝ) false) * weight (n := n) θ xs) =
              ENNReal.ofReal (bernoulliPMF (θ : ℝ) false) * (∑ xs : Fin n → Bool, weight (n := n) θ xs) := by
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin n → Bool)))
              (f := fun xs : Fin n → Bool => weight (n := n) θ xs)
              (a := ENNReal.ofReal (bernoulliPMF (θ : ℝ) false))).symm
        simp [weight_cons, this]
      -- Finish using the induction hypothesis and `ofReal_bernoulliPMF_add`.
      have ih : (∑ xs : Fin n → Bool, weight (n := n) θ xs) = 1 := sum_weight_eq_one n θ
      -- Combine the two branches (true/false head bit).
      calc
        (∑ b : Bool, ∑ xs : Fin n → Bool, weight (n := n + 1) θ (Fin.cons b xs))
            = (∑ xs : Fin n → Bool, weight (n := n + 1) θ (Fin.cons true xs)) +
                (∑ xs : Fin n → Bool, weight (n := n + 1) θ (Fin.cons false xs)) := by
                  -- `Bool` sum is two terms.
                  simp
        _ = (ENNReal.ofReal (bernoulliPMF (θ : ℝ) true) +
              ENNReal.ofReal (bernoulliPMF (θ : ℝ) false)) * (∑ xs : Fin n → Bool, weight (n := n) θ xs) := by
              -- Factor out the shared suffix-weight sum.
              simpa [htrue, hfalse] using
                (add_mul (ENNReal.ofReal (bernoulliPMF (θ : ℝ) true))
                    (ENNReal.ofReal (bernoulliPMF (θ : ℝ) false))
                    (∑ xs : Fin n → Bool, weight (n := n) θ xs)).symm
        _ = 1 := by
              simp [ofReal_bernoulliPMF_add (θ := θ), ih]

/-- The `PMF` on `Fin n → Bool` induced by `theta`. -/
def pmf (θ : Theta) : PMF (Fin n → Bool) :=
  PMF.ofFintype (weight (n := n) θ) (sum_weight_eq_one (n := n) θ)

@[simp] lemma pmf_apply (θ : Theta) (xs : Fin n → Bool) :
    pmf (n := n) θ xs = weight (n := n) θ xs := by
  simp [pmf]

@[simp] lemma pmf_toMeasure_apply_singleton (θ : Theta) (xs : Fin n → Bool) :
    (pmf (n := n) θ).toMeasure {xs} = weight (n := n) θ xs := by
  simp [pmf]

private lemma measurable_weight (xs : Fin n → Bool) :
    Measurable fun θ : Theta => weight (n := n) θ xs := by
  -- `bernoulliProductPMF` is a finite product of measurable functions.
  -- We use the closed form `θ^k * (1-θ)^(n-k)` for measurability.
  have hmeas : Measurable fun t : ℝ => bernoulliProductPMF t xs := by
    -- Use `bernoulliProductPMF_eq_power` and measurability of `pow` and subtraction.
    have : Measurable fun t : ℝ =>
        t ^ (countTrue xs) * (1 - t) ^ (countFalse xs) := by
      have hm1 : Measurable fun t : ℝ => t ^ (countTrue xs) := by
        simpa using (measurable_id.pow_const (countTrue xs))
      have hm2 : Measurable fun t : ℝ => (1 - t) ^ (countFalse xs) := by
        have : Measurable fun t : ℝ => 1 - t := by
          simpa [sub_eq_add_neg] using (measurable_const.sub measurable_id)
        simpa using this.pow_const (countFalse xs)
      exact hm1.mul hm2
    simpa [bernoulliProductPMF_eq_power] using this
  -- Restrict to the subtype and apply `ENNReal.measurable_ofReal`.
  simpa [weight] using (ENNReal.measurable_ofReal.comp (hmeas.comp measurable_subtype_coe))

private lemma measurable_pmf_toMeasure_apply (s : Set (Fin n → Bool)) :
    Measurable fun θ : Theta => (pmf (n := n) θ).toMeasure s := by
  classical
  -- On a fintype, `PMF.toMeasure` is computed by a finite sum.
  have hrewrite :
      (fun θ : Theta => (pmf (n := n) θ).toMeasure s) =
        fun θ : Theta => ∑ x : Fin n → Bool, (if x ∈ s then weight (n := n) θ x else 0) := by
    funext θ
    -- Rewrite `toMeasure s` as a `Fintype` sum of indicators.
    simp [PMF.toMeasure_apply_fintype, pmf_apply, weight, Set.indicator]
  -- Use measurability of finite sums.
  have hmeasTerm :
      ∀ x : Fin n → Bool, Measurable fun θ : Theta =>
        (if x ∈ s then weight (n := n) θ x else 0) := by
    intro x
    by_cases hx : x ∈ s
    · simp [hx, measurable_weight (n := n) (xs := x)]
    · simp [hx]
  -- Finish with the rewrite.
  classical
  -- Use `Finset.measurable_fun_sum` (from mathlib's measurability lemmas).
  have hsum :
      Measurable (fun θ : Theta =>
        ∑ x : Fin n → Bool, (if x ∈ s then weight (n := n) θ x else 0)) := by
    simpa using
      (Finset.measurable_fun_sum (s := (Finset.univ : Finset (Fin n → Bool)))
        (f := fun x : Fin n → Bool => fun θ : Theta => (if x ∈ s then weight (n := n) θ x else 0))
        (fun x _hx => hmeasTerm x))
  simpa [hrewrite] using hsum

/-- The Bernoulli product kernel on `Theta` at horizon `n`. -/
def kernel (n : ℕ) : ProbabilityTheory.Kernel Theta (Fin n → Bool) :=
  { toFun := fun θ => (pmf (n := n) θ).toMeasure
    measurable' := by
      -- Use the characterization of measurability of `Measure`-valued functions.
      refine MeasureTheory.Measure.measurable_of_measurable_coe _ ?_
      intro s _hs
      exact measurable_pmf_toMeasure_apply (n := n) s }

instance kernel_isMarkov (n : ℕ) : ProbabilityTheory.IsMarkovKernel (kernel (n := n)) := by
  classical
  refine ⟨fun θ => ?_⟩
  -- `PMF.toMeasure` is a probability measure.
  simpa [kernel] using (show IsProbabilityMeasure ((pmf (n := n) θ).toMeasure) from (by infer_instance))

end Kernel

/-! ## Packaging as a Kyburg parametrized distribution -/

/-- The Kyburg parametrized distribution corresponding to a Bernoulli mixture at horizon `n`. -/
def pd (M : BernoulliMixture) (n : ℕ) :
    ParametrizedDistribution Theta (Fin n → Bool) :=
  { kernel := kernel (n := n)
    kernel_isMarkov := kernel_isMarkov (n := n)
    mixingMeasure := mixingMeasureTheta M
    mixing_isProbability := inferInstance }

/-! ## Main bridge lemma -/

theorem flatten_apply_singleton (M : BernoulliMixture) (n : ℕ) (xs : Fin n → Bool) :
    (ParametrizedDistribution.flatten (pd M n)) {xs}
      = ENNReal.ofReal (M.prob xs) := by
  classical
  -- Expand `flatten` as a `lintegral` of singleton masses.
  have hmeas : MeasurableSet ({xs} : Set (Fin n → Bool)) := by simp
  have hflat :
      (ParametrizedDistribution.flatten (pd M n)) {xs} =
        ∫⁻ θ : Theta, ENNReal.ofReal (bernoulliProductPMF (θ : ℝ) xs) ∂mixingMeasureTheta M := by
    -- `flatten_apply` + the explicit kernel gives the desired integrand.
    simpa [pd, kernel, pmf_toMeasure_apply_singleton, pmf, weight] using
      (ParametrizedDistribution.flatten_apply (pd M n) {xs} hmeas)
  -- Reduce the subtype integral to a set-lintegral on `ℝ`.
  have hs : MeasurableSet (Set.Icc (0 : ℝ) 1) := measurableSet_Icc
  -- The integrand is `ENNReal.ofReal (bernoulliProductPMF θ xs)`.
  -- `lintegral_subtype_comap` converts `Θ`-integral with `comap` to a set integral.
  have hsub :
      (∫⁻ θ : Theta, ENNReal.ofReal (bernoulliProductPMF (θ : ℝ) xs) ∂mixingMeasureTheta M) =
        ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bernoulliProductPMF t xs) ∂M.mixingMeasure := by
    -- `mixingMeasureTheta` is `comap (↑)`.
    simpa [mixingMeasureTheta, hs] using
      (MeasureTheory.lintegral_subtype_comap (μ := M.mixingMeasure) (s := Set.Icc (0 : ℝ) 1) hs
        (f := fun t : ℝ => ENNReal.ofReal (bernoulliProductPMF t xs)))
  -- Convert the set-lintegral of `ENNReal.ofReal` to `ENNReal.ofReal` of the Bochner integral.
  have hcont : Continuous fun t : ℝ => bernoulliProductPMF t xs := by
    -- Use the closed form and continuity of `pow`.
    have h1 : Continuous fun t : ℝ => t ^ (countTrue xs) := by
      simpa using (continuous_pow (countTrue xs))
    have h2 : Continuous fun t : ℝ => (1 - t) ^ (countFalse xs) := by
      have : Continuous fun t : ℝ => 1 - t := by
        simpa [sub_eq_add_neg] using (continuous_const.sub continuous_id)
      simpa using (continuous_pow (countFalse xs)).comp this
    simpa [bernoulliProductPMF_eq_power] using h1.mul h2
  have hint :
      Integrable (fun t : ℝ => bernoulliProductPMF t xs)
        (M.mixingMeasure.restrict (Set.Icc (0 : ℝ) 1)) := by
    -- On a finite measure, a measurable function bounded by a constant is integrable.
    haveI : IsProbabilityMeasure M.mixingMeasure := M.isProbability
    have hs_finite : M.mixingMeasure (Set.Icc (0 : ℝ) 1) ≠ ∞ := by
      have hle : M.mixingMeasure (Set.Icc (0 : ℝ) 1) ≤ M.mixingMeasure Set.univ :=
        measure_mono (Set.subset_univ _)
      have huniv : M.mixingMeasure Set.univ = 1 := by
        simp
      -- `μ(Icc) ≤ 1 < ∞`.
      exact ne_of_lt (lt_of_le_of_lt (hle.trans_eq huniv) (by simp))
    have hmeas :
        AEStronglyMeasurable (fun t : ℝ => bernoulliProductPMF t xs) M.mixingMeasure :=
      hcont.measurable.aestronglyMeasurable
    have hbound :
        ∀ᵐ t ∂(M.mixingMeasure.restrict (Set.Icc (0 : ℝ) 1)),
          ‖bernoulliProductPMF t xs‖ ≤ (1 : ℝ) := by
      -- On `[0,1]` each factor is in `[0,1]`, so the product is in `[0,1]`.
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc ?_
      intro t ht
      have ht0 : (0 : ℝ) ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1
      have hpow1 : t ^ (countTrue xs) ≤ 1 := by
        exact pow_le_one₀ (n := countTrue xs) ht0 ht1
      have hpow2 : (1 - t) ^ (countFalse xs) ≤ 1 := by
        have hle : 1 - t ≤ 1 := by linarith
        exact pow_le_one₀ (n := countFalse xs) h1t hle
      have hnonneg1 : 0 ≤ t ^ (countTrue xs) := pow_nonneg ht0 _
      have hnonneg2 : 0 ≤ (1 - t) ^ (countFalse xs) := pow_nonneg h1t _
      have hnonneg : 0 ≤ t ^ (countTrue xs) * (1 - t) ^ (countFalse xs) :=
        mul_nonneg hnonneg1 hnonneg2
      have hle1 : t ^ (countTrue xs) * (1 - t) ^ (countFalse xs) ≤ 1 := by
        -- Multiply the `≤ 1` bounds.
        have := mul_le_mul hpow1 hpow2 hnonneg2 (by linarith)
        simpa [one_mul] using this
      have habs : ‖t ^ (countTrue xs) * (1 - t) ^ (countFalse xs)‖ ≤ (1 : ℝ) := by
        simpa [Real.norm_of_nonneg hnonneg] using hle1
      simpa [bernoulliProductPMF_eq_power] using habs
    -- Now apply the bounded-integrable lemma.
    have hIntOn :
        IntegrableOn (fun t : ℝ => bernoulliProductPMF t xs) (Set.Icc (0 : ℝ) 1) M.mixingMeasure :=
      (Measure.integrableOn_of_bounded (μ := M.mixingMeasure) (s := Set.Icc (0 : ℝ) 1)
        hs_finite hmeas (M := (1 : ℝ)) hbound)
    simpa [IntegrableOn]
  have hnonneg :
      (0 : ℝ → ℝ) ≤ᵐ[(M.mixingMeasure.restrict (Set.Icc (0 : ℝ) 1))]
        (fun t : ℝ => bernoulliProductPMF t xs) := by
    -- On `Icc 0 1`, `bernoulliProductPMF` is nonnegative.
    refine (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc ?_)
    intro t ht
    -- Use the closed form and nonnegativity of factors.
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht1
    -- Powers of nonneg are nonneg.
    have : 0 ≤ t ^ (countTrue xs) * (1 - t) ^ (countFalse xs) := by
      exact mul_nonneg (pow_nonneg ht0 _) (pow_nonneg h1t _)
    simpa [bernoulliProductPMF_eq_power] using this
  have hconv :
      ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bernoulliProductPMF t xs) ∂M.mixingMeasure =
        ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) 1, bernoulliProductPMF t xs ∂M.mixingMeasure) := by
    -- Apply `ofReal_integral_eq_lintegral_ofReal` to the restricted measure.
    -- Then rewrite the integrals-on-sets as integrals w.r.t. `restrict` (definitionally).
    have h :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := M.mixingMeasure.restrict (Set.Icc (0 : ℝ) 1))
        (f := fun t : ℝ => bernoulliProductPMF t xs) hint hnonneg)
    simpa using h.symm
  -- Put everything together.
  calc
    (ParametrizedDistribution.flatten (pd M n)) {xs}
        = ∫⁻ θ : Theta, ENNReal.ofReal (bernoulliProductPMF (θ : ℝ) xs) ∂mixingMeasureTheta M := hflat
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bernoulliProductPMF t xs) ∂M.mixingMeasure := hsub
    _ = ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) 1, bernoulliProductPMF t xs ∂M.mixingMeasure) := hconv
    _ = ENNReal.ofReal (M.prob xs) := by simp [BernoulliMixture.prob]

end DeFinettiConnection

end Mettapedia.ProbabilityTheory.HigherOrderProbability
