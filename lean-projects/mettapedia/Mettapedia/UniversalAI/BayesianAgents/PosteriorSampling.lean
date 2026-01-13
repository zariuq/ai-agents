import Mettapedia.UniversalAI.BayesianAgents.HistoryProbability
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Posterior Sampling / Thompson Sampling (History-Level)

This file defines a reusable **posterior-sampling** (a.k.a. Thompson sampling) agent for the
`BayesianAgents` API:

1. Maintain a posterior over a (countable) family of candidate environments `envs : ι → Environment`
   with prior weights `prior : ι → ℝ≥0∞`.
2. Sample a candidate environment from the posterior (equivalently: randomize over its induced
   optimal action).
3. Act optimally for the sampled environment for the remaining horizon.

We implement the agent as a stochastic policy by marginalizing the sampling:
`π_TS(a | h) = ∑ i, posterior(i | h) * 𝟙[a = optimalAction(envs i, h)]`.

This construction is intended to be shared between:
- bandit instances (finite/parametric `ι`),
- general RL environment classes (countable `ι`, e.g. reflective-oracle environments).
-/

namespace Mettapedia.UniversalAI.BayesianAgents

open scoped ENNReal NNReal

/-! ## Normalized Posterior on Histories -/

/-- Unnormalized posterior weight: `prior i * envs i (h)` (environment-only history probability). -/
noncomputable def unnormalizedPosteriorWeight {ι : Type*}
    (prior : ι → ℝ≥0∞) (envs : ι → Environment) (h : History) : ι → ℝ≥0∞ :=
  fun i => prior i * historyProbability (envs i) h

/-- The normalizing constant `Z(h) = ∑ i, prior i * envs i(h)`. -/
noncomputable def unnormalizedPosteriorTotal {ι : Type*}
    (prior : ι → ℝ≥0∞) (envs : ι → Environment) (h : History) : ℝ≥0∞ :=
  ∑' i, unnormalizedPosteriorWeight prior envs h i

theorem unnormalizedPosteriorWeight_le_prior {ι : Type*}
    (prior : ι → ℝ≥0∞) (envs : ι → Environment) (h : History) (i : ι) :
    unnormalizedPosteriorWeight prior envs h i ≤ prior i := by
  have h_prob : historyProbability (envs i) h ≤ 1 :=
    historyProbability_le_one (envs i) h
  simpa [unnormalizedPosteriorWeight, mul_one] using (mul_le_mul_left' h_prob (prior i))

theorem unnormalizedPosteriorTotal_le_priorTotal {ι : Type*}
    (prior : ι → ℝ≥0∞) (envs : ι → Environment) (h : History) :
    unnormalizedPosteriorTotal prior envs h ≤ ∑' i, prior i := by
  classical
  refine ENNReal.tsum_le_tsum ?_
  intro i
  exact unnormalizedPosteriorWeight_le_prior prior envs h i

theorem unnormalizedPosteriorTotal_le_one {ι : Type*}
    (prior : ι → ℝ≥0∞) (envs : ι → Environment) (h : History)
    (h_prior : (∑' i, prior i) ≤ 1) :
    unnormalizedPosteriorTotal prior envs h ≤ 1 := by
  exact le_trans (unnormalizedPosteriorTotal_le_priorTotal prior envs h) h_prior

theorem unnormalizedPosteriorTotal_ne_top {ι : Type*}
    (prior : ι → ℝ≥0∞) (envs : ι → Environment) (h : History)
    (h_prior : (∑' i, prior i) ≤ 1) :
    unnormalizedPosteriorTotal prior envs h ≠ ∞ := by
  have hle : unnormalizedPosteriorTotal prior envs h ≤ 1 :=
    unnormalizedPosteriorTotal_le_one prior envs h h_prior
  exact (lt_of_le_of_lt hle ENNReal.one_lt_top).ne_top

/-- A totalized posterior distribution on indices: normalize the unnormalized weights; if the
normalizer is `0`, fall back to a Dirac distribution at `default`. -/
noncomputable def posteriorWeightNormalized {ι : Type*} [Inhabited ι]
    (prior : ι → ℝ≥0∞) (envs : ι → Environment) (h : History) : ι → ℝ≥0∞ :=
by
  classical
  let w := unnormalizedPosteriorWeight prior envs h
  let Z := unnormalizedPosteriorTotal prior envs h
  exact
    if hZ : Z = 0 then
      fun i => if i = default then 1 else 0
    else
      fun i => w i / Z

theorem posteriorWeightNormalized_tsum_eq_one {ι : Type*} [Inhabited ι]
    (prior : ι → ℝ≥0∞) (envs : ι → Environment) (h : History)
    (h_prior : (∑' i, prior i) ≤ 1) :
    ∑' i, posteriorWeightNormalized prior envs h i = 1 := by
  classical
  set w : ι → ℝ≥0∞ := unnormalizedPosteriorWeight prior envs h
  set Z : ℝ≥0∞ := unnormalizedPosteriorTotal prior envs h
  by_cases hZ : Z = 0
  · -- In the degenerate case `Z = 0`, we return a Dirac distribution at `default`.
    simp [posteriorWeightNormalized, Z, hZ, tsum_ite_eq]
  · have hZ_ne0 : Z ≠ 0 := hZ
    have hZ_ne_top : Z ≠ ∞ := by
      simpa [Z] using unnormalizedPosteriorTotal_ne_top prior envs h h_prior
    calc
      (∑' i, posteriorWeightNormalized prior envs h i)
          = ∑' i, w i / Z := by
              simp [posteriorWeightNormalized, Z, w, hZ]
      _ = ∑' i, w i * Z⁻¹ := by
            simp [div_eq_mul_inv]
      _ = (∑' i, w i) * Z⁻¹ := by
            simpa using (ENNReal.tsum_mul_right (f := w) (a := Z⁻¹))
      _ = Z * Z⁻¹ := by simp [Z, w, unnormalizedPosteriorTotal]
      _ = 1 := ENNReal.mul_inv_cancel hZ_ne0 hZ_ne_top

/-! ## Thompson Sampling Agent -/

/-- Posterior-sampling / Thompson-sampling agent over an indexed family of environments.

At a history `h`, sample an index `i` from `posteriorWeightNormalized prior envs h` and take the
optimal action for environment `envs i` for the remaining horizon. -/
noncomputable def thompsonSamplingAgent {ι : Type*} [Inhabited ι]
    (prior : ι → ℝ≥0∞) (envs : ι → Environment) (h_prior : (∑' i, prior i) ≤ 1)
    (γ : DiscountFactor) (horizon : ℕ) : Agent where
  policy h a :=
    match horizon - 2 * h.cycles with
    | 0 =>
        if a = Action.stay then 1 else 0
    | k + 1 =>
        ∑' i : ι,
          posteriorWeightNormalized prior envs h i *
            (if a = optimalAction (envs i) γ h k then 1 else 0)
  policy_sum_one h _hw := by
    classical
    cases hrem : horizon - 2 * h.cycles with
    | zero =>
        -- Deterministic fallback action.
        -- `∑ a, 𝟙[a = stay] = 1`.
        simp [tsum_ite_eq]
    | succ k =>
        -- Swap sums and use that the posterior is a probability distribution.
        have hPost :
            (∑' i : ι, posteriorWeightNormalized prior envs h i) = 1 :=
          posteriorWeightNormalized_tsum_eq_one (prior := prior) (envs := envs) (h := h) h_prior
        have hGoal :
          (∑' a : Action,
                ∑' i : ι,
                  posteriorWeightNormalized prior envs h i *
                    (if a = optimalAction (envs i) γ h k then 1 else 0))
              =
            ∑' i : ι,
              ∑' a : Action,
                posteriorWeightNormalized prior envs h i *
                  (if a = optimalAction (envs i) γ h k then 1 else 0) := by
                simp [ENNReal.tsum_comm]
        have hGoal'' :
            (∑' a : Action,
                  ∑' i : ι,
                    posteriorWeightNormalized prior envs h i *
                      (if a = optimalAction (envs i) γ h k then 1 else 0)) = 1 := by
          calc
            (∑' a : Action,
                  ∑' i : ι,
                    posteriorWeightNormalized prior envs h i *
                      (if a = optimalAction (envs i) γ h k then 1 else 0))
                =
              ∑' i : ι,
                ∑' a : Action,
                  posteriorWeightNormalized prior envs h i *
                    (if a = optimalAction (envs i) γ h k then 1 else 0) := hGoal
            _ = ∑' i : ι, posteriorWeightNormalized prior envs h i := by
                -- `∀ i, Σ_a posterior(i) * 𝟙[a = argmax_i] = posterior(i)`
                refine tsum_congr ?_
                intro i
                have hAct :
                    (∑' a : Action,
                        (if a = optimalAction (envs i) γ h k then (1 : ℝ≥0∞) else 0)) = 1 := by
                  simp [tsum_ite_eq]
                calc
                  (∑' a : Action,
                        posteriorWeightNormalized prior envs h i *
                          (if a = optimalAction (envs i) γ h k then 1 else 0))
                      =
                    posteriorWeightNormalized prior envs h i *
                      ∑' a : Action,
                        (if a = optimalAction (envs i) γ h k then (1 : ℝ≥0∞) else 0) := by
                        -- pull out the constant factor
                        simp
                  _ = posteriorWeightNormalized prior envs h i := by simp [hAct]
            _ = 1 := hPost
        -- Unfold `policy` in this branch.
        simpa [hrem] using hGoal''

end Mettapedia.UniversalAI.BayesianAgents
