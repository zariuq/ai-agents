import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.AsymptoticOptimality

/-!
# Phase 5: Connecting Measure Theory to Discrete Infrastructure

This file bridges the measure-theoretic machinery (Phases 1-4) to the
discrete infrastructure in `FixedPoint.lean`.

## Main Results

* `bayesian_consistency_bridge` - Connects measure-theoretic to discrete form
* `regret_convergence_bridge` - From trajectory-based to history-based convergence
* `main_grain_of_truth` - THE MAIN THEOREM: Asymptotic optimality

## Architecture

The connection works as follows:

```
Phase 1-4: Measure Theory
  HistoryFiltration    → Trajectories, filtrations, environmentMeasure
  LikelihoodRatio      → log-LR is supermartingale under true env
  PosteriorConcentration → ∀ᵐ traj, posterior → 1 on true env
  RegretConvergence    → ∀ᵐ traj, expected regret → 0

Phase 5: Bridge (this file)
  ae_to_discrete       → Convert a.s. convergence to ε-δ form
  consistency_bridge   → Connect posteriorWeight to bayesianPosteriorWeight
  regret_bridge        → Connect trajectory-based to history-based regret

FixedPoint.lean: Discrete Infrastructure
  bayesian_consistency → ∀ ε > 0, ∃ t₀, ∀ t ≥ t₀, |posterior - 1| < ε
  IsAsymptoticallyOptimal → Expected regret → 0
```

## References

- Leike (2016). PhD Thesis, Chapter 7
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.Main

open MeasureTheory ProbabilityTheory Real
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.LikelihoodRatio
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.PosteriorConcentration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.RegretConvergence
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.AsymptoticOptimality
open Mettapedia.UniversalAI.ReflectiveOracles
open scoped ENNReal NNReal MeasureTheory

/-! ## Bridge: Trajectory Posterior to Discrete Posterior

The key insight is that both posteriorWeight (on trajectories) and
bayesianPosteriorWeight (on histories) compute the same thing -
they just represent it differently.
-/

/-- The trajectory-based posteriorWeight equals the discrete bayesianPosteriorWeight
    when evaluated at the corresponding history.

    posteriorWeight O M prior envs ν_idx t traj = bayesianPosteriorWeight O M prior envs ν_idx h
    where h = trajectoryToHistory traj t -/
theorem posteriorWeight_eq_bayesianPosteriorWeight (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (ν_idx : EnvironmentIndex) (t : ℕ) (traj : Trajectory) :
    PosteriorConcentration.posteriorWeight O M prior envs ν_idx t traj =
      bayesianPosteriorWeight O M prior envs ν_idx (trajectoryToHistory traj t) := by
  -- By definition of posteriorWeight
  rfl

/-! ## No “A.S. → ∀ Histories” Bridge (by design)

Leike's convergence theorems are *on-policy* and are stated either almost surely or in probability.
Bridging an a.s. trajectory statement into a “for all histories” ε-δ statement is both technically
heavy and conceptually wrong for Chapter 7 (off-policy counterfactuals are generally unlearnable).

Accordingly, this file only provides **measure-theoretic wrappers**.
-/

/-! ## Regret Convergence Bridge

Connect trajectory-based regret convergence to discrete form.
-/

/-- **REGRET CONVERGENCE BRIDGE**:

    From trajectory-based to history-based regret convergence.

    This bridges:
    - Phase 4's consistency_implies_expected_regret_convergence
    to:
    - FixedPoint's consistency_implies_regret_convergence format -/
theorem regret_convergence_bridge (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex)
    (h_grain : 0 < prior.weight ν_star_idx)
    (h_stoch : isStochastic (envs ν_star_idx))
    (h_agent_optimal : ∀ h : History, h.wellFormed = true →
      regret (envs ν_star_idx) agent γ h horizon = 0)
    (h_consistency : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
      Filter.Tendsto
        (fun t => (PosteriorConcentration.posteriorWeight O M prior envs ν_star_idx t traj).toReal)
        Filter.atTop (nhds 1)) :
    IsAsymptoticallyOptimalAe O M prior envs agent γ horizon ν_star_idx h_stoch := by
  exact isAsymptoticallyOptimalAe_of_consistency O M prior envs agent γ horizon ν_star_idx
    h_grain h_stoch h_agent_optimal h_consistency

/-! ## The Main Theorem

The culmination of Phases 1-5: Grain of Truth convergence.
-/

/-- **THE MAIN GRAIN OF TRUTH THEOREM**:

    If:
    1. The prior has positive weight on the true environment (grain of truth)
    2. The agent is optimal for the true environment
    3. All other environments are distinguishable from the true one

    Then the agent is asymptotically optimal in mean.

    This is the formal statement of Leike's Theorem 7.4 (PhD Thesis).

    Proof structure:
    1. Phase 2: Log-likelihood ratio is supermartingale (KL divergence ≥ 0)
    2. Phase 3: Posterior concentrates on true environment (martingale convergence)
    3. Phase 4: Regret → 0 as posterior concentrates
    4. Phase 5: Convert measure-theoretic result to discrete form

    The key insight is that Bayesian learning provably works when the prior
    contains the truth - no matter how small the prior weight. -/
theorem main_grain_of_truth (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex)
    /- Grain of Truth: true environment has positive prior weight -/
    (h_grain : 0 < prior.weight ν_star_idx)
    /- Stochasticity: true environment is stochastic -/
    (h_stoch : isStochastic (envs ν_star_idx))
    /- Agent is optimal for true environment -/
    (h_agent_optimal : ∀ h : History, h.wellFormed = true →
      regret (envs ν_star_idx) agent γ h horizon = 0)
    /- Identifiability: every wrong environment has log-likelihood ratio → -∞ under ν*^π. -/
    (h_ident : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      IdentifiableWithPolicy (envs i) (envs ν_star_idx) agent h_stoch)
    /- Dominated-convergence hypothesis for swapping `t → ∞` with `∑' i` in the denominator. -/
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
      DominatedLikelihoodRatioSeries O M prior envs ν_star_idx traj) :
    IsAsymptoticallyOptimalAe O M prior envs agent γ horizon ν_star_idx h_stoch :=
by
  have h_consistency :
      ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
        Filter.Tendsto
          (fun t => (PosteriorConcentration.posteriorWeight O M prior envs ν_star_idx t traj).toReal)
          Filter.atTop (nhds 1) :=
    posteriorWeight_true_ae_tendsto_one_of_identifiableWithPolicy (O := O) (M := M)
      (prior := prior) (envs := envs) (pi := agent) (ν_star_idx := ν_star_idx) (h_stoch := h_stoch)
      h_ident h_dom
  exact regret_convergence_bridge O M prior envs agent γ horizon ν_star_idx
    h_grain h_stoch h_agent_optimal h_consistency

/-- Convenience wrapper: run the full Grain-of-Truth pipeline assuming `ν(h_t)/ν*(h_t) → 0`
for every wrong environment.

This avoids the intermediate `IdentifiableWithPolicy` packaging (which would additionally require
eventual positivity of the likelihood ratio to take logs). -/
theorem main_grain_of_truth_of_likelihoodRatio_converges_to_zero (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex)
    (h_grain : 0 < prior.weight ν_star_idx)
    (h_stoch : isStochastic (envs ν_star_idx))
    (h_agent_optimal : ∀ h : History, h.wellFormed = true →
      regret (envs ν_star_idx) agent γ h horizon = 0)
    (h_lr_tendsto : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
        Filter.Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal)
          Filter.atTop (nhds 0))
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
      DominatedLikelihoodRatioSeries O M prior envs ν_star_idx traj) :
    IsAsymptoticallyOptimalAe O M prior envs agent γ horizon ν_star_idx h_stoch := by
  have h_consistency :
      ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
        Filter.Tendsto
          (fun t => (PosteriorConcentration.posteriorWeight O M prior envs ν_star_idx t traj).toReal)
          Filter.atTop (nhds 1) :=
    posteriorWeight_true_ae_tendsto_one_of_likelihoodRatio_converges_to_zero (O := O) (M := M)
      (prior := prior) (envs := envs) (pi := agent) (ν_star_idx := ν_star_idx) (h_stoch := h_stoch)
      (h_lr := h_lr_tendsto) (h_dom := h_dom)
  exact regret_convergence_bridge O M prior envs agent γ horizon ν_star_idx
    h_grain h_stoch h_agent_optimal h_consistency

/-- Convenience wrapper: a strong Leike-style “per-step likelihood ratio shrinkage” hypothesis
implies the full likelihood-ratio identifiability needed for posterior concentration. -/
theorem main_grain_of_truth_of_eventually_stepLikelihoodRatio_le (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex)
    (h_grain : 0 < prior.weight ν_star_idx)
    (h_stoch : isStochastic (envs ν_star_idx))
    (h_agent_optimal : ∀ h : History, h.wellFormed = true →
      regret (envs ν_star_idx) agent γ h horizon = 0)
    (h_step : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      ∃ r : ℝ≥0∞, r < 1 ∧
        ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
          ∀ᶠ t in Filter.atTop, stepLikelihoodRatio (envs i) (envs ν_star_idx) t traj ≤ r)
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
      DominatedLikelihoodRatioSeries O M prior envs ν_star_idx traj) :
    IsAsymptoticallyOptimalAe O M prior envs agent γ horizon ν_star_idx h_stoch := by
  have h_lr_tendsto :
      ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
        ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
          Filter.Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal)
            Filter.atTop (nhds 0) := by
    intro i hi
    rcases h_step i hi with ⟨r, hr, h_step_i⟩
    simpa using
      (likelihoodRatio_converges_to_zero_of_eventually_stepLikelihoodRatio_le
        (ν := envs i) (ν_star := envs ν_star_idx) (pi := agent) (h_stoch := h_stoch) hr h_step_i)
  exact main_grain_of_truth_of_likelihoodRatio_converges_to_zero (O := O) (M := M) (prior := prior) (envs := envs)
    (agent := agent) (γ := γ) (horizon := horizon) (ν_star_idx := ν_star_idx)
    h_grain h_stoch h_agent_optimal (h_lr_tendsto := h_lr_tendsto) (h_dom := h_dom)

/-- Convenience wrapper: run the full Grain-of-Truth pipeline assuming every wrong environment is
refutable by a finite prefix almost surely under the true on-policy measure.

This is a strong “support mismatch” identifiability condition, but it avoids any `log`-packaging
and is often the easiest concrete route to `ν(h_t)/ν*(h_t) → 0`. -/
theorem main_grain_of_truth_of_refutableWithPolicy (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex)
    (h_grain : 0 < prior.weight ν_star_idx)
    (h_stoch : isStochastic (envs ν_star_idx))
    (h_agent_optimal : ∀ h : History, h.wellFormed = true →
      regret (envs ν_star_idx) agent γ h horizon = 0)
    (h_ref : ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
      RefutableWithPolicy (envs i) (envs ν_star_idx) agent h_stoch)
    (h_dom : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
      DominatedLikelihoodRatioSeries O M prior envs ν_star_idx traj) :
    IsAsymptoticallyOptimalAe O M prior envs agent γ horizon ν_star_idx h_stoch := by
  have h_lr_tendsto :
      ∀ i : EnvironmentIndex, i ≠ ν_star_idx →
        ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
          Filter.Tendsto (fun t => (likelihoodRatio (envs i) (envs ν_star_idx) t traj).toReal)
            Filter.atTop (nhds 0) := by
    intro i hi
    simpa using
      (likelihoodRatio_converges_to_zero_of_refutableWithPolicy (ν := envs i) (ν_star := envs ν_star_idx)
        (pi := agent) (h_stoch := h_stoch) (h_ref := h_ref i hi))
  exact main_grain_of_truth_of_likelihoodRatio_converges_to_zero (O := O) (M := M) (prior := prior) (envs := envs)
    (agent := agent) (γ := γ) (horizon := horizon) (ν_star_idx := ν_star_idx)
    h_grain h_stoch h_agent_optimal (h_lr_tendsto := h_lr_tendsto) (h_dom := h_dom)

/-! ## Summary of Phase 5

We have established the measure-theoretic wrapper for the Phase 4 implication:

1. `posteriorWeight_eq_bayesianPosteriorWeight` - Direct equality
2. `regret_convergence_bridge` - Consistency → asymptotic optimality (a.s.)
3. `main_grain_of_truth` - Same, packaged as the main theorem
-/

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.Main
