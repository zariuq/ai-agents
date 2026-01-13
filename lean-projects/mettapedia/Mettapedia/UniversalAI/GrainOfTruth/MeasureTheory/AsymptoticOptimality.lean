import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.RegretConvergence

/-!
# Measure-Theoretic Asymptotic Optimality (Leike-style)

The current `FixedPoint.IsAsymptoticallyOptimal` is stated in a very strong
“for all histories” ε-δ form. For the Leike/Hutter development we want the
standard *almost sure* (or in-mean) convergence statements under the true
trajectory measure.

This file introduces a measure-theoretic notion of asymptotic optimality that
matches the outputs of the Phase 1–4 measure theory pipeline.
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.AsymptoticOptimality

open MeasureTheory ProbabilityTheory Filter
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth
open Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
open Mettapedia.UniversalAI.ReflectiveOracles
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.RegretConvergence
open scoped ENNReal NNReal MeasureTheory

/-! ## Definitions -/

/-- *Almost sure* asymptotic optimality in mean: along almost every true trajectory,
the posterior-expected regret tends to `0`. -/
def IsAsymptoticallyOptimalAe (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex) (h_stoch : isStochastic (envs ν_star_idx)) : Prop :=
  ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
    Filter.Tendsto (fun t => expectedRegretOnTrajectory O M prior envs agent γ t horizon traj)
      Filter.atTop (nhds 0)

/-! ## Wrappers -/

theorem isAsymptoticallyOptimalAe_of_consistency (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (agent : Agent) (γ : DiscountFactor) (horizon : ℕ)
    (ν_star_idx : EnvironmentIndex)
    (h_grain : 0 < prior.weight ν_star_idx)
    (h_stoch : isStochastic (envs ν_star_idx))
    (h_π_optimal : ∀ h : History, h.wellFormed = true →
      regret (envs ν_star_idx) agent γ h horizon = 0)
    (h_consistency : ∀ᵐ traj ∂(environmentMeasureWithPolicy (envs ν_star_idx) agent h_stoch),
      Filter.Tendsto
        (fun t => (PosteriorConcentration.posteriorWeight O M prior envs ν_star_idx t traj).toReal)
        Filter.atTop (nhds 1)) :
    IsAsymptoticallyOptimalAe O M prior envs agent γ horizon ν_star_idx h_stoch := by
  -- This is exactly Phase 4.
  simpa [IsAsymptoticallyOptimalAe] using
    (consistency_implies_expected_regret_convergence O M prior envs agent γ horizon
      ν_star_idx h_grain h_stoch h_π_optimal h_consistency)

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.AsymptoticOptimality
