import Mettapedia.UniversalAI.BayesianAgents.PosteriorSampling
import Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration

/-!
# Thompson / Posterior Sampling for Grain-of-Truth (Leike, Ch. 5–7)

This file defines the Thompson-sampling / posterior-sampling policy over a countable environment
class, in the concrete `BayesianAgents` API used by the Grain-of-Truth development.

The *learning-theory* proofs (asymptotic optimality in mean, value convergence, etc.) are developed
in follow-up files; this module provides the shared definition that both the bandit and RL
instantiations can reuse.

References:
- Leike et al. (2016) “Thompson Sampling is Asymptotically Optimal in General Environments”.
- Leike (2016) PhD thesis, Chapter 5 (optimality) and Chapter 7 (multi-agent / grain of truth).
-/

namespace Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.ThompsonSampling

open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.GrainOfTruth
open Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.HistoryFiltration
open Mettapedia.UniversalAI.ReflectiveOracles
open scoped ENNReal NNReal MeasureTheory

/-! ## Thompson Sampling Agent (Countable Environment Class) -/

/-- Thompson / posterior-sampling agent over a countable family `envs : ℕ → Environment`.

This is the “sample an environment from the posterior, then act optimally for it” construction,
implemented as a stochastic policy by marginalizing the sampling. -/
noncomputable def thompsonSamplingAgent (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (envs : ℕ → Environment)
    (γ : DiscountFactor) (horizon : ℕ) : Agent :=
  Mettapedia.UniversalAI.BayesianAgents.thompsonSamplingAgent
    (prior := prior.weight) (envs := envs) (h_prior := prior.tsum_le_one) γ horizon

end Mettapedia.UniversalAI.GrainOfTruth.MeasureTheory.ThompsonSampling

