import Mathlib.Probability.Distributions.Beta
import Mettapedia.ProbabilityTheory.Distributions.Bernoulli
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Beta-Bernoulli Conjugate Prior

This file establishes the conjugacy relationship between the Beta distribution
(prior over Bernoulli parameter) and the Bernoulli distribution (likelihood).

## Main Definitions

* `BetaBernoulliPrior`: Beta(α,β) prior for Bernoulli parameter
* `posterior`: Bayesian posterior after observing outcome
* `mean`: Posterior mean (Thompson Sampling uses this for arm selection)

## Main Theorems

* `betaBernoulli_conjugacy`: Beta-Bernoulli conjugacy relationship
* `posterior_mean_shift`: Posterior mean shifts toward observed data

## References

- Thompson, W. R. (1933). "On the likelihood that one unknown probability
  exceeds another in view of the evidence of two samples"
- Russo & Van Roy (2014). "Learning to Optimize via Information-Directed Sampling"

-/

namespace Mettapedia.ProbabilityTheory

/-- Beta-Bernoulli prior for Bayesian inference.

    The Beta(α,β) distribution is the conjugate prior for the Bernoulli
    parameter p. After observing k successes in n trials, the posterior
    is Beta(α+k, β+n-k).
-/
structure BetaBernoulliPrior where
  α : ℝ
  β : ℝ
  α_pos : 0 < α
  β_pos : 0 < β

namespace BetaBernoulliPrior

/-- Posterior after observing a single Bernoulli outcome.

    * If outcome = true (success): α → α+1
    * If outcome = false (failure): β → β+1
-/
def posterior (prior : BetaBernoulliPrior) (outcome : Bool) : BetaBernoulliPrior :=
  if outcome then
    { α := prior.α + 1
      β := prior.β
      α_pos := by linarith [prior.α_pos]
      β_pos := prior.β_pos }
  else
    { α := prior.α
      β := prior.β + 1
      α_pos := prior.α_pos
      β_pos := by linarith [prior.β_pos] }

/-- Posterior mean (expected value of Beta distribution).

    For Beta(α,β), the mean is α/(α+β).
    This is what Thompson Sampling uses for arm selection.
-/
noncomputable def mean (prior : BetaBernoulliPrior) : ℝ :=
  prior.α / (prior.α + prior.β)

/-- Posterior mean after observing outcome. -/
noncomputable def posteriorMean (prior : BetaBernoulliPrior) (outcome : Bool) : ℝ :=
  (prior.posterior outcome).mean

/-- Prior mean is always in [0,1]. -/
theorem mean_mem_unit_interval (prior : BetaBernoulliPrior) :
    0 ≤ prior.mean ∧ prior.mean ≤ 1 := by
  unfold mean
  constructor
  · apply div_nonneg <;> linarith [prior.α_pos, prior.β_pos]
  · have h_pos : 0 < prior.α + prior.β := by linarith [prior.α_pos, prior.β_pos]
    rw [div_le_one h_pos]
    linarith [prior.β_pos]

/-- Beta-Bernoulli conjugacy theorem.

    After observing outcome, the posterior mean is:
    * If success: (α+1)/(α+β+1)
    * If failure: α/(α+β+1)
-/
theorem betaBernoulli_conjugacy (prior : BetaBernoulliPrior) (outcome : Bool) :
    prior.posteriorMean outcome =
      (prior.α + if outcome then 1 else 0) / (prior.α + prior.β + 1) := by
  unfold posteriorMean mean posterior
  split_ifs with h
  · -- outcome = true (success)
    simp
    ring_nf
  · -- outcome = false (failure)
    simp
    ring_nf

/-- Posterior mean is always in [0,1]. -/
theorem posteriorMean_mem_unit_interval (prior : BetaBernoulliPrior) (outcome : Bool) :
    0 ≤ prior.posteriorMean outcome ∧ prior.posteriorMean outcome ≤ 1 := by
  unfold posteriorMean mean posterior
  split_ifs <;> simp
  · -- success case: (α+1)/(α+1+β) ≤ 1
    constructor
    · apply div_nonneg <;> linarith [prior.α_pos, prior.β_pos]
    · have h_pos : 0 < prior.α + 1 + prior.β := by linarith [prior.α_pos, prior.β_pos]
      rw [div_le_one h_pos]
      linarith [prior.β_pos]
  · -- failure case: α/(α+β+1) ≤ 1
    constructor
    · apply div_nonneg <;> linarith [prior.α_pos, prior.β_pos]
    · have h_pos : 0 < prior.α + (prior.β + 1) := by linarith [prior.α_pos, prior.β_pos]
      rw [div_le_one h_pos]
      linarith [prior.β_pos]

/-- Posterior mean shifts toward observed data.

    * If success, posterior mean increases
    * If failure, posterior mean decreases
-/
theorem posterior_mean_shift (prior : BetaBernoulliPrior) (outcome : Bool) :
    (outcome = true → prior.posteriorMean true ≥ prior.mean) ∧
    (outcome = false → prior.posteriorMean false ≤ prior.mean) := by
  unfold posteriorMean mean posterior
  constructor
  · -- Success case: α/(α+β) ≤ (α+1)/(α+β+1)
    intro _
    simp
    have h1 : 0 < prior.α + prior.β := by linarith [prior.α_pos, prior.β_pos]
    have h2 : 0 < prior.α + 1 + prior.β := by linarith [prior.α_pos, prior.β_pos]
    suffices h : prior.α * (prior.α + 1 + prior.β) ≤ (prior.α + 1) * (prior.α + prior.β) by
      calc prior.α / (prior.α + prior.β)
        _ = prior.α * (prior.α + 1 + prior.β) / ((prior.α + prior.β) * (prior.α + 1 + prior.β)) := by
            rw [mul_div_mul_right]; linarith
        _ ≤ (prior.α + 1) * (prior.α + prior.β) / ((prior.α + prior.β) * (prior.α + 1 + prior.β)) := by
            exact div_le_div_of_nonneg_right h (by positivity)
        _ = (prior.α + 1) / (prior.α + 1 + prior.β) := by
            rw [mul_comm (prior.α + 1), mul_div_mul_left]; linarith
    nlinarith [sq_nonneg prior.α, sq_nonneg prior.β, prior.β_pos]
  · -- Failure case: α/(α+β+1) ≤ α/(α+β)
    intro _
    simp
    have h1 : 0 < prior.α + (prior.β + 1) := by linarith [prior.α_pos, prior.β_pos]
    have h2 : 0 < prior.α + prior.β := by linarith [prior.α_pos, prior.β_pos]
    suffices h : prior.α * (prior.α + prior.β) ≤ prior.α * (prior.α + (prior.β + 1)) by
      calc prior.α / (prior.α + (prior.β + 1))
        _ = prior.α * (prior.α + prior.β) / ((prior.α + (prior.β + 1)) * (prior.α + prior.β)) := by
            rw [mul_div_mul_right]; linarith
        _ ≤ prior.α * (prior.α + (prior.β + 1)) / ((prior.α + (prior.β + 1)) * (prior.α + prior.β)) := by
            exact div_le_div_of_nonneg_right h (by positivity)
        _ = prior.α * (prior.α + (prior.β + 1)) / ((prior.α + prior.β) * (prior.α + (prior.β + 1))) := by
            ring_nf
        _ = prior.α / (prior.α + prior.β) := by
            rw [mul_div_mul_right]; linarith
    nlinarith [sq_nonneg prior.α, prior.α_pos]

end BetaBernoulliPrior

end Mettapedia.ProbabilityTheory
