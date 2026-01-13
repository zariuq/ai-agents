import Mettapedia.UniversalAI.TimeBoundedAIXI.Core

/-!
# Chapter 7 (core-generic): Provability / enumerability scaffolding

Chapter 7’s convergence story informally combines two ingredients:

1. A proof system that can certify `VA`/`ValidValueLowerBound` claims (modeled by `CompleteProofChecker`).
2. An “enumerability from below / realizability” assumption ensuring that for any history `h` and accuracy `ε`,
   there exists some *certifiable* program whose claimed value is within `ε` of optimal at `h`.

This file packages a minimal version of (2) that is strong enough to *derive*
`HasNearOptimalVerifiedProgramsForAllHistories`, and therefore supply the `nearOptimal` field of
`AIXItlConvergenceAssumptions`.
-/

namespace Mettapedia.UniversalAI.TimeBoundedAIXI.Core

open scoped Classical

/-! ## Enumerability / realizability interface -/

/-- A standard “enumerable from below” style interface for the optimal Q-value at horizon `n`. -/
structure OptimalQValueLowerApprox {Action : Type uA} {Percept : Type uP}
    [Inhabited Action] [Fintype Action] [Fintype Percept] [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor) (n : ℕ) where
  approx : ℕ → BayesianAgents.Core.History Action Percept → ℚ
  /-- Each approximation is a lower bound on the optimal Q-value. -/
  approx_le_optimal :
    ∀ k h,
      BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h →
        (approx k h : ℝ) ≤ BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n
  /-- For any `ε>0`, some approximation is within `ε` of optimal. -/
  approx_close :
    ∀ h,
      BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h →
        ∀ ε : ℝ, 0 < ε →
          ∃ k, BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤ (approx k h : ℝ)

/-- Realize approximation indices as actually verifiable programs. -/
structure VerifiedProgramRealizer {Action : Type uA} {Percept : Type uP}
    [Inhabited Action] [Fintype Action] [Fintype Percept] [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor) (n : ℕ)
    (approx : ℕ → BayesianAgents.Core.History Action Percept → ℚ) where
  realize :
    ∀ h,
      BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h →
        ∀ k, ∃ p : ExtendedChronologicalProgram Action Percept,
          ValidValueLowerBound μ γ (n + 1) p ∧ (approx k h : ℝ) ≤ (p.compute h).1

/-- An abstract source of increasingly good *certifiable* value lower bounds for the optimal value.

This is intentionally stronger than the bare “enumerable from below” definition: it includes a
bridge that turns the approximation index into an actual *program* that satisfies `ValidValueLowerBound`.

It is designed to be instantiated later by a concrete provability model (proof enumeration + VA
predicate completeness). -/
structure NearOptimalVerifiedProgramSource {Action : Type uA} {Percept : Type uP}
    [Inhabited Action] [Fintype Action] [Fintype Percept] [BayesianAgents.Core.PerceptReward Percept]
    (μ : BayesianAgents.Core.Environment Action Percept) (γ : BayesianAgents.Core.DiscountFactor) (n : ℕ) where
  /-- A (rational) under-approximation index. -/
  approx : ℕ → BayesianAgents.Core.History Action Percept → ℚ
  /-- Convergence-from-below at the target history: for any `ε>0`, some index is within `ε` of optimal. -/
  approx_close :
    ∀ h,
      BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h →
        ∀ ε : ℝ, 0 < ε →
          ∃ k, BayesianAgents.Core.optimalQValue μ γ h (BayesianAgents.Core.optimalAction μ γ h n) n - ε ≤ (approx k h : ℝ)
  /-- Realize an approximation index as an actually verified program whose claim meets the approximation. -/
  realize :
    ∀ h,
      BayesianAgents.Core.History.wellFormed (Action := Action) (Percept := Percept) h →
        ∀ k, ∃ p : ExtendedChronologicalProgram Action Percept,
          ValidValueLowerBound μ γ (n + 1) p ∧ (approx k h : ℝ) ≤ (p.compute h).1

namespace NearOptimalVerifiedProgramSource

variable {Action : Type uA} {Percept : Type uP} [Inhabited Action] [Fintype Action] [Fintype Percept]
    [BayesianAgents.Core.PerceptReward Percept]
    {μ : BayesianAgents.Core.Environment Action Percept} {γ : BayesianAgents.Core.DiscountFactor} {n : ℕ}

/-- Build a `NearOptimalVerifiedProgramSource` from a lower approximation process and a realizer. -/
def ofLowerApproxAndRealizer
    (approx : OptimalQValueLowerApprox (μ := μ) (γ := γ) (Action := Action) (Percept := Percept) n)
    (realizer :
      VerifiedProgramRealizer (μ := μ) (γ := γ) (Action := Action) (Percept := Percept) n approx.approx) :
    NearOptimalVerifiedProgramSource (μ := μ) (γ := γ) (Action := Action) (Percept := Percept) n :=
  { approx := approx.approx
    approx_close := approx.approx_close
    realize := realizer.realize }

/-- A `NearOptimalVerifiedProgramSource` yields the Chapter 7 hypothesis “near-optimal verified programs exist
for every well-formed history.” -/
theorem hasNearOptimalVerifiedProgramsForAllHistories
    (src : NearOptimalVerifiedProgramSource (μ := μ) (γ := γ) n) :
    HasNearOptimalVerifiedProgramsForAllHistories (μ := μ) (γ := γ) n := by
  intro h hwf ε hε
  rcases src.approx_close h hwf ε hε with ⟨k, hk⟩
  rcases src.realize h hwf k with ⟨p, hpValid, hpApprox⟩
  refine ⟨p, hpValid, ?_⟩
  exact le_trans hk hpApprox

end NearOptimalVerifiedProgramSource

/-! ## Convenience: build convergence assumptions from a checker + source -/

namespace AIXItlConvergenceAssumptions

variable {Action : Type uA} {Percept : Type uP} [Inhabited Action] [Fintype Action] [Fintype Percept]
    [BayesianAgents.Core.PerceptReward Percept]
    {μ : BayesianAgents.Core.Environment Action Percept} {γ : BayesianAgents.Core.DiscountFactor} {n : ℕ}

/-- Combine a complete proof checker with a `NearOptimalVerifiedProgramSource` into packaged convergence assumptions. -/
def ofCheckerAndSource
    (checker :
      CompleteProofChecker (α := ExtendedChronologicalProgram Action Percept) (ValidValueLowerBound μ γ (n + 1)))
    (src : NearOptimalVerifiedProgramSource (μ := μ) (γ := γ) n) :
    AIXItlConvergenceAssumptions (μ := μ) (γ := γ) n :=
  { checker := checker
    nearOptimal := src.hasNearOptimalVerifiedProgramsForAllHistories }

end AIXItlConvergenceAssumptions

end Mettapedia.UniversalAI.TimeBoundedAIXI.Core
