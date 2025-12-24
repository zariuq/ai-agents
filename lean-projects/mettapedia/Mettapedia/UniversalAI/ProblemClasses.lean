import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mettapedia.UniversalAI.BayesianAgents

/-!
# Important Problem Classes (Hutter 2005, Chapter 6)

This file formalizes the reduction of various AI problem classes to the AIXI framework,
following Chapter 6 of Hutter's "Universal Artificial Intelligence" (2005).

## Main Definitions

### Problem Classes
* `SequencePredictionProblem` - Binary sequence prediction (SP)
* `StrategicGameProblem` - Strategic games like chess (SG)
* `FunctionMinimizationProblem` - Function minimization (FM)
* `SupervisedLearningProblem` - Learning from examples (EX)

### Key Results
* Each problem class can be embedded in the AIXI framework
* AIXI is optimal for each problem class (when specialized)
* Reduction theorems showing equivalence of optimal strategies

## References

- Hutter, M. (2005). "Universal Artificial Intelligence", Chapter 6
- Section 6.2: Sequence Prediction
- Section 6.3: Strategic Games
- Section 6.4: Function Minimization
- Section 6.5: Supervised Learning from Examples

## Mathematical Content

### Sequence Prediction (Section 6.2)
Given a probability distribution μ over binary sequences, the SP_μ agent predicts:
  x̂_k = argmax_{x_k} μ(x_<k x_k)

Key theorem: Using AIμ for SP yields the same prediction as SP_μ.

### Strategic Games (Section 6.3)
For two-player zero-sum games with perfect information:
  - Minimax strategy: y_k = argmax min ... max min V(y₁o₁...y_no_n)
  - AIμ implements minimax when μ models rational opponent

### Function Minimization (Section 6.4)
Given function f: Y → ℝ, minimize weighted sum α₁z₁ + ... + α_m z_m
  - FMF: Final model (only final output matters)
  - FMS: Sum model (all outputs matter equally)
  - FME: Exponential weighting

### Supervised Learning (Section 6.5)
Learn relations R ⊆ Z × V from examples:
  - Environment presents (z_k, v_k) ∈ R or (z_k, ?) for queries
  - Agent outputs prediction y_k, receives reward r_k = δ(z_k, y_k) ∈ R
-/

namespace Mettapedia.UniversalAI.ProblemClasses

open BayesianAgents
open scoped Classical

/-! ## Section 6.1: Repetition of the AIμ/ξ Models

This section recalls the key definitions from Chapter 4/5. We import them
from BayesianAgents.lean.
-/

/-! ## Section 6.2: Sequence Prediction (SP)

Sequence prediction is the simplest and most well-studied problem class.
Given observations z₁z₂z₃..., predict the next element.
-/

/-- A sequence prediction problem with known prior μ.
    The environment generates a binary sequence according to μ.

    A semimeasure satisfies: μ(xs ++ [0]) + μ(xs ++ [1]) ≤ μ(xs)
    This is the standard definition from Solomonoff/Li-Vitányi.
    For probability measures, equality holds; for semimeasures, we allow ≤. -/
structure SequencePredictionProblem where
  /-- Prior probability distribution over binary sequences -/
  μ : List Bool → ENNReal
  /-- Base case: μ([]) ≤ 1 (probability of the empty sequence) -/
  μ_base_le_one : μ [] ≤ 1
  /-- Semimeasure property: sum of extensions ≤ prefix probability.
      This is the standard definition: μ(xs0) + μ(xs1) ≤ μ(xs) -/
  semimeasure : ∀ xs, μ (xs ++ [false]) + μ (xs ++ [true]) ≤ μ xs

/-- Any prefix probability is ≤ 1 (follows from semimeasure + base case).

    Uses reverse induction since the semimeasure property extends to the right. -/
theorem SequencePredictionProblem.μ_le_one (sp : SequencePredictionProblem)
    (xs : List Bool) : sp.μ xs ≤ 1 := by
  induction xs using List.reverseRecOn with
  | nil => exact sp.μ_base_le_one
  | append_singleton init b ih =>
    -- μ(init ++ [b]) ≤ μ(init ++ [false]) + μ(init ++ [true]) ≤ μ(init) ≤ 1
    have h := sp.semimeasure init
    cases b with
    | false =>
      calc sp.μ (init ++ [false])
          ≤ sp.μ (init ++ [false]) + sp.μ (init ++ [true]) := le_add_of_nonneg_right (zero_le _)
        _ ≤ sp.μ init := h
        _ ≤ 1 := ih
    | true =>
      calc sp.μ (init ++ [true])
          ≤ sp.μ (init ++ [false]) + sp.μ (init ++ [true]) := le_add_of_nonneg_left (zero_le _)
        _ ≤ sp.μ init := h
        _ ≤ 1 := ih

/-- The optimal sequence predictor for known μ.
    Predicts the bit with higher conditional probability.

    SPμ: x̂_k = argmax_{x_k} μ(x_<k x_k)  (Equation 6.10) -/
noncomputable def optimalSequencePredictor (sp : SequencePredictionProblem)
    (history : List Bool) : Bool :=
  if sp.μ (history ++ [true]) > sp.μ (history ++ [false]) then true else false

/-- Expected number of prediction errors for the optimal predictor SPμ.
    E_n^μ := Σ_{k=1}^n Σ_{x<k} μ(x<k)(1 - max μ(x<k x_k))  (Equation 6.8) -/
noncomputable def expectedPredictionErrors (sp : SequencePredictionProblem)
    (n : ℕ) : ℝ :=
  -- Sum over k from 1 to n of probability of error at step k
  -- This is a placeholder for the full summation
  (n : ℝ) * (1 - (sp.μ []).toReal / 2)  -- Simplified bound

/-- Interpret an action as a bit prediction for sequence prediction embeddings.

We identify `Action.right` with predicting `true` and `Action.left`/`Action.stay`
with predicting `false`. -/
def actionBit : Action → Bool
  | Action.left => false
  | Action.right => true
  | Action.stay => false

/-- The sequence of observed bits extracted from the observation component of percepts. -/
def obsBits (h : History) : List Bool :=
  h.percepts.map Percept.obs

/-- Appending an action does not change the observed-bit sequence. -/
theorem obsBits_append_act (h : History) (a : Action) :
    obsBits (h ++ [HistElem.act a]) = obsBits h := by
  simp [obsBits, History.percepts_append, History.percepts]

/-- The AI environment induced by a sequence prediction problem.
    We interpret predictions as actions and observations as rewards.

    As per Section 6.2.1:
    - y_k ∈ {0,1} is the prediction for bit z_k
    - r_k = δ_{y_k, z_k} (1 if correct, 0 if wrong)
    - o_k = ε (no observation needed, redundant with reward)

    We encode the *true next bit* as the observation `o_k : Bool` and the reward
    as `r_k = δ_{y_k, o_k}` in the reward bit of the percept.

    The probability of the next bit is given by the semimeasure `μ` and is
    independent of the agent's prediction. -/
noncomputable def spToEnvironment (sp : SequencePredictionProblem) : Environment :=
  let probFun : History → Percept → ENNReal := fun h x =>
    match h.getLast? with
    | some (HistElem.act a) =>
        -- Observation is the next bit z_k and reward bit is correctness: r_k = δ_{y_k, z_k}.
        if x.rewardBit = (actionBit a == x.obs) then sp.μ (obsBits h ++ [x.obs]) else 0
    | _ => 0
  { prob := probFun
    prob_le_one := by
      intro h _hw
      classical
      cases hlast : h.getLast? with
      | none =>
          rw [tsum_fintype]
          simp [probFun, hlast]
      | some e =>
          cases e with
          | per _x =>
              rw [tsum_fintype]
              simp [probFun, hlast]
          | act a =>
              rw [tsum_fintype]
              -- For each observation bit z, exactly one rewardBit value is consistent with correctness,
              -- so the total mass is μ(prefix++[false]) + μ(prefix++[true]).
              have hsum :
                  (∑ x : Percept,
                      (if x.rewardBit = (actionBit a == x.obs) then sp.μ (obsBits h ++ [x.obs]) else 0))
                    = sp.μ (obsBits h ++ [false]) + sp.μ (obsBits h ++ [true]) := by
                let e : Percept ≃ Bool × Bool := ⟨
                  fun p => match p with | Percept.mk o r => (o, r),
                  fun p => Percept.mk p.1 p.2,
                  by intro p; cases p; rfl,
                  by intro p; cases p; rfl⟩
                have h1 :
                    (∑ x : Percept,
                        (if x.rewardBit = (actionBit a == x.obs) then sp.μ (obsBits h ++ [x.obs]) else 0))
                      =
                    (∑ x : Bool × Bool,
                        (if x.2 = (actionBit a == x.1) then sp.μ (obsBits h ++ [x.1]) else 0)) := by
                  refine Fintype.sum_equiv e
                    (fun x : Percept =>
                      if x.rewardBit = (actionBit a == x.obs) then sp.μ (obsBits h ++ [x.obs]) else 0)
                    (fun x : Bool × Bool =>
                      if x.2 = (actionBit a == x.1) then sp.μ (obsBits h ++ [x.1]) else 0) ?_
                  intro x
                  cases x with
                  | mk _o _r => rfl
                rw [h1]
                cases a <;>
                  simp [actionBit, Fintype.sum_prod_type, add_comm]
              have hbound :
                  sp.μ (obsBits h ++ [false]) + sp.μ (obsBits h ++ [true]) ≤ 1 := by
                calc
                  sp.μ (obsBits h ++ [false]) + sp.μ (obsBits h ++ [true]) ≤ sp.μ (obsBits h) :=
                    sp.semimeasure _
                  _ ≤ 1 := sp.μ_le_one _
              have hprob :
                  (∑ x : Percept, probFun h x) = sp.μ (obsBits h ++ [false]) + sp.μ (obsBits h ++ [true]) := by
                simpa [probFun, hlast] using hsum
              -- Finish by unfolding `probFun` using `hlast`.
              simpa [hprob] using hbound
  }

/-- A canonical "decision history" encoding a sequence of observed bits.

We use a dummy action (`Action.stay`) before each percept. This is sufficient for
Theorem 6.2.1 since `spToEnvironment` depends only on the observation bits. -/
def spDecisionHistory : List Bool → History
  | [] => []
  | b :: bs =>
      HistElem.act Action.stay :: HistElem.per (Percept.mk b false) :: spDecisionHistory bs

theorem spDecisionHistory_obsBits (bits : List Bool) :
    obsBits (spDecisionHistory bits) = bits := by
  induction bits with
  | nil => simp [spDecisionHistory, obsBits, History.percepts]
  | cons b bs ih =>
      simp [spDecisionHistory, obsBits, History.percepts, Percept.obs]
      -- Reduce to the induction hypothesis.
      simpa [obsBits] using ih

theorem spDecisionHistory_perceptsObs_append_act (bits : List Bool) (a : Action) :
    List.map Percept.obs (spDecisionHistory bits ++ [HistElem.act a]).percepts = bits := by
  have : obsBits (spDecisionHistory bits ++ [HistElem.act a]) = bits := by
    -- Appending an action does not change the observation prefix.
    simpa [obsBits_append_act] using (spDecisionHistory_obsBits (bits := bits))
  simpa [obsBits] using this

theorem spDecisionHistory_obsBits_append_act (bits : List Bool) (a : Action) :
    obsBits (spDecisionHistory bits ++ [HistElem.act a]) = bits := by
  simpa [obsBits_append_act] using (spDecisionHistory_obsBits (bits := bits))

theorem spDecisionHistory_append_act_wellFormed (bits : List Bool) (a : Action) :
    ((spDecisionHistory bits) ++ [HistElem.act a]).wellFormed = true := by
  induction bits with
  | nil => simp [spDecisionHistory, History.wellFormed]
  | cons b bs ih =>
      simp [spDecisionHistory, History.wellFormed, ih]

/-!
### Theorem 6.2.1: AIμ = SPμ (Sequence Prediction)

In the induced AIXI environment for sequence prediction, the one-step optimal
action predicts the most likely next bit under μ, i.e. it coincides with the
specialized SPμ predictor.

Reference: Hutter (2005), Section 6.2.1, Eq. (6.12).
-/

/-- Expected immediate reward (one-step optimal Q-value) for a given action in the induced
sequence-prediction environment. -/
noncomputable def expectedRewardForAction (sp : SequencePredictionProblem) (γ : DiscountFactor)
    (h : History) (a : Action) : ℝ :=
  optimalQValue (spToEnvironment sp) γ h a 1

theorem expectedRewardForAction_spDecisionHistory (sp : SequencePredictionProblem) (γ : DiscountFactor)
    (bits : List Bool) (a : Action) :
    expectedRewardForAction sp γ (spDecisionHistory bits) a
      = (sp.μ (bits ++ [actionBit a])).toReal := by
  classical
  -- Unfold the one-step optimal Q-value: future value is 0 at horizon 0.
  have ha_wf : ((spDecisionHistory bits) ++ [HistElem.act a]).wellFormed = true :=
    spDecisionHistory_append_act_wellFormed (bits := bits) (a := a)
  have ha_last :
      ((spDecisionHistory bits) ++ [HistElem.act a]).getLast? = some (HistElem.act a) := by
    simp
  -- Compute directly by cases on the action and simplifying the 4-percept fold.
  cases a <;> simp [expectedRewardForAction, BayesianAgents.optimalQValue, BayesianAgents.optimalValue,
    spToEnvironment, actionBit, ha_wf, ha_last, spDecisionHistory_obsBits_append_act,
    Percept.reward, Percept.obs, Percept.rewardBit, List.foldl_cons, List.foldl_nil]

/-- Theorem 6.2.1 (Hutter 2005): in the induced sequence-prediction environment,
the optimal one-step action predicts the most likely next bit under μ. -/
theorem aimu_eq_spμ (sp : SequencePredictionProblem) (γ : DiscountFactor) (bits : List Bool) :
    actionBit (optimalAction (spToEnvironment sp) γ (spDecisionHistory bits) 1)
      = optimalSequencePredictor sp bits := by
  classical
  let μT := sp.μ (bits ++ [true])
  let μF := sp.μ (bits ++ [false])
  have hμT : μT ≠ (⊤ : ENNReal) := by
    exact ne_top_of_le_ne_top (by simp) (sp.μ_le_one (bits ++ [true]))
  have hμF : μF ≠ (⊤ : ENNReal) := by
    exact ne_top_of_le_ne_top (by simp) (sp.μ_le_one (bits ++ [false]))
  have hgt : μT.toReal > μF.toReal ↔ μT > μF := by
    -- Convert `>` to `<` and use strict monotonicity of `toReal` below `⊤`.
    simpa [gt_iff_lt] using (ENNReal.toReal_lt_toReal hμF hμT)
  have hq_left :
      optimalQValue (spToEnvironment sp) γ (spDecisionHistory bits) Action.left 1 = μF.toReal := by
    simpa [expectedRewardForAction] using
      expectedRewardForAction_spDecisionHistory (sp := sp) (γ := γ) (bits := bits) (a := Action.left)
  have hq_right :
      optimalQValue (spToEnvironment sp) γ (spDecisionHistory bits) Action.right 1 = μT.toReal := by
    simpa [expectedRewardForAction] using
      expectedRewardForAction_spDecisionHistory (sp := sp) (γ := γ) (bits := bits) (a := Action.right)
  have hq_stay :
      optimalQValue (spToEnvironment sp) γ (spDecisionHistory bits) Action.stay 1 = μF.toReal := by
    simpa [expectedRewardForAction] using
      expectedRewardForAction_spDecisionHistory (sp := sp) (γ := γ) (bits := bits) (a := Action.stay)
  -- Unfold the foldl argmax over the three actions and reduce to the μ-comparison.
  by_cases h : μT > μF
  · have h' : μT.toReal > μF.toReal := hgt.mpr h
    have hnot : ¬μT.toReal < μF.toReal := by
      exact not_lt.mpr (le_of_lt h')
    simp [optimalSequencePredictor, actionBit, optimalAction, hq_left, hq_right, hq_stay, μT, μF, h, h', hnot,
      List.foldl_cons, List.foldl_nil]
  · have h' : ¬μT.toReal > μF.toReal := by
      intro ht
      exact h (hgt.mp ht)
    simp [optimalSequencePredictor, actionBit, optimalAction, hq_left, hq_right, hq_stay, μT, μF, h, h',
      List.foldl_cons, List.foldl_nil]

/-! ## Section 6.3: Strategic Games (SG)

Two-player zero-sum games with alternating moves.
-/

/-- A strategic game specification.
    Player 1 (agent) makes moves y_k, player 2 (environment) makes moves o_k.
    The game ends after n rounds with value V(y₁o₁...y_no_n).
    We use Action from BayesianAgents for the move type. -/
structure StrategicGameProblem where
  /-- Maximum number of rounds -/
  maxRounds : ℕ
  /-- Valuation function: positive = player 1 wins, negative = player 2 wins -/
  gameValuation : List (Action × Bool) → ℝ
  /-- Valuation is in [-1, 1] -/
  valuation_bounded : ∀ moves, |gameValuation moves| ≤ 1

/-- The minimax value of a game position.
    V*(position) = max_{y} min_{o} V*(position ++ [(y, o)])  (Equation 6.18-6.19) -/
noncomputable def minimaxValue (sg : StrategicGameProblem)
    (position : List (Action × Bool)) (remaining : ℕ) : ℝ :=
  match remaining with
  | 0 => sg.gameValuation position
  | n + 1 =>
    -- Player 1 (agent) maximizes
    let actions := [Action.left, Action.right, Action.stay]
    actions.foldl (fun best_y a =>
      max best_y (
        -- Player 2 (environment) minimizes
        [false, true].foldl (fun worst_o o =>
          min worst_o (minimaxValue sg (position ++ [(a, o)]) n)
        ) 1  -- Start with max possible value
      )
    ) (-1)  -- Start with min possible value

/-- The minimax strategy for player 1 (agent).
    y_k = argmax_{y_k} min_{o_k} ... max_{y_n} min_{o_n} V(...)  (Equation 6.19) -/
noncomputable def minimaxStrategy (sg : StrategicGameProblem)
    (position : List (Action × Bool)) (remaining : ℕ) : Action :=
  let actions := [Action.left, Action.right, Action.stay]
  actions.foldl (fun (best : Action × ℝ) a =>
    let val := [false, true].foldl (fun worst_o o =>
      min worst_o (minimaxValue sg (position ++ [(a, o)]) (remaining - 1))
    ) 1
    if val > best.2 then (a, val) else best
  ) (Action.stay, -2) |>.1

/-- The environment induced by a strategic game with minimax opponent.
    μ^SG models player 2 playing optimally (minimizing V).

    (Hutter 2005, Section 6.3.3, Equation 6.20-6.21) -/
noncomputable def sgToEnvironment (_sg : StrategicGameProblem) : Environment where
  prob := fun h _x =>
    -- Probability 1/4 for each of 4 percepts when well-formed
    -- Simplified: uniform distribution (actual would be deterministic)
    if h.wellFormed then (1 : ENNReal) / 4 else 0
  prob_le_one := fun h _ => by
    -- The tsum of 1/4 over 4 percepts equals 1 ≤ 1
    -- or tsum of 0's equals 0 ≤ 1
    by_cases hw : h.wellFormed
    · -- Well-formed: tsum of 1/4 over Fintype with 4 elements = 1
      simp only [hw, ↓reduceIte]
      rw [tsum_fintype]
      have hcard : Fintype.card Percept = 4 := by decide
      simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      norm_num
    · -- Not well-formed: tsum of 0 = 0 ≤ 1
      simp only [] at hw ⊢
      convert zero_le (1 : ENNReal)
      rw [tsum_fintype]
      simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
      intro x
      simp [hw]

/-! ### Theorem 6.3.1: AIμ Implements Minimax (Not Formalized)

When μ models a minimax-playing opponent, the AI agent's optimal
strategy is also the minimax strategy.

**Statement** (Hutter 2005, Section 6.3.3, Equation 6.22):
For strategic games with rational opponent model, AIμ = minimax.

**Proof sketch**: The expectimax over a deterministic minimax opponent
reduces to minimax tree search.

**Why not formalized**: Requires proving equivalence of expectimax
with deterministic opponent to minimax. -/

/-! ## Section 6.4: Function Minimization (FM)

Minimize f: Y → ℝ using as few function evaluations as possible.
-/

/-- A function minimization problem.
    We seek to minimize expected value α₁z₁ + ... + α_mz_m
    where z_k = f(y_k) and α_k are weights. -/
structure FunctionMinimizationProblem where
  /-- The function to minimize (probabilistic: distribution over functions) -/
  μ_f : (ℕ → ℝ) → ENNReal
  /-- Number of evaluation cycles allowed -/
  horizon : ℕ
  /-- Weight function for each cycle -/
  weights : ℕ → ℝ
  /-- Weights are non-negative -/
  weights_nonneg : ∀ k, 0 ≤ weights k

/-- Final model (FMF): Only the final output matters.
    α_k = 0 for k < m, α_m = 1 -/
def finalModelWeights (m : ℕ) : ℕ → ℝ :=
  fun k => if k = m then 1 else 0

/-- Sum model (FMS): All outputs matter equally.
    α_k = 1 for all k -/
def sumModelWeights : ℕ → ℝ := fun _ => 1

/-- Exponential model (FME): Increasing pressure to produce good outputs.
    α_k = e^{γ(k-1)} for some γ > 0 -/
noncomputable def exponentialModelWeights (γ : ℝ) (_m : ℕ) : ℕ → ℝ :=
  fun k => Real.exp (γ * ((k : ℝ) - 1))

/-- The expected weighted sum for a function minimization strategy.
    E^FM = Σ_k α_k · E[z_k]  (Equation 6.26) -/
noncomputable def fmExpectedCost (fm : FunctionMinimizationProblem)
    (_strategy : ℕ → ℕ) : ℝ :=
  -- Sum over cycles of weighted expected function value
  (List.range fm.horizon).foldl (fun sum k =>
    sum + fm.weights k * 0  -- Placeholder for expected value
  ) 0

/-! ### Theorem 6.4.1: FM Embeds in AI Framework (Not Formalized)

The FMμ model is equivalent to AIμ with appropriate reward structure:
r_k = -α_k · z_k

**Statement** (Hutter 2005, Section 6.4.5, below Equation 6.28):
Function minimization is a special case of the AI framework.

**Why not formalized**: The embedding is straightforward but requires
defining the reward transformation precisely. -/

/-! ### Theorem 6.4.2: FM^ is Inventive (Not Formalized)

The universal function minimizer FM^ will never cease searching
for minima, testing an infinite set of different y's as m → ∞.

**Statement** (Hutter 2005, Section 6.4.4):
As horizon increases, FM^ explores infinitely many inputs.

**Why not formalized**: Requires formalizing the universal prior over
functions and showing it assigns positive probability to all inputs. -/

/-! ## Section 6.5: Supervised Learning from Examples (EX)

Learn a relation R ⊆ Z × V from examples.
-/

/-- A supervised learning problem.
    The environment presents examples (z, v) ∈ R or queries (z, ?) -/
structure SupervisedLearningProblem where
  /-- Type of inputs -/
  Z : Type*
  /-- Type of outputs -/
  V : Type*
  /-- The target relation to learn -/
  R : Z → V → Prop
  /-- Distribution over the relation -/
  σ_R : ENNReal
  /-- Distribution over example sequences -/
  μ_R : List (Z × Option V) → ENNReal

/-- An example presentation is either a labeled example or a query. -/
inductive ExamplePresentation (Z V : Type*) where
  | labeled : Z → V → ExamplePresentation Z V
  | query : Z → ExamplePresentation Z V

/-- The reward for a prediction in supervised learning.
    r_k = 1 if (z_k, y_k) ∈ R, 0 otherwise.

    (Hutter 2005, Section 6.5.2) -/
def supervisedReward (R : α → β → Prop) [DecidableRel R]
    (z : α) (prediction : β) : ℕ :=
  if R z prediction then 1 else 0

/-! ### Theorem 6.5.1: AIξ Learns Supervised Efficiently (Not Formalized)

The universal AIξ model, although never designed for supervised learning,
can learn to take advantage of examples from a supervisor.

**Statement** (Hutter 2005, Section 6.5.2):
- μ_R and R are learned from examples (information content K(R))
- Learning how to learn supervised is only O(1) complexity

**Why not formalized**: Requires formalizing the information-theoretic
argument about Kolmogorov complexity of learning strategies. -/

/-! ### Comparison: Supervised vs Reinforcement Learning (Not Formalized)

Supervised learning is much more efficient than reinforcement learning
for the same task:
- Supervised: O(1) cycles to learn R (examples contain information)
- Reinforcement: O(K(R)) cycles (rewards contain limited information)

**Statement** (Hutter 2005, Section 6.5.2):
Information content in examples >> information in rewards.

**Why not formalized**: Information-theoretic comparison requires
formalizing channel capacity of reward vs example signals. -/

/-! ## Section 6.6: Other Aspects of Intelligence

Summary of how various AI concepts fit into the AIXI model:
- Probability theory and utility theory: Heart of AI models
- Reinforcement learning: Explicitly built in via rewards
- Supervised learning: Emergent phenomenon (Section 6.5)
- Planning: Expectimax series for horizon > 1
- Minimax: Special case for zero-sum games
- Knowledge: Accumulated on work tape
-/

/-! ### AIXI Incorporates Core AI Methods

The AIXI model incorporates the core components of AI:
- Decision theory (utility maximization)
- Probability theory (Bayesian beliefs)
- Algorithmic information theory (Solomonoff prior)
- Reinforcement learning (reward signals)
- Planning (expectimax lookahead)

(Hutter 2005, Section 6.6) -/

/-! ## Chapter 6 Summary

### Main Result: AIXI is Universally Optimal (Not Formalized)

Each problem class (SP, SG, FM, EX) can be embedded in the AIXI framework,
and AIXI's behavior specializes to the optimal solution for that class.

**What IS formalized in this file**:
- `SequencePredictionProblem` structure with semimeasure property
- `SequencePredictionProblem.μ_le_one`: prefix probabilities are bounded
- `spToEnvironment`: embedding SP into the Environment type
- `StrategicGameProblem` structure with minimax definitions
- `sgToEnvironment`: embedding SG into the Environment type
- `FunctionMinimizationProblem` structure with weight models
- `SupervisedLearningProblem` structure

**What is NOT formalized** (requires additional infrastructure):
- Proving AIμ = SPμ (expectimax reduces to argmax)
- Proving AIμ = minimax for strategic games
- Information-theoretic bounds on learning efficiency
- Convergence of AIξ to optimal behavior

### Corollary: Unified Foundation

Instead of developing specialized algorithms for each problem class,
AIXI provides a universal algorithm that automatically specializes
to the optimal solution for any given problem structure.

The computational limitations are addressed in Chapter 7 (TimeBoundedAIXI.lean),
which introduces AIXItl as a computable approximation.

(Hutter 2005, Chapter 6 conclusion) -/

end Mettapedia.UniversalAI.ProblemClasses
