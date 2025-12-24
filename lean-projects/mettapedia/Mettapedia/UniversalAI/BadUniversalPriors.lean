import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mettapedia.UniversalAI.BayesianAgents

/-!
# Bad Universal Priors and Notions of Optimality

This file formalizes the negative results from Leike & Hutter (2015):
"Bad Universal Priors and Notions of Optimality"

## Main Results

These results show fundamental limitations of AIXI and Bayesian RL:

* **Theorem 7 (Dogmatic Prior)**: For any computable policy π, there exists a
  universal mixture ξ' that makes AIXI follow π (as long as V^π > ε)

* **Theorem 18 (Pareto Optimality is Trivial)**: Every policy is Pareto optimal
  in the class of all computable environments

* **Corollary 13**: Some AIXIs are stupid - AIXI can score arbitrarily close
  to minimum intelligence

* **Corollary 14**: Any computable policy can score arbitrarily close to
  maximum intelligence

## Philosophical Implications

These results show that AIXI is a *relative* theory of intelligence,
dependent on the choice of the Universal Turing Machine (UTM).
There can be no invariance theorem for AIXI as there is for Kolmogorov complexity.

## References

- Leike, J. & Hutter, M. (2015). "Bad Universal Priors and Notions of Optimality"
  JMLR Workshop and Conference Proceedings vol 40:1-16
- arXiv:1510.05572
-/

namespace Mettapedia.UniversalAI.BadUniversalPriors

open BayesianAgents

/-! ## Hell and Heaven Environments

The key construction uses "hell" (reward 0 forever) and "heaven" (reward 1 forever)
environments to manipulate AIXI's behavior.
-/

/-- The Hell environment: always returns reward 0.
    Used to punish agents that deviate from a prescribed policy. -/
noncomputable def hellEnvironment : Environment where
  prob := fun h x =>
    -- Probability 1/2 for each of 2 percepts with rewardBit = false
    if h.wellFormed ∧ x.rewardBit = false then (1 : ENNReal) / 2 else 0
  prob_le_one := fun h _ => by
    rw [tsum_fintype]
    by_cases hw : h.wellFormed
    · -- Well-formed: sum over 4 percepts = 1/2 + 0 + 1/2 + 0 = 1
      simp only [hw, true_and]
      -- Use equivalence with Bool × Bool to expand sum
      let e : Percept ≃ Bool × Bool := ⟨
        fun p => match p with | Percept.mk a b => (a, b),
        fun ⟨a, b⟩ => Percept.mk a b,
        fun p => by cases p; rfl,
        fun ⟨a, b⟩ => rfl⟩
      have h1 : ∑ x : Percept, (if x.rewardBit = false then (1 : ENNReal) / 2 else 0) =
          ∑ x : Bool × Bool, (if x.2 = false then (1 : ENNReal) / 2 else 0) := by
        rw [Fintype.sum_equiv e]
        intro ⟨a, b⟩; rfl
      rw [h1]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte]
      -- Sum over second Bool: (if false = false then 1/2 else 0) + (if true = false then 1/2 else 0)
      --                     = 1/2 + 0 = 1/2
      -- Total: 1/2 + 1/2 = 1
      sorry
    · -- Not well-formed: all probabilities are 0
      simp only [] at hw ⊢
      convert zero_le (1 : ENNReal)
      simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
      intro x
      simp [hw]

/-- The Heaven environment: always returns reward 1.
    Used to reward agents that follow a prescribed policy. -/
noncomputable def heavenEnvironment : Environment where
  prob := fun h x =>
    -- Probability 1/2 for percepts with rewardBit = true
    if h.wellFormed ∧ x.rewardBit = true then (1 : ENNReal) / 2 else 0
  prob_le_one := fun h _ => by
    rw [tsum_fintype]
    by_cases hw : h.wellFormed
    · -- Well-formed: sum over 4 percepts = 0 + 1/2 + 0 + 1/2 = 1
      simp only [hw, true_and]
      let e : Percept ≃ Bool × Bool := ⟨
        fun p => match p with | Percept.mk a b => (a, b),
        fun ⟨a, b⟩ => Percept.mk a b,
        fun p => by cases p; rfl,
        fun ⟨a, b⟩ => rfl⟩
      have h1 : ∑ x : Percept, (if x.rewardBit = true then (1 : ENNReal) / 2 else 0) =
          ∑ x : Bool × Bool, (if x.2 = true then (1 : ENNReal) / 2 else 0) := by
        rw [Fintype.sum_equiv e]
        intro ⟨a, b⟩; rfl
      rw [h1]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte]
      sorry
    · -- Not well-formed: all probabilities are 0
      simp only [] at hw ⊢
      convert zero_le (1 : ENNReal)
      simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left]
      intro x
      simp [hw]

/-- Value in hell environment is 0 (no rewards ever). -/
theorem value_in_hell (π : Agent) (γ : DiscountFactor) (h : History) :
    value hellEnvironment π γ h 0 = 0 := by
  simp only [value_zero]

/-- In this model `horizon` counts *half-steps* (agent move / environment move).
So a single interaction cycle needs `horizon = 2`. In heaven, the value is `1`. -/
theorem value_in_heaven_eq_one (π : Agent) (γ : DiscountFactor) :
    value heavenEnvironment π γ [] 2 = 1 := by
  -- Expand the 2-step value: one action choice (value) and one percept step (qValue).
  -- All percepts with rewardBit=true have prob 1/2 and reward 1, others 0
  -- So we get: sum over actions of (policy(a) * sum over percepts of (prob * reward))
  -- = sum over actions of (policy(a) * (1/2 * 1 + 1/2 * 1)) = sum of policy(a) = 1
  sorry

theorem value_in_heaven_positive (π : Agent) (γ : DiscountFactor) :
    0 < value heavenEnvironment π γ [] 2 := by
  simp [value_in_heaven_eq_one (π := π) (γ := γ)]

/-! ## The Dogmatic Prior (Theorem 7)

The key construction: given any computable policy π, we create an environment ν
that mimics the universal mixture ξ while following π, but sends the agent to
hell (reward 0 forever) if it deviates from π.
-/

/-- A deterministic policy: selects a single action with probability 1.
    Used to define the "prescribed" behavior in the dogmatic prior. -/
noncomputable def deterministicPolicy (actionFn : History → Action) : Agent where
  policy := fun h a => if a = actionFn h then 1 else 0
  policy_sum_one := fun h _ => by
    sorry

/-- Create an environment that punishes deviation from a prescribed action function.

    ν(e_{1:t} | a_{1:t}) =
      - ξ(e_{1:t} | a_{1:t})  if a_k = π(æ_{<k}) for all k ≤ t
      - Goes to hell (reward 0) if agent deviates

    For simplicity, we condition on whether the FIRST action matches. -/
noncomputable def dogmaticEnv (ξ : Environment) (targetAction : Action) : Environment where
  prob := fun h x =>
    -- Check if first action (if any) matches target
    let firstAction := h.actions.head?
    match firstAction with
    | none => ξ.prob h x  -- No actions yet, behave like ξ
    | some a =>
      if a = targetAction then
        ξ.prob h x  -- Followed policy, behave like ξ
      else
        -- Deviated: go to hell (only reward 0 percepts)
        if x.rewardBit = false then ξ.prob h x else 0
  prob_le_one := fun h hw => by
    cases hfirst : h.actions.head? with
    | none => exact ξ.prob_le_one h hw
    | some a =>
      -- Need to handle the match case for `some a`
      by_cases ha : a = targetAction
      · simp only [ha, ↓reduceIte]
        exact ξ.prob_le_one h hw
      · simp only [ha, ↓reduceIte]
        -- Sum is ≤ sum over ξ which is ≤ 1
        calc ∑' x, (if x.rewardBit = false then ξ.prob h x else 0)
            ≤ ∑' x, ξ.prob h x := by
              apply ENNReal.tsum_le_tsum
              intro x; split_ifs <;> simp
          _ ≤ 1 := ξ.prob_le_one h hw

/-- Key property: The dogmatic environment equals the base environment
    for histories where the agent follows the target action. -/
theorem dogmatic_equals_base_on_policy (ξ : Environment) (targetAction : Action)
    (h : History) (x : Percept)
    (hfirst : h.actions.head? = some targetAction) :
    (dogmaticEnv ξ targetAction).prob h x = ξ.prob h x := by
  simp only [dogmaticEnv, hfirst, ↓reduceIte]

/-! ## Theorem 7: The Dogmatic Prior

For any computable policy π, any universal mixture ξ, and ε > 0,
there exists a universal mixture ξ' such that for any history h
consistent with π with V^π_ξ(h) > ε, the action π(h) is the
unique ξ'-optimal action.
-/

/-- The dogmatic prior mixture: ξ' = (1/2)ν + (ε/2)ξ
    where ν is the dogmatic environment for the target action. -/
noncomputable def dogmaticMixture (ξ : Environment) (targetAction : Action)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : Environment where
  prob := fun h x =>
    (1/2 : ENNReal) * (dogmaticEnv ξ targetAction).prob h x +
    (ENNReal.ofReal (ε/2)) * ξ.prob h x
  prob_le_one := fun h hw => by
    have h1 : ∑' x, ((1/2 : ENNReal) * (dogmaticEnv ξ targetAction).prob h x +
               ENNReal.ofReal (ε/2) * ξ.prob h x) =
        (1/2) * ∑' x, (dogmaticEnv ξ targetAction).prob h x +
        ENNReal.ofReal (ε/2) * ∑' x, ξ.prob h x := by
      rw [ENNReal.tsum_add]
      congr 1 <;> rw [ENNReal.tsum_mul_left]
    rw [h1]
    have hdog_le : ∑' x, (dogmaticEnv ξ targetAction).prob h x ≤ 1 :=
      (dogmaticEnv ξ targetAction).prob_le_one h hw
    have hξ_le : ∑' x, ξ.prob h x ≤ 1 := ξ.prob_le_one h hw
    have hε2_le : ENNReal.ofReal (ε/2) ≤ 1/2 := by
      have h1 : ε / 2 ≤ 1 / 2 := by linarith
      calc ENNReal.ofReal (ε/2) ≤ ENNReal.ofReal (1/2) := ENNReal.ofReal_le_ofReal h1
        _ = 1/2 := by simp only [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2),
            ENNReal.ofReal_ofNat]
    calc (1/2 : ENNReal) * ∑' x, (dogmaticEnv ξ targetAction).prob h x +
         ENNReal.ofReal (ε/2) * ∑' x, ξ.prob h x
        ≤ (1/2) * 1 + (1/2) * 1 := by
            apply add_le_add
            · exact mul_le_mul_left' hdog_le _
            · calc ENNReal.ofReal (ε/2) * ∑' x, ξ.prob h x
                  ≤ (1/2) * ∑' x, ξ.prob h x := mul_le_mul_right' hε2_le _
                _ ≤ (1/2) * 1 := mul_le_mul_left' hξ_le _
      _ = 1 := by sorry

/-! ### Main Theorem Statement

**Theorem 7** (Leike & Hutter 2015):
Let π be any computable policy, let ξ be any universal mixture,
and let ε > 0. There is a universal mixture ξ' such that for any
history h consistent with π and V^π_ξ(h) > ε, the action π(h) is
the unique ξ'-optimal action.

**Proof idea**:
1. Construct ν that mimics ξ while following π, but goes to hell on deviation
2. Set ξ' = (1/2)ν + (ε/2)ξ
3. Since ν equals ξ on policy π, posterior weight of ν stays at 2/(1+ε)
4. Deviating gives V* ≤ ε/(1+ε) < ε < V^π_ξ(h), so deviation is suboptimal
-/

/-!
### Theorem 7 (Dogmatic Prior) (Not Formalized)

Statement: For any target action with positive value, the dogmatic mixture makes
following that action strictly better than any deviation.

Leike & Hutter (2015), Theorem 7, is a *value comparison* result for a
carefully engineered universal mixture. Proving it here would require:

- a probability-valued (ENNReal / ℝ≥0∞) formulation of `value`/`qValue` so that
  mixture linearity is available as an algebraic lemma (our current definitions
  use `ENNReal.toReal` inside the recursion, which blocks clean linearity),
- an explicit notion of “universal mixture” and “computable policy” connected
  to the computability development elsewhere in Mettapedia,
- a careful “go to hell after deviation” environment construction that matches
  the paper (the current `dogmaticEnv` only checks the *first* action as a toy model).

The definitions above (`dogmaticEnv`, `dogmaticMixture`) are kept as a starting
point, but the full theorem statement is documented rather than asserted.
-/

/-! ## Theorem 18: Pareto Optimality is Trivial

Every policy is Pareto optimal in the class of all computable environments.
This completely undermines Pareto optimality as an optimality criterion.
-/

/-- Definition of Pareto optimality.

    A policy π is Pareto optimal in environment class M iff there is no
    policy π̃ that does at least as well in all environments and
    strictly better in at least one. -/
def ParetoOptimal (π : Agent) (M : Set Environment) (γ : DiscountFactor) (m : ℕ) : Prop :=
  ¬∃ π' : Agent,
    (∀ ν ∈ M, value ν π' γ [] m ≥ value ν π γ [] m) ∧
    (∃ ρ ∈ M, value ρ π' γ [] m > value ρ π γ [] m)

/-- A "buddy environment" for a specific action that rewards that action
    and punishes all others.

    - If agent takes targetAction at first step, go to heaven (reward 1 forever)
    - If agent takes any other action, go to hell (reward 0 forever)

    This environment is computable and demonstrates that every policy
    is Pareto optimal. -/
noncomputable def buddyEnvironment (targetAction : Action) : Environment where
  prob := fun h x =>
    match h.actions.head? with
    | none =>
      -- No action yet: uniform distribution
      if h.wellFormed then (1 : ENNReal) / 4 else 0
    | some a =>
      if a = targetAction then
        -- Went to heaven: reward 1
        if h.wellFormed ∧ x.rewardBit = true then (1 : ENNReal) / 2 else 0
      else
        -- Went to hell: reward 0
        if h.wellFormed ∧ x.rewardBit = false then (1 : ENNReal) / 2 else 0
  prob_le_one := fun h hw => by
    cases hfirst : h.actions.head? with
    | none =>
      sorry
    | some a =>
      sorry

/-- **Theorem 18**: Every policy is Pareto optimal.

    **Proof**: For any policy π, we construct "buddy environments" that
    defend π against any challenger π̃. For each history h where π and π̃
    first disagree, there's an environment that rewards π's action and
    punishes π̃'s action. Together, these environments ensure no π̃ can
    dominate π.

    This is a devastating result: Pareto optimality is meaningless because
    every policy, no matter how bad, is Pareto optimal! -/
theorem pareto_optimality_trivial_horizon2 (π : Agent) (γ : DiscountFactor)
    (M : Set Environment) (hM : ∀ ν, ν ∈ M) :
    ParetoOptimal π M γ 2 := by
  classical
  unfold ParetoOptimal
  intro hcontra
  rcases hcontra with ⟨π', hdomAll, ρ, hρM, hstrict⟩
  -- Use the buddy environments for each first action to force agreement of first-step action
  -- distributions; then horizon-2 value is identical in every environment, contradicting `hstrict`.
  have hwell : History.wellFormed [] := by simp only [History.wellFormed]
  -- Helper: value in a buddy environment at horizon 2 equals the policy mass on the defended action.
  have hbuddy :
      ∀ a : Action, value (buddyEnvironment a) π γ [] 2 = (π.policy [] a).toReal ∧
        value (buddyEnvironment a) π' γ [] 2 = (π'.policy [] a).toReal := by
    intro a
    constructor
    · -- Value for π
      simp only [value, qValue, buddyEnvironment, History.wellFormed, History.actions,
        List.foldl, List.head?, ne_eq, ↓reduceIte]
      sorry
    · -- Value for π'
      simp only [value, qValue, buddyEnvironment, History.wellFormed, History.actions,
        List.foldl, List.head?, ne_eq, ↓reduceIte]
      sorry

  have hprob_ge : ∀ a : Action, (π'.policy [] a).toReal ≥ (π.policy [] a).toReal := by
    intro a
    have haM : buddyEnvironment a ∈ M := hM (buddyEnvironment a)
    have hdom := hdomAll (buddyEnvironment a) haM
    -- Rewrite both sides using `hbuddy`.
    have hπ : value (buddyEnvironment a) π γ [] 2 = (π.policy [] a).toReal := (hbuddy a).1
    have hπ' : value (buddyEnvironment a) π' γ [] 2 = (π'.policy [] a).toReal := (hbuddy a).2
    -- Use the dominance inequality.
    simp only [hπ, hπ'] at hdom
    exact hdom

  -- Convert the ENNReal "sum to 1" property into a real sum over the 3 actions.
  have hsumπ : (π.policy [] Action.left).toReal
      + (π.policy [] Action.right).toReal
      + (π.policy [] Action.stay).toReal = 1 := by
    sorry

  have hsumπ' : (π'.policy [] Action.left).toReal
      + (π'.policy [] Action.right).toReal
      + (π'.policy [] Action.stay).toReal = 1 := by
    sorry

  -- From componentwise ≥ and equal sums, all three components are equal.
  have hleft : (π'.policy [] Action.left).toReal = (π.policy [] Action.left).toReal := by
    have hge := hprob_ge Action.left
    have hge_rest :
        (π'.policy [] Action.right).toReal + (π'.policy [] Action.stay).toReal ≥
          (π.policy [] Action.right).toReal + (π.policy [] Action.stay).toReal := by
      linarith [hprob_ge Action.right, hprob_ge Action.stay]
    -- Use sums to get the reverse inequality for the left component.
    have hle : (π'.policy [] Action.left).toReal ≤ (π.policy [] Action.left).toReal := by
      -- Rearrange via `hsumπ` and `hsumπ'`.
      have : (π'.policy [] Action.left).toReal =
          1 - ((π'.policy [] Action.right).toReal + (π'.policy [] Action.stay).toReal) := by
        linarith [hsumπ']
      have : (π'.policy [] Action.left).toReal ≤
          1 - ((π.policy [] Action.right).toReal + (π.policy [] Action.stay).toReal) := by
        have hsub : 1 - ((π'.policy [] Action.right).toReal + (π'.policy [] Action.stay).toReal) ≤
            1 - ((π.policy [] Action.right).toReal + (π.policy [] Action.stay).toReal) := by
          exact sub_le_sub_left hge_rest _
        -- replace the left side with the expression from `hsumπ'`
        linarith [hsumπ', hsub]
      -- The right-hand side is exactly the left component of π by `hsumπ`.
      linarith [hsumπ, this]
    exact le_antisymm hle hge

  have hright : (π'.policy [] Action.right).toReal = (π.policy [] Action.right).toReal := by
    have hge := hprob_ge Action.right
    have hge_rest :
        (π'.policy [] Action.left).toReal + (π'.policy [] Action.stay).toReal ≥
          (π.policy [] Action.left).toReal + (π.policy [] Action.stay).toReal := by
      linarith [hprob_ge Action.left, hprob_ge Action.stay]
    have hle : (π'.policy [] Action.right).toReal ≤ (π.policy [] Action.right).toReal := by
      have hsub : 1 - ((π'.policy [] Action.left).toReal + (π'.policy [] Action.stay).toReal) ≤
          1 - ((π.policy [] Action.left).toReal + (π.policy [] Action.stay).toReal) := by
        exact sub_le_sub_left hge_rest _
      have hπ'expr : (π'.policy [] Action.right).toReal =
          1 - ((π'.policy [] Action.left).toReal + (π'.policy [] Action.stay).toReal) := by
        linarith [hsumπ']
      have hπexpr : (π.policy [] Action.right).toReal =
          1 - ((π.policy [] Action.left).toReal + (π.policy [] Action.stay).toReal) := by
        linarith [hsumπ]
      linarith [hπ'expr, hπexpr, hsub]
    exact le_antisymm hle hge

  have hstay : (π'.policy [] Action.stay).toReal = (π.policy [] Action.stay).toReal := by
    -- Obtain from sum equality once left/right agree.
    linarith [hsumπ, hsumπ', hleft, hright]

  -- With identical first-step action probabilities, horizon-2 values coincide in every environment.
  have hEqVal : value ρ π' γ [] 2 = value ρ π γ [] 2 := by
    -- Expand both values and rewrite using the probability equalities.
    simp [value, qValue, History.wellFormed, List.foldl, hleft, hright, hstay]

  -- Contradiction with the assumed strict improvement in some environment ρ.
  have : ¬ value ρ π' γ [] 2 > value ρ π γ [] 2 := by
    simp only [hEqVal, lt_self_iff_false, not_false_eq_true]
  exact this hstrict

/-!
### Theorem 18 (Full Generality) (Not Formalized)

`pareto_optimality_trivial_horizon2` captures the core phenomenon already for one
interaction cycle (`horizon = 2`). Extending this to arbitrary horizons (and to the
standard Pareto definition quantified over *all histories*) requires a “buddy
environment” construction indexed by the *first disagreement history*, as in
Leike & Hutter (2015). We keep the definitions above as scaffolding, but do not
assert the full theorem here.
-/

/-! ## Corollaries: Intelligence is Subjective

These corollaries show that the Legg-Hutter intelligence measure
and balanced Pareto optimality depend entirely on the UTM choice.
-/

/-!
### Corollary 13: Some AIXIs are stupid.

For any universal mixture ξ and every ε > 0, there is a universal
mixture ξ' such that AIXI with ξ' scores near-minimum intelligence
when measured with ξ.

**Proof sketch**: Use the dogmatic prior to make AIXI follow a
near-worst policy.
-/

/-!
### Corollary 14: AIXI is stupid for some intelligence measures.

For any ξ-optimal policy π*_ξ and for every ε > 0, there is a
universal mixture ξ' such that π*_ξ scores near-zero and some
other policy scores near-maximum.

**Proof sketch**: The dogmatic prior for any other policy will
make AIXI score near-maximum.
-/

/-!
### Corollary 15: Computable policies can be smart.

For any computable policy π and any ε > 0, there is a universal
mixture ξ' such that π scores near-maximum intelligence.

**Proof sketch**: Use the dogmatic prior for π.
-/

/-! ## Summary: Implications for AI Safety

These results have profound implications:

1. **No invariance theorem**: Unlike Kolmogorov complexity, AIXI's behavior
   depends fundamentally on the UTM choice. There is no "natural" UTM.

2. **Pareto optimality is meaningless**: Every policy is Pareto optimal,
   so this cannot distinguish good from bad policies.

3. **Intelligence is subjective**: The Legg-Hutter intelligence measure
   can make any computable policy score arbitrarily high or low.

4. **Exploration is crucial**: The underlying problem is that Bayesian
   agents like AIXI don't explore enough. The dogmatic prior exploits
   this by threatening hell for exploration.

5. **Solutions exist**: Adding explicit exploration (BayesExp, knowledge-seeking
   agents, optimism) can restore weak asymptotic optimality.

Table of optimality notions (from paper):
| Notion                        | Status                                    |
|-------------------------------|-------------------------------------------|
| μ-optimal                     | Requires knowing true environment         |
| Pareto optimality             | Trivial (Theorem 18)                      |
| Balanced Pareto optimality    | UTM-dependent (Corollary 13, 14)          |
| Self-optimizing               | Doesn't apply to M^CCS_LSC                |
| Strong asymptotic optimality  | Impossible                                |
| Weak asymptotic optimality    | Achievable (BayesExp), but not by AIXI    |

-/

end Mettapedia.UniversalAI.BadUniversalPriors
