import Mathlib.Tactic
import Mettapedia.Logic.UniversalPrediction.PrefixMeasure

/-!
# Beta-Bernoulli Predictors as Prefix Measures

This file defines the standard Beta-Bernoulli sequential predictors as `PrefixMeasure`s
on finite binary strings `BinString = List Bool`.

We avoid any integration/Beta-function machinery by defining the prefix probability
recursively via the posterior-predictive rule:

* `μ([]) = 1`
* If `x` has counts `(k,m)` (true/false), then
  * `μ(x ++ [true])  = μ(x) * (k + α) / (k + m + α + β)`
  * `μ(x ++ [false]) = μ(x) * (m + β) / (k + m + α + β)`

For `α=β=1` this is Laplace's rule of succession.
For `α=β=1/2` this is the Jeffreys/KT predictor.

These predictors are useful as *computable competitors* in the universal-mixture
(dominance/regret) story.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical

/-- Count true values in a boolean list. -/
def countTrue (x : BinString) : ℕ := (x.filter (· = true)).length

/-- Count false values in a boolean list. -/
def countFalse (x : BinString) : ℕ := (x.filter (· = false)).length

@[simp] lemma countTrue_nil : countTrue [] = 0 := rfl
@[simp] lemma countFalse_nil : countFalse [] = 0 := rfl

@[simp] lemma countTrue_cons_true (x : BinString) : countTrue (true :: x) = countTrue x + 1 := by
  simp [countTrue, List.filter]

@[simp] lemma countTrue_cons_false (x : BinString) : countTrue (false :: x) = countTrue x := by
  simp [countTrue, List.filter]

@[simp] lemma countFalse_cons_true (x : BinString) : countFalse (true :: x) = countFalse x := by
  simp [countFalse, List.filter]

@[simp] lemma countFalse_cons_false (x : BinString) : countFalse (false :: x) = countFalse x + 1 := by
  simp [countFalse, List.filter]

@[simp] lemma countTrue_append (x y : BinString) : countTrue (x ++ y) = countTrue x + countTrue y := by
  simp [countTrue]

@[simp] lemma countFalse_append (x y : BinString) : countFalse (x ++ y) = countFalse x + countFalse y := by
  simp [countFalse]

@[simp] lemma countTrue_singleton_true : countTrue [true] = 1 := rfl
@[simp] lemma countTrue_singleton_false : countTrue [false] = 0 := rfl
@[simp] lemma countFalse_singleton_true : countFalse [true] = 0 := rfl
@[simp] lemma countFalse_singleton_false : countFalse [false] = 1 := rfl

/-- One-step predictive probabilities for the Beta(α,β) model from current counts. -/
private def betaStepProb (α β : ℝ) (k m : ℕ) (b : Bool) : ℝ :=
  let denom : ℝ := (k + m : ℝ) + α + β
  if b
    then ((k : ℝ) + α) / denom
    else ((m : ℝ) + β) / denom

private lemma betaStepProb_denom_pos (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k m : ℕ) :
    0 < ((k + m : ℝ) + α + β) := by
  have hk : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
  have hm : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
  linarith

private lemma betaStepProb_nonneg (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k m : ℕ) (b : Bool) :
    0 ≤ betaStepProb α β k m b := by
  unfold betaStepProb
  set denom : ℝ := (k + m : ℝ) + α + β
  have hdenom : 0 < denom := by
    simpa [denom] using betaStepProb_denom_pos α β hα hβ k m
  cases b
  · -- false
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    exact div_nonneg (by linarith [hm0, le_of_lt hβ]) (le_of_lt hdenom)
  · -- true
    have hk0 : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    exact div_nonneg (by linarith [hk0, le_of_lt hα]) (le_of_lt hdenom)

/-- Auxiliary definition: prefix probability computed sequentially from counts.

`betaPrefixAux α β k m xs` is the probability of observing `xs` next,
starting from current counts `(k,m)`.
-/
private def betaPrefixAux (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k m : ℕ) : BinString → ENNReal
  | [] => 1
  | b :: xs =>
      let p : ℝ := betaStepProb α β k m b
      ENNReal.ofReal p * betaPrefixAux α β hα hβ (if b then k + 1 else k) (if b then m else m + 1) xs

private lemma betaPrefixAux_nil (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k m : ℕ) :
    betaPrefixAux α β hα hβ k m [] = 1 := rfl

private lemma betaPrefixAux_cons (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k m : ℕ) (b : Bool)
    (xs : BinString) :
    betaPrefixAux α β hα hβ k m (b :: xs) =
      ENNReal.ofReal (betaStepProb α β k m b) *
        betaPrefixAux α β hα hβ (if b then k + 1 else k) (if b then m else m + 1) xs := by
  rfl

/-- The key prefix-measure identity: appending one bit splits the mass.

This is proved by list induction, using the fact that the predictive probabilities
for `true/false` sum to `1` at every state.
-/
private theorem betaPrefixAux_additive
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (k m : ℕ) (xs : BinString) :
    betaPrefixAux α β hα hβ k m (xs ++ [false]) +
        betaPrefixAux α β hα hβ k m (xs ++ [true]) =
      betaPrefixAux α β hα hβ k m xs := by
  induction xs generalizing k m with
  | nil =>
      -- Direct computation at the current counts.
      simp [betaPrefixAux, betaStepProb]
      -- Reduce to: ofReal(pFalse) + ofReal(pTrue) = 1.
      set denom : ℝ := (k + m : ℝ) + α + β
      have hdenom : 0 < denom := by
        simpa [denom] using betaStepProb_denom_pos α β hα hβ k m
      have hk0 : 0 ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
      have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
      have hpos_true : 0 ≤ ((k : ℝ) + α) / denom :=
        div_nonneg (by linarith [hk0, le_of_lt hα]) (le_of_lt hdenom)
      have hpos_false : 0 ≤ ((m : ℝ) + β) / denom :=
        div_nonneg (by linarith [hm0, le_of_lt hβ]) (le_of_lt hdenom)
      -- Combine via `ofReal_add` and simplify.
      have :
          ENNReal.ofReal (((m : ℝ) + β) / denom) + ENNReal.ofReal (((k : ℝ) + α) / denom) =
            ENNReal.ofReal (1 : ℝ) := by
        -- `a+b` is nonnegative, so `ofReal (a+b) = ofReal a + ofReal b`.
        have hsum_nonneg : 0 ≤ ((m : ℝ) + β) / denom + ((k : ℝ) + α) / denom := by
          linarith [hpos_true, hpos_false]
        -- Use commutativity to match the lemma order.
        calc
          ENNReal.ofReal (((m : ℝ) + β) / denom) + ENNReal.ofReal (((k : ℝ) + α) / denom)
              = ENNReal.ofReal (((m : ℝ) + β) / denom + ((k : ℝ) + α) / denom) := by
                  symm
                  exact ENNReal.ofReal_add hpos_false hpos_true
          _ = ENNReal.ofReal (1 : ℝ) := by
                  congr 1
                  field_simp [denom, ne_of_gt hdenom]
                  ring
      simpa using this
  | cons b xs ih =>
      -- Peel off the head bit; both sides share the same first-step factor.
      cases b
      · -- b = false
        -- First rewrite the inner sum via the induction hypothesis at the updated counts `(k, m+1)`.
        have ih' :
            betaPrefixAux α β hα hβ k (m + 1) (xs ++ [false]) +
                betaPrefixAux α β hα hβ k (m + 1) (xs ++ [true]) =
              betaPrefixAux α β hα hβ k (m + 1) xs := by
          simpa using (ih (k := k) (m := m + 1))
        -- Expand one step and factor out the common first-step probability.
        simp [betaPrefixAux, betaStepProb]
        -- At this point, the goal is `p*A + p*B = p*C` with `A+B=C`.
        have hmul :
            ENNReal.ofReal ((↑m + β) / (↑k + ↑m + α + β)) *
                (betaPrefixAux α β hα hβ k (m + 1) (xs ++ [false]) +
                  betaPrefixAux α β hα hβ k (m + 1) (xs ++ [true])) =
              ENNReal.ofReal ((↑m + β) / (↑k + ↑m + α + β)) *
                betaPrefixAux α β hα hβ k (m + 1) xs := by
          simpa using congrArg
            (fun t =>
              ENNReal.ofReal ((↑m + β) / (↑k + ↑m + α + β)) * t) ih'
        -- Convert `p*(A+B)` to `p*A + p*B`.
        calc
          ENNReal.ofReal ((↑m + β) / (↑k + ↑m + α + β)) *
                betaPrefixAux α β hα hβ k (m + 1) (xs ++ [false]) +
              ENNReal.ofReal ((↑m + β) / (↑k + ↑m + α + β)) *
                betaPrefixAux α β hα hβ k (m + 1) (xs ++ [true]) =
              ENNReal.ofReal ((↑m + β) / (↑k + ↑m + α + β)) *
                (betaPrefixAux α β hα hβ k (m + 1) (xs ++ [false]) +
                  betaPrefixAux α β hα hβ k (m + 1) (xs ++ [true])) := by
            simp [mul_add]
          _ =
              ENNReal.ofReal ((↑m + β) / (↑k + ↑m + α + β)) *
                betaPrefixAux α β hα hβ k (m + 1) xs := hmul
      · -- b = true
        have ih' :
            betaPrefixAux α β hα hβ (k + 1) m (xs ++ [false]) +
                betaPrefixAux α β hα hβ (k + 1) m (xs ++ [true]) =
              betaPrefixAux α β hα hβ (k + 1) m xs := by
          simpa using (ih (k := k + 1) (m := m))
        simp [betaPrefixAux, betaStepProb]
        have hmul :
            ENNReal.ofReal ((↑k + α) / (↑k + ↑m + α + β)) *
                (betaPrefixAux α β hα hβ (k + 1) m (xs ++ [false]) +
                  betaPrefixAux α β hα hβ (k + 1) m (xs ++ [true])) =
              ENNReal.ofReal ((↑k + α) / (↑k + ↑m + α + β)) *
                betaPrefixAux α β hα hβ (k + 1) m xs := by
          simpa using congrArg
            (fun t =>
              ENNReal.ofReal ((↑k + α) / (↑k + ↑m + α + β)) * t) ih'
        calc
          ENNReal.ofReal ((↑k + α) / (↑k + ↑m + α + β)) *
                betaPrefixAux α β hα hβ (k + 1) m (xs ++ [false]) +
              ENNReal.ofReal ((↑k + α) / (↑k + ↑m + α + β)) *
                betaPrefixAux α β hα hβ (k + 1) m (xs ++ [true]) =
              ENNReal.ofReal ((↑k + α) / (↑k + ↑m + α + β)) *
                (betaPrefixAux α β hα hβ (k + 1) m (xs ++ [false]) +
                  betaPrefixAux α β hα hβ (k + 1) m (xs ++ [true])) := by
            simp [mul_add]
          _ =
              ENNReal.ofReal ((↑k + α) / (↑k + ↑m + α + β)) *
                betaPrefixAux α β hα hβ (k + 1) m xs := hmul

/-- The Beta(α,β) sequential predictor as a `PrefixMeasure`. -/
noncomputable def betaPrefixMeasure (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : PrefixMeasure where
  toFun := fun x => betaPrefixAux α β hα hβ 0 0 x
  root_eq_one' := by simp [betaPrefixAux]
  additive' := by
    intro x
    -- Use the general auxiliary additivity lemma.
    simpa using
      (betaPrefixAux_additive (α := α) (β := β) (hα := hα) (hβ := hβ) (k := 0) (m := 0) (xs := x))

/-- Laplace/uniform prior: Beta(1,1). -/
noncomputable abbrev laplacePrefixMeasure : PrefixMeasure :=
  betaPrefixMeasure (α := 1) (β := 1) (by norm_num) (by norm_num)

/-- Jeffreys/KT prior: Beta(1/2, 1/2). -/
noncomputable abbrev jeffreysPrefixMeasure : PrefixMeasure :=
  betaPrefixMeasure (α := (1 / 2 : ℝ)) (β := (1 / 2 : ℝ)) (by norm_num) (by norm_num)

end Mettapedia.Logic.UniversalPrediction
