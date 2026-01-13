import Mathlib.Tactic.Ring
import Mettapedia.Logic.UniversalPrediction.FiniteHorizon

/-!
# Finite-horizon chain rule for prefix relative entropy (Hutter 2005, Chapter 3)

This file proves a finite-horizon “chain rule” decomposition for the prefix-level relative entropy

`Dₙ(μ‖ξ) = ∑_{x : 𝔹ⁿ} μ(x) log (μ(x)/ξ(x))`,

expressing `D_{n+1}` as `Dₙ` plus the expected one-step relative entropy of the conditional
next-bit predictions.

We work with `μ : PrefixMeasure` (a genuine probability measure on cylinders) and
`ξ : Semimeasure`. The chain rule is stated under a dominance hypothesis `Dominates ξ μ c`
with `c > 0`, which ensures the relevant log terms are well-behaved on the `μ`-support.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical BigOperators

namespace FiniteHorizon

/-! ## One-step conditionals (as real numbers) -/

/-- Real-valued conditional probability (via `ENNReal.toReal`) for a semimeasure. -/
def condProb (μ : Semimeasure) (x : BinString) (b : Bool) : ℝ :=
  (conditionalENN μ [b] x).toReal

/-- One-step (binary) relative entropy between conditionals `μ(·|x)` and `ξ(·|x)`.

This is the usual discrete formula
`∑_{b∈{0,1}} μ(b|x) log( μ(b|x) / ξ(b|x) )`.
-/
def stepRelEntropy (μ : PrefixMeasure) (ξ : Semimeasure) (x : BinString) : ℝ :=
  condProb μ.toSemimeasure x true * Real.log (condProb μ.toSemimeasure x true / condProb ξ x true) +
    condProb μ.toSemimeasure x false * Real.log (condProb μ.toSemimeasure x false / condProb ξ x false)

@[simp]
lemma prefixPMF_apply (μ : PrefixMeasure) (n : ℕ) (f : Fin n → Bool) :
    prefixPMF μ n f = μ (List.ofFn f) := rfl

/-! ## Helper lemma: `List.ofFn` for `Fin.snoc` -/

lemma ofFn_snoc {n : ℕ} (b : Bool) (g : Fin n → Bool) :
    List.ofFn (Fin.snoc g b) = List.ofFn g ++ [b] := by
  have hlist : List.ofFn (Fin.snoc g b) = (List.ofFn g).concat b := by
    simpa [List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last] using
      (List.ofFn_succ' (f := Fin.snoc g b))
  rw [hlist]
  simp [List.concat_eq_append]

/-- Finite-horizon chain rule (under dominance): `D_{n+1} = Dₙ + E[ stepRelEntropy ]`. -/
theorem relEntropy_succ_eq (μ : PrefixMeasure) (ξ : Semimeasure) {c : ENNReal}
    (hdom : Dominates ξ μ c) (hc0 : c ≠ 0) (n : ℕ) :
    relEntropy μ ξ (n + 1) =
      relEntropy μ ξ n + expectPrefix μ n (fun x => stepRelEntropy μ ξ x) := by
  classical
  -- Expand `relEntropy`/`expectPrefix` into explicit finite sums over `Fin n → Bool`,
  -- and rewrite `prefixPMF` evaluation to `μ (List.ofFn ·)`.
  simp only [FiniteHorizon.relEntropy, FiniteHorizon.expectPrefix, prefixPMF_apply]
  -- It suffices to prove the corresponding identity for the explicit sums.
  -- We rewrite the length-`n+1` sum using `Fin.snocEquiv` to split off the last bit.
  have hsplit :
      (∑ f : Fin (n + 1) → Bool,
            (μ (List.ofFn f)).toReal *
              Real.log ((μ (List.ofFn f)).toReal / (ξ (List.ofFn f)).toReal)) =
        ∑ g : Fin n → Bool,
          ∑ b : Bool,
            (μ (List.ofFn g ++ [b])).toReal *
              Real.log ((μ (List.ofFn g ++ [b])).toReal / (ξ (List.ofFn g ++ [b])).toReal) := by
    -- First, swap the indexing set to a product via `Fin.snocEquiv`.
    have hEquiv :
        (∑ p : Bool × (Fin n → Bool),
              (μ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => Bool) p))).toReal *
                Real.log
                  ((μ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => Bool) p))).toReal /
                    (ξ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => Bool) p))).toReal)) =
            ∑ f : Fin (n + 1) → Bool,
              (μ (List.ofFn f)).toReal *
                Real.log ((μ (List.ofFn f)).toReal / (ξ (List.ofFn f)).toReal) := by
      refine
        Fintype.sum_equiv (Fin.snocEquiv fun _ : Fin (n + 1) => Bool)
          (fun p =>
            (μ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => Bool) p))).toReal *
              Real.log
                ((μ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => Bool) p))).toReal /
                  (ξ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => Bool) p))).toReal))
          (fun f =>
            (μ (List.ofFn f)).toReal *
              Real.log ((μ (List.ofFn f)).toReal / (ξ (List.ofFn f)).toReal)) ?_
      intro p
      rfl
    -- Uncurry and rewrite `List.ofFn (Fin.snoc g b)` as `List.ofFn g ++ [b]`.
    calc
      (∑ f : Fin (n + 1) → Bool,
            (μ (List.ofFn f)).toReal *
              Real.log ((μ (List.ofFn f)).toReal / (ξ (List.ofFn f)).toReal))
          = ∑ p : Bool × (Fin n → Bool),
              (μ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => Bool) p))).toReal *
                Real.log
                  ((μ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => Bool) p))).toReal /
                    (ξ (List.ofFn ((Fin.snocEquiv fun _ : Fin (n + 1) => Bool) p))).toReal) := by
              simpa using hEquiv.symm
      _ = ∑ b : Bool, ∑ g : Fin n → Bool,
              (μ (List.ofFn (Fin.snoc g b))).toReal *
                Real.log ((μ (List.ofFn (Fin.snoc g b))).toReal / (ξ (List.ofFn (Fin.snoc g b))).toReal) := by
              simp [Fintype.sum_prod_type, Fin.snocEquiv]
      _ = ∑ b : Bool, ∑ g : Fin n → Bool,
              (μ (List.ofFn g ++ [b])).toReal *
                Real.log ((μ (List.ofFn g ++ [b])).toReal / (ξ (List.ofFn g ++ [b])).toReal) := by
              refine Fintype.sum_congr (fun b => ∑ g : Fin n → Bool, _)
                (fun b => ∑ g : Fin n → Bool, _) ?_
              intro b
              refine Fintype.sum_congr (fun g : Fin n → Bool => _)
                (fun g : Fin n → Bool => _) ?_
              intro g
              simp only [ofFn_snoc]
      _ = ∑ g : Fin n → Bool, ∑ b : Bool,
              (μ (List.ofFn g ++ [b])).toReal *
                Real.log ((μ (List.ofFn g ++ [b])).toReal / (ξ (List.ofFn g ++ [b])).toReal) := by
              -- Swap the order of summation (`Bool` ↔ prefix).
              simpa using
                (Finset.sum_comm (s := (Finset.univ : Finset Bool))
                  (t := (Finset.univ : Finset (Fin n → Bool)))
                  (f := fun b g =>
                    (μ (List.ofFn g ++ [b])).toReal *
                      Real.log ((μ (List.ofFn g ++ [b])).toReal / (ξ (List.ofFn g ++ [b])).toReal)))
  -- Now apply the per-prefix (inner Bool-sum) chain rule and sum over prefixes.
  -- For each prefix `x`, split the contribution over `b=false/true`.
  have hinner :
      ∀ g : Fin n → Bool,
        (∑ b : Bool,
              (μ (List.ofFn g ++ [b])).toReal *
                Real.log ((μ (List.ofFn g ++ [b])).toReal / (ξ (List.ofFn g ++ [b])).toReal)) =
          (μ (List.ofFn g)).toReal * Real.log ((μ (List.ofFn g)).toReal / (ξ (List.ofFn g)).toReal) +
            (μ (List.ofFn g)).toReal * stepRelEntropy μ ξ (List.ofFn g) := by
    intro g
    let x : BinString := List.ofFn g
    -- If `μ(x)=0`, all contributions are `0`.
    by_cases hx0 : μ x = 0
    · have hx0_false : μ (x ++ [false]) = 0 := by
        have hle : μ (x ++ [false]) ≤ μ x := by
          simpa using (μ.toSemimeasure.mono x false)
        have hle0 : μ (x ++ [false]) ≤ 0 := by simpa [hx0] using hle
        exact le_antisymm hle0 (by simp)
      have hx0_true : μ (x ++ [true]) = 0 := by
        have hle : μ (x ++ [true]) ≤ μ x := by
          simpa using (μ.toSemimeasure.mono x true)
        have hle0 : μ (x ++ [true]) ≤ 0 := by simpa [hx0] using hle
        exact le_antisymm hle0 (by simp)
      -- Everything is zero by simplification.
      simp [x, hx0, hx0_false, hx0_true, FiniteHorizon.stepRelEntropy, FiniteHorizon.condProb]
    · -- Otherwise, we use a per-branch log-ratio decomposition.
      have hξx0 : ξ x ≠ 0 := by
        intro hξx0
        have : μ x = 0 := Dominates.eq_zero_of_eq_zero (h := hdom) hc0 x hξx0
        exact hx0 this
      have hμxTop : μ x ≠ (⊤ : ENNReal) := by
        simpa using (semimeasure_ne_top μ.toSemimeasure x)
      have hξxTop : ξ x ≠ (⊤ : ENNReal) := semimeasure_ne_top ξ x
      have hμxReal0 : (μ x).toReal ≠ 0 := (ne_of_gt (ENNReal.toReal_pos hx0 hμxTop))
      have hξxReal0 : (ξ x).toReal ≠ 0 := (ne_of_gt (ENNReal.toReal_pos hξx0 hξxTop))

      -- Helper: `μ(x0)+μ(x1)=μ(x)` at the `toReal` level.
      have hsumμ :
          (μ (x ++ [false])).toReal + (μ (x ++ [true])).toReal = (μ x).toReal := by
        have hfalseTop : μ (x ++ [false]) ≠ (⊤ : ENNReal) := by
          simpa using (semimeasure_ne_top μ.toSemimeasure (x ++ [false]))
        have htrueTop : μ (x ++ [true]) ≠ (⊤ : ENNReal) := by
          simpa using (semimeasure_ne_top μ.toSemimeasure (x ++ [true]))
        have htoRealAdd :
            (μ (x ++ [false]) + μ (x ++ [true])).toReal =
              (μ (x ++ [false])).toReal + (μ (x ++ [true])).toReal := by
          simpa using (ENNReal.toReal_add hfalseTop htrueTop)
        have hadd : μ (x ++ [false]) + μ (x ++ [true]) = μ x := by
          simpa using (μ.additive' x)
        -- Reorder to match the goal.
        have : (μ (x ++ [false]) + μ (x ++ [true])).toReal = (μ x).toReal := by simp [hadd]
        simpa [x] using (htoRealAdd.symm.trans this)

      -- Helper: `μ(x) * μ(b|x) = μ(xb)` at the `toReal` level.
      have hmass_cond : ∀ b : Bool, (μ x).toReal * condProb μ.toSemimeasure x b = (μ (x ++ [b])).toReal := by
        intro b
        -- If `μ(x)=0` this is trivial, but we are in the `μ(x)≠0` branch.
        have hcond :
            condProb μ.toSemimeasure x b =
              (μ (x ++ [b])).toReal / (μ x).toReal := by
          simp [FiniteHorizon.condProb, conditionalENN]
        -- Use `mul_div_cancel₀` on reals.
        rw [hcond, mul_div_cancel₀ (a := (μ (x ++ [b])).toReal) (b := (μ x).toReal) hμxReal0]

      -- Per-branch log decomposition: if `μ(xb) ≠ 0`, then
      -- `log(μ(xb)/ξ(xb)) = log(μ(x)/ξ(x)) + log(μ(b|x)/ξ(b|x))`.
      have hbranch :
          ∀ b : Bool,
            (μ (x ++ [b])).toReal *
                Real.log ((μ (x ++ [b])).toReal / (ξ (x ++ [b])).toReal) =
              (μ (x ++ [b])).toReal * Real.log ((μ x).toReal / (ξ x).toReal) +
                (μ (x ++ [b])).toReal *
                  Real.log (condProb μ.toSemimeasure x b / condProb ξ x b) := by
        intro b
        by_cases hxb0 : μ (x ++ [b]) = 0
        · simp [hxb0]
        · have hξxb0 : ξ (x ++ [b]) ≠ 0 := by
            intro hξxb0
            have : μ (x ++ [b]) = 0 := Dominates.eq_zero_of_eq_zero (h := hdom) hc0 (x ++ [b]) hξxb0
            exact hxb0 this
          have hμxbTop : μ (x ++ [b]) ≠ (⊤ : ENNReal) := by
            simpa using (semimeasure_ne_top μ.toSemimeasure (x ++ [b]))
          have hξxbTop : ξ (x ++ [b]) ≠ (⊤ : ENNReal) := semimeasure_ne_top ξ (x ++ [b])
          have hμxbReal0 : (μ (x ++ [b])).toReal ≠ 0 :=
            ne_of_gt (ENNReal.toReal_pos hxb0 hμxbTop)
          have hξxbReal0 : (ξ (x ++ [b])).toReal ≠ 0 :=
            ne_of_gt (ENNReal.toReal_pos hξxb0 hξxbTop)
          have hcondμ :
              condProb μ.toSemimeasure x b = (μ (x ++ [b])).toReal / (μ x).toReal := by
            simp [FiniteHorizon.condProb, conditionalENN]
          have hcondξ :
              condProb ξ x b = (ξ (x ++ [b])).toReal / (ξ x).toReal := by
            simp [FiniteHorizon.condProb, conditionalENN]
          -- Work in reals with `a = μ(xb)`, `A = μ(x)`, `b' = ξ(xb)`, `B = ξ(x)`.
          set a : ℝ := (μ (x ++ [b])).toReal
          set A : ℝ := (μ x).toReal
          set b' : ℝ := (ξ (x ++ [b])).toReal
          set B : ℝ := (ξ x).toReal
          have ha0 : a ≠ 0 := by simpa [a] using hμxbReal0
          have hA0 : A ≠ 0 := by simpa [A] using hμxReal0
          have hb0 : b' ≠ 0 := by simpa [b'] using hξxbReal0
          have hB0 : B ≠ 0 := by simpa [B] using hξxReal0
          have hlog :
              Real.log (a / b') =
                Real.log (A / B) + Real.log ((a / A) / (b' / B)) := by
            -- Expand all logs via `log_div` and simplify.
            have h1 : Real.log (a / b') = Real.log a - Real.log b' := by
              simpa using (Real.log_div ha0 hb0)
            have h2 : Real.log (A / B) = Real.log A - Real.log B := by
              simpa using (Real.log_div hA0 hB0)
            have h3 : Real.log ((a / A) / (b' / B)) = Real.log (a / A) - Real.log (b' / B) := by
              have haA0 : a / A ≠ 0 := by
                exact div_ne_zero ha0 hA0
              have hbB0 : b' / B ≠ 0 := by
                exact div_ne_zero hb0 hB0
              simpa using (Real.log_div haA0 hbB0)
            have h4 : Real.log (a / A) = Real.log a - Real.log A := by
              simpa using (Real.log_div ha0 hA0)
            have h5 : Real.log (b' / B) = Real.log b' - Real.log B := by
              simpa using (Real.log_div hb0 hB0)
            calc
              Real.log (a / b')
                  = Real.log a - Real.log b' := h1
              _ = (Real.log A - Real.log B) + ((Real.log a - Real.log A) - (Real.log b' - Real.log B)) := by
                    ring
              _ = (Real.log A - Real.log B) + (Real.log (a / A) - Real.log (b' / B)) := by
                    simp [h4, h5]
              _ = Real.log (A / B) + Real.log ((a / A) / (b' / B)) := by
                    simp [h2, h3, sub_eq_add_neg, add_assoc, add_left_comm]
          -- Multiply the log identity by `a` and rewrite the conditionals.
          have hlog' :
              a * Real.log (a / b') =
                a * Real.log (A / B) + a * Real.log ((a / A) / (b' / B)) := by
            calc
              a * Real.log (a / b')
                  = a * (Real.log (A / B) + Real.log ((a / A) / (b' / B))) := by simp [hlog]
              _ = a * Real.log (A / B) + a * Real.log ((a / A) / (b' / B)) := by
                    simp [mul_add]
          -- Turn back into the original notation.
          have : (μ (x ++ [b])).toReal * Real.log ((μ (x ++ [b])).toReal / (ξ (x ++ [b])).toReal) =
                (μ (x ++ [b])).toReal * Real.log ((μ x).toReal / (ξ x).toReal) +
                  (μ (x ++ [b])).toReal * Real.log (condProb μ.toSemimeasure x b / condProb ξ x b) := by
            -- `simp` will rewrite `condProb` using `hcondμ/hcondξ`.
            have hcondRatio :
                (condProb μ.toSemimeasure x b / condProb ξ x b) =
                  ((a / A) / (b' / B)) := by
              simp [FiniteHorizon.condProb, conditionalENN, a, A, b', B]
            -- Now rewrite using `hlog'`.
            simpa [a, A, b', B, hcondRatio] using hlog'
          exact this

      -- Assemble the Bool-sum, first rewriting it as `true + false`.
      have hBool :
          (∑ b : Bool,
                (μ (x ++ [b])).toReal *
                  Real.log ((μ (x ++ [b])).toReal / (ξ (x ++ [b])).toReal)) =
            (μ (x ++ [true])).toReal *
                Real.log ((μ (x ++ [true])).toReal / (ξ (x ++ [true])).toReal) +
              (μ (x ++ [false])).toReal *
                Real.log ((μ (x ++ [false])).toReal / (ξ (x ++ [false])).toReal) := by
        simp

      -- Use the per-branch decomposition and regroup.
      -- `Fintype.sum_bool` gives the `true + false` ordering, so we follow it.
      rw [hBool]
      have ht := hbranch true
      have hf := hbranch false
      -- Rewrite and collect the `log(μ(x)/ξ(x))` terms using `μ(x0)+μ(x1)=μ(x)`.
      -- Also rewrite the conditional part as `μ(x) * stepRelEntropy`.
      have hcondPart :
          (μ (x ++ [true])).toReal * Real.log (condProb μ.toSemimeasure x true / condProb ξ x true) +
              (μ (x ++ [false])).toReal * Real.log (condProb μ.toSemimeasure x false / condProb ξ x false) =
            (μ x).toReal * stepRelEntropy μ ξ x := by
        unfold stepRelEntropy
        -- Expand and use `μ(x) * μ(b|x) = μ(xb)`.
        have ht' : (μ x).toReal * condProb μ.toSemimeasure x true = (μ (x ++ [true])).toReal :=
          hmass_cond true
        have hf' : (μ x).toReal * condProb μ.toSemimeasure x false = (μ (x ++ [false])).toReal :=
          hmass_cond false
        -- Reassociate `μ(x) * (p * log(..))` as `(μ(x) * p) * log(..)` and rewrite via `ht'`/`hf'`.
        calc
          (μ (x ++ [true])).toReal * Real.log (condProb μ.toSemimeasure x true / condProb ξ x true) +
              (μ (x ++ [false])).toReal * Real.log (condProb μ.toSemimeasure x false / condProb ξ x false)
              =
              ((μ x).toReal * condProb μ.toSemimeasure x true) *
                  Real.log (condProb μ.toSemimeasure x true / condProb ξ x true) +
                ((μ x).toReal * condProb μ.toSemimeasure x false) *
                  Real.log (condProb μ.toSemimeasure x false / condProb ξ x false) := by
                simp [ht', hf']
          _ =
              (μ x).toReal *
                  (condProb μ.toSemimeasure x true *
                      Real.log (condProb μ.toSemimeasure x true / condProb ξ x true)) +
                (μ x).toReal *
                  (condProb μ.toSemimeasure x false *
                      Real.log (condProb μ.toSemimeasure x false / condProb ξ x false)) := by
                ring
          _ =
              (μ x).toReal *
                (condProb μ.toSemimeasure x true * Real.log (condProb μ.toSemimeasure x true / condProb ξ x true) +
                  condProb μ.toSemimeasure x false *
                    Real.log (condProb μ.toSemimeasure x false / condProb ξ x false)) := by
                ring
          _ = (μ x).toReal * stepRelEntropy μ ξ x := by rfl

      -- Main regrouping.
      -- First, rewrite using `ht` and `hf`.
      -- Then `simp` handles the algebraic re-association.
      -- Finally, apply `hsumμ` for the coefficient sum.
      calc
        (μ (x ++ [true])).toReal * Real.log ((μ (x ++ [true])).toReal / (ξ (x ++ [true])).toReal) +
            (μ (x ++ [false])).toReal *
              Real.log ((μ (x ++ [false])).toReal / (ξ (x ++ [false])).toReal)
            =
          ((μ (x ++ [true])).toReal * Real.log ((μ x).toReal / (ξ x).toReal) +
              (μ (x ++ [true])).toReal * Real.log (condProb μ.toSemimeasure x true / condProb ξ x true)) +
            ((μ (x ++ [false])).toReal * Real.log ((μ x).toReal / (ξ x).toReal) +
              (μ (x ++ [false])).toReal * Real.log (condProb μ.toSemimeasure x false / condProb ξ x false)) := by
              simp [ht, hf, add_assoc]
        _ =
          ((μ (x ++ [true])).toReal + (μ (x ++ [false])).toReal) * Real.log ((μ x).toReal / (ξ x).toReal) +
            ((μ (x ++ [true])).toReal * Real.log (condProb μ.toSemimeasure x true / condProb ξ x true) +
              (μ (x ++ [false])).toReal * Real.log (condProb μ.toSemimeasure x false / condProb ξ x false)) := by
              ring
        _ = (μ x).toReal * Real.log ((μ x).toReal / (ξ x).toReal) +
              (μ x).toReal * stepRelEntropy μ ξ x := by
              -- Use `μ(x0)+μ(x1)=μ(x)` and the conditional-part lemma.
              -- Note: `hsumμ` is for `false + true`; we use commutativity to match.
              have hsumμ' :
                  (μ (x ++ [true])).toReal + (μ (x ++ [false])).toReal = (μ x).toReal := by
                simpa [add_comm] using hsumμ
              simp [hsumμ', hcondPart, add_comm]

  -- Finish by combining `hsplit` and summing `hinner` over `g`.
  -- The dominance chain rule is an equality of the unfolded sums, hence of `relEntropy`.
  -- `simp` at the start already reduced to this goal.
  -- Now we use `hsplit` and then `Fintype.sum_congr` with `hinner`.
  calc
    (∑ f : Fin (n + 1) → Bool,
          (μ (List.ofFn f)).toReal *
            Real.log ((μ (List.ofFn f)).toReal / (ξ (List.ofFn f)).toReal))
        =
      ∑ g : Fin n → Bool,
        ∑ b : Bool,
          (μ (List.ofFn g ++ [b])).toReal *
            Real.log ((μ (List.ofFn g ++ [b])).toReal / (ξ (List.ofFn g ++ [b])).toReal) := hsplit
    _ =
      ∑ g : Fin n → Bool,
        ((μ (List.ofFn g)).toReal * Real.log ((μ (List.ofFn g)).toReal / (ξ (List.ofFn g)).toReal) +
          (μ (List.ofFn g)).toReal * stepRelEntropy μ ξ (List.ofFn g)) := by
        refine Fintype.sum_congr _ _ ?_
        intro g
        simpa using hinner g
    _ =
        (∑ g : Fin n → Bool, (μ (List.ofFn g)).toReal * Real.log ((μ (List.ofFn g)).toReal / (ξ (List.ofFn g)).toReal)) +
          (∑ g : Fin n → Bool, (μ (List.ofFn g)).toReal * stepRelEntropy μ ξ (List.ofFn g)) := by
        -- Distribute the sum over `+`.
        -- (This is a `Finset` sum over `Finset.univ` under the hood.)
        simpa using
          (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin n → Bool)))
            (f := fun g =>
              (μ (List.ofFn g)).toReal * Real.log ((μ (List.ofFn g)).toReal / (ξ (List.ofFn g)).toReal))
            (g := fun g => (μ (List.ofFn g)).toReal * stepRelEntropy μ ξ (List.ofFn g)))

end FiniteHorizon

end Mettapedia.Logic.UniversalPrediction
