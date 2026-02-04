import Mettapedia.Computability.HutterComputability

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Lower semicomputability of rational-valued functions (Hutter, Chapter 2)

Hutter's `LowerSemicomputable` predicate is phrased in terms of **computable monotone dyadic
approximations** `a x n / 2^n`.

This file provides a small but extremely useful bridge lemma:

* if a real-valued function is given *exactly* as a ratio of natural numbers `num x / den x`,
  with `den x > 0` and `num, den` computable,
  then the function is `LowerSemicomputable`.

The witness is the standard floor approximation:

`a x n := (num x * 2^n) / den x`  (natural-number division).

Then `dyadic (a x n) n` is an increasing sequence converging to `(num x)/(den x)`.
-/

namespace Mettapedia.Computability.Hutter

open Filter
open scoped Classical

variable {α : Type*} [Primcodable α]

namespace LowerSemicomputable

/-- Floor-based dyadic approximant for the rational `m / d` (with `d > 0`). -/
def natRatioApprox (m d n : ℕ) : ℕ :=
  (m * 2 ^ n) / d

@[simp] lemma natRatioApprox_zero (m d : ℕ) : natRatioApprox m d 0 = m / d := by
  simp [natRatioApprox]

private lemma natRatioApprox_mul_le (m d n : ℕ) :
    natRatioApprox m d n * d ≤ m * 2 ^ n := by
  -- `(a / d) * d ≤ a`.
  simpa [natRatioApprox, Nat.mul_assoc] using Nat.div_mul_le_self (m * 2 ^ n) d

private lemma natRatioApprox_lt_mul_succ (m d n : ℕ) (hd : 0 < d) :
    m * 2 ^ n < (natRatioApprox m d n + 1) * d := by
  -- `a < (a/d + 1) * d` for `d > 0`.
  -- This is `a / d < a / d + 1`, rewritten via `Nat.div_lt_iff_lt_mul`.
  have hlt : (m * 2 ^ n) / d < (m * 2 ^ n) / d + 1 := Nat.lt_succ_self _
  -- Unfold `natRatioApprox` to match the goal.
  simpa [natRatioApprox, Nat.mul_assoc] using (Nat.div_lt_iff_lt_mul hd).1 hlt

private lemma natRatioApprox_two_mul_le_succ (m d n : ℕ) (hd : 0 < d) :
    natRatioApprox m d n * 2 ≤ natRatioApprox m d (n + 1) := by
  -- Let `qₙ = ⌊m*2^n / d⌋`. Then `2*qₙ*d ≤ m*2^(n+1)`, so `2*qₙ ≤ qₙ₊₁`.
  have hqd : natRatioApprox m d n * d ≤ m * 2 ^ n := natRatioApprox_mul_le m d n
  have hqd' : (natRatioApprox m d n * 2) * d ≤ m * 2 ^ (n + 1) := by
    -- Multiply the inequality `qₙ*d ≤ m*2^n` by 2.
    have : (natRatioApprox m d n * d) * 2 ≤ (m * 2 ^ n) * 2 :=
      Nat.mul_le_mul_right 2 hqd
    -- Rewrite `* 2` as `2 *` and fold the RHS into `2^(n+1)`.
    -- We use associativity/commutativity on `ℕ`.
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.pow_succ] using this
  -- Use `Nat.le_div_iff_mul_le` to conclude.
  exact (Nat.le_div_iff_mul_le hd).2 hqd'

private lemma monotone_dyadic_natRatioApprox (m d : ℕ) (hd : 0 < d) :
    Monotone (fun n : ℕ => dyadic (natRatioApprox m d n) n) := by
  -- It is enough to show `f n ≤ f (n+1)` for all `n`.
  refine monotone_nat_of_le_succ ?_
  intro n
  -- `qₙ/2^n ≤ qₙ₊₁/2^(n+1)` is equivalent to `2*qₙ ≤ qₙ₊₁`.
  have h2 : natRatioApprox m d n * 2 ≤ natRatioApprox m d (n + 1) :=
    natRatioApprox_two_mul_le_succ m d n hd
  -- Convert to reals and divide by the positive denominator `2^(n+1)`.
  unfold dyadic
  have hcast : (natRatioApprox m d n * 2 : ℝ) ≤ natRatioApprox m d (n + 1) := by
    exact_mod_cast h2
  have hden : 0 < (2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
  have hdiv :
      ((natRatioApprox m d n * 2 : ℝ) / (2 : ℝ) ^ (n + 1)) ≤
        ((natRatioApprox m d (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)) :=
    div_le_div_of_nonneg_right hcast (le_of_lt hden)
  -- Rewrite `(q*2)/2^(n+1)` as `q/2^n` using `pow_succ`.
  have hrew :
      ((natRatioApprox m d n : ℝ) / (2 : ℝ) ^ n) =
        ((natRatioApprox m d n * 2 : ℝ) / (2 : ℝ) ^ (n + 1)) := by
    -- `q/2^n = (q*2)/(2^n*2)`.
    have h2ne0 : (2 : ℝ) ≠ 0 := by norm_num
    -- `field_simp` is overkill; `simp` handles this cancellation.
    simp [pow_succ, div_eq_mul_inv, h2ne0, mul_assoc, mul_left_comm, mul_comm]
  simpa [hrew] using hdiv

private lemma abs_sub_natRatioApprox_le (m d n : ℕ) (hd : 0 < d) :
    |dyadic (natRatioApprox m d n) n - (m : ℝ) / (d : ℝ)| ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
  -- Use the standard sandwich: `q/2^n ≤ m/d < (q+1)/2^n`.
  set q : ℕ := natRatioApprox m d n
  have hq_mul_le : q * d ≤ m * 2 ^ n := by
    simpa [q] using natRatioApprox_mul_le m d n
  have hq_mul_lt : m * 2 ^ n < (q + 1) * d := by
    simpa [q] using natRatioApprox_lt_mul_succ m d n hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hd'
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hpow0 : (2 : ℝ) ^ n ≠ 0 := ne_of_gt hpow
  -- Lower bound: `q/2^n ≤ m/d`.
  have hle : (q : ℝ) / (2 : ℝ) ^ n ≤ (m : ℝ) / (d : ℝ) := by
    have hq' : (q : ℝ) * (d : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ n := by exact_mod_cast hq_mul_le
    -- First divide by `d`, then by `2^n`.
    have hqd : (q : ℝ) ≤ ((m : ℝ) * (2 : ℝ) ^ n) / (d : ℝ) := by
      -- `q ≤ (m*2^n)/d ↔ q*d ≤ m*2^n` since `d > 0`.
      exact (le_div_iff₀ hd').2 hq'
    have hqdn :
        (q : ℝ) / (2 : ℝ) ^ n ≤ (((m : ℝ) * (2 : ℝ) ^ n) / (d : ℝ)) / (2 : ℝ) ^ n :=
      div_le_div_of_nonneg_right hqd (le_of_lt hpow)
    -- Simplify the RHS: `((m*2^n)/d)/2^n = m/d`.
    have hpow0' : (2 : ℝ) ^ n ≠ 0 := hpow0
    -- Rewrite `(a/d)/c = a/(d*c)` and cancel the common factor `2^n`.
    have hcancel :
        (((m : ℝ) * (2 : ℝ) ^ n) / (d : ℝ)) / (2 : ℝ) ^ n = (m : ℝ) / (d : ℝ) := by
      -- `(m*2^n)/d/2^n = (m*2^n)/(d*2^n) = m/d`.
      calc
        (((m : ℝ) * (2 : ℝ) ^ n) / (d : ℝ)) / (2 : ℝ) ^ n
            = ((m : ℝ) * (2 : ℝ) ^ n) / ((d : ℝ) * (2 : ℝ) ^ n) := by
                simp [div_div]
        _ = (m : ℝ) / (d : ℝ) := by
                -- Cancel `(2^n)` on numerator/denominator.
                simpa using
                  (mul_div_mul_right (a := (m : ℝ)) (b := (d : ℝ)) (c := (2 : ℝ) ^ n) hpow0)
    simpa [hcancel] using hqdn
  -- Upper bound: `m/d < (q+1)/2^n`.
  have hlt : (m : ℝ) / (d : ℝ) < ((q + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
    have hq' : (m : ℝ) * (2 : ℝ) ^ n < ((q + 1 : ℕ) : ℝ) * (d : ℝ) := by exact_mod_cast hq_mul_lt
    -- First divide by `d`, then by `2^n`.
    have hqd : ((m : ℝ) * (2 : ℝ) ^ n) / (d : ℝ) < ((q + 1 : ℕ) : ℝ) := by
      -- `a/d < b ↔ a < b*d` since `d > 0`.
      exact (div_lt_iff₀ hd').2 hq'
    have hqdn :
        (((m : ℝ) * (2 : ℝ) ^ n) / (d : ℝ)) / (2 : ℝ) ^ n < ((q + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n :=
      div_lt_div_of_pos_right hqd hpow
    have hpow0' : (2 : ℝ) ^ n ≠ 0 := hpow0
    have hcancel :
        (((m : ℝ) * (2 : ℝ) ^ n) / (d : ℝ)) / (2 : ℝ) ^ n = (m : ℝ) / (d : ℝ) := by
      calc
        (((m : ℝ) * (2 : ℝ) ^ n) / (d : ℝ)) / (2 : ℝ) ^ n
            = ((m : ℝ) * (2 : ℝ) ^ n) / ((d : ℝ) * (2 : ℝ) ^ n) := by
                simp [div_div]
        _ = (m : ℝ) / (d : ℝ) := by
                simpa using
                  (mul_div_mul_right (a := (m : ℝ)) (b := (d : ℝ)) (c := (2 : ℝ) ^ n) hpow0)
    simpa [hcancel] using hqdn
  -- Convert to the bound on the absolute error.
  have herr : (m : ℝ) / (d : ℝ) - (q : ℝ) / (2 : ℝ) ^ n ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
    -- From `m/d < (q+1)/2^n` we get `m/d - q/2^n < 1/2^n`.
    have : (m : ℝ) / (d : ℝ) - (q : ℝ) / (2 : ℝ) ^ n <
        ((q + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n - (q : ℝ) / (2 : ℝ) ^ n :=
      sub_lt_sub_right hlt ((q : ℝ) / (2 : ℝ) ^ n)
    -- RHS simplifies to `1/2^n`.
    have hrhs :
        ((q + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n - (q : ℝ) / (2 : ℝ) ^ n = (1 : ℝ) / (2 : ℝ) ^ n := by
      -- Rewrite `a/t - b/t` as `(a-b)/t`.
      rw [← sub_div]
      simp
    have hlt' : (m : ℝ) / (d : ℝ) - (q : ℝ) / (2 : ℝ) ^ n < (1 : ℝ) / (2 : ℝ) ^ n :=
      lt_of_lt_of_eq this hrhs
    exact le_of_lt hlt'
  have habs :
      |(q : ℝ) / (2 : ℝ) ^ n - (m : ℝ) / (d : ℝ)| = (m : ℝ) / (d : ℝ) - (q : ℝ) / (2 : ℝ) ^ n := by
    -- Since `(q/2^n) ≤ (m/d)`, the difference is nonpositive.
    have hnonpos : (q : ℝ) / (2 : ℝ) ^ n - (m : ℝ) / (d : ℝ) ≤ 0 := by linarith [hle]
    calc
      |(q : ℝ) / (2 : ℝ) ^ n - (m : ℝ) / (d : ℝ)| =
          -((q : ℝ) / (2 : ℝ) ^ n - (m : ℝ) / (d : ℝ)) := by
            simpa using (abs_of_nonpos hnonpos)
      _ = (m : ℝ) / (d : ℝ) - (q : ℝ) / (2 : ℝ) ^ n := by simp
  -- Replace `dyadic q n` with `q/2^n` and finish.
  simpa [dyadic, q, habs] using herr

private lemma tendsto_dyadic_natRatioApprox (m d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => dyadic (natRatioApprox m d n) n) atTop (nhds ((m : ℝ) / (d : ℝ))) := by
  have hbound :
      ∀ n : ℕ, ‖dyadic (natRatioApprox m d n) n - (m : ℝ) / (d : ℝ)‖ ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
    intro n
    simpa [Real.norm_eq_abs] using abs_sub_natRatioApprox_le m d n hd
  have hgeom : Tendsto (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ n) atTop (nhds (0 : ℝ)) := by
    have : (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ n) = fun n : ℕ => (1 / 2 : ℝ) ^ n := by
      funext n
      simp [div_eq_mul_inv]
    rw [this]
    refine tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_
    · norm_num
    · norm_num
  have hnorm :
      Tendsto (fun n : ℕ => ‖dyadic (natRatioApprox m d n) n - (m : ℝ) / (d : ℝ)‖) atTop (nhds (0 : ℝ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeom ?_ ?_
    · intro n; exact norm_nonneg _
    · intro n; exact hbound n
  simpa [tendsto_iff_norm_sub_tendsto_zero] using hnorm

/-- If `f x = (num x) / (den x)` with `den x > 0` and `num, den` computable, then `f` is lower
semicomputable (via floor dyadic approximants). -/
theorem of_natRatio (num den : α → ℕ)
    (hnum : Computable num) (hden : Computable den)
    (hden_pos : ∀ x, 0 < den x) :
    LowerSemicomputable (fun x : α => (num x : ℝ) / (den x : ℝ)) := by
  classical
  let a : α → ℕ → ℕ := fun x n => natRatioApprox (num x) (den x) n
  refine ⟨a, ?_, ?_, ?_⟩
  · -- Computability of `a`.
    let a_unc : α × ℕ → ℕ := fun p => natRatioApprox (num p.1) (den p.1) p.2
    have hmul : Computable₂ ((· * ·) : ℕ → ℕ → ℕ) := (_root_.Primrec.nat_mul).to_comp
    have hdiv : Computable₂ ((· / ·) : ℕ → ℕ → ℕ) := (_root_.Primrec.nat_div).to_comp
    have hpow2 : Computable fun n : ℕ => 2 ^ n := by
      have hstep : Computable₂ fun (_ : ℕ) (t : ℕ × ℕ) => t.2 * 2 := by
        simpa using (hmul.comp (Computable.snd.comp Computable.snd) (Computable.const 2)).to₂
      have hrec :
          Computable fun n : ℕ =>
            Nat.rec (motive := fun _ => ℕ) 1 (fun _ IH => IH * 2) n :=
        Computable.nat_rec (hf := (show Computable (fun n : ℕ => n) from Computable.id))
          (hg := Computable.const 1) (hh := hstep)
      refine hrec.of_eq ?_
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          simp [Nat.pow_succ, ih, Nat.mul_comm]
    have hnum_unc : Computable fun p : α × ℕ => num p.1 := hnum.comp Computable.fst
    have hden_unc : Computable fun p : α × ℕ => den p.1 := hden.comp Computable.fst
    have hpow_unc : Computable fun p : α × ℕ => 2 ^ p.2 := hpow2.comp Computable.snd
    have hmul_unc : Computable fun p : α × ℕ => num p.1 * (2 ^ p.2) :=
      (hmul.comp hnum_unc hpow_unc).to₂
    have ha_unc : Computable a_unc := by
      have hdiv_unc : Computable fun p : α × ℕ => (num p.1 * 2 ^ p.2) / den p.1 :=
        (hdiv.comp hmul_unc hden_unc).to₂
      simpa [a_unc, natRatioApprox] using hdiv_unc
    exact ha_unc.to₂
  · intro x
    simpa [a, natRatioApprox] using
      monotone_dyadic_natRatioApprox (m := num x) (d := den x) (hden_pos x)
  · intro x
    simpa [a, natRatioApprox] using
      tendsto_dyadic_natRatioApprox (m := num x) (d := den x) (hden_pos x)

end LowerSemicomputable

end Mettapedia.Computability.Hutter
