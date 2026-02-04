import Mettapedia.Computability.HutterComputability

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Finset.Interval
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Closure lemmas for Hutter-style lower semicomputability

`Mettapedia.Computability.HutterComputability` defines Hutter's notion of *lower semicomputability*
(`LowerSemicomputable`) for real-valued functions via **computable monotone dyadic
approximations**.

This file provides one key closure lemma used in the universal prediction layer:

* a **countable nonnegative sum** of *uniformly* lower-semicomputable functions is again
  lower-semicomputable.

The construction is the standard diagonal one:

* given a dyadic witness `a : (ℕ × α) → ℕ → ℕ` for `g : ℕ → α → ℝ`,
* define a witness for `x ↦ ∑' i, g i x` by
  `A x n := ∑ i < n, a (i, x) n`.

We prove convergence via Tannery's theorem (`tendsto_tsum_of_dominated_convergence`), viewing the
diagonal approximants as a dominated family of series.
-/

namespace Mettapedia.Computability.Hutter

open Filter
open scoped Classical BigOperators

variable {α : Type*} [Primcodable α]

/-! ## A computable “sum over range” helper on naturals -/

/-- Sum `f 0 + ... + f (n-1)` via primitive recursion. -/
def sumRange (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumRange f n + f n

lemma natRec_eq_sumRange (f : ℕ → ℕ) :
    (fun n => Nat.rec 0 (fun i acc => acc + f i) n) = sumRange f := by
  funext n
  induction n with
  | zero =>
      simp [sumRange]
  | succ n ih =>
      simp [sumRange, ih]

@[simp] lemma sumRange_zero (f : ℕ → ℕ) : sumRange f 0 = 0 := rfl

@[simp] lemma sumRange_succ (f : ℕ → ℕ) (n : ℕ) : sumRange f (n + 1) = sumRange f n + f n := rfl

lemma sumRange_eq_finset_sum (f : ℕ → ℕ) (n : ℕ) :
    sumRange f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero =>
      simp [sumRange]
  | succ n ih =>
      simp [sumRange, ih, Finset.sum_range_succ]

lemma dyadic_sumRange (f : ℕ → ℕ) (n : ℕ) :
    dyadic (sumRange f n) n = ∑ i ∈ Finset.range n, dyadic (f i) n := by
  -- Both sides are the same rational number with denominator `2^n`.
  rw [sumRange_eq_finset_sum (f := f) (n := n)]
  unfold dyadic
  -- `((∑ f i) : ℝ) / 2^n = ∑ ((f i : ℝ) / 2^n)`.
  -- Factor out the common `((2 : ℝ) ^ n)⁻¹`.
  simp [div_eq_mul_inv, Finset.sum_mul]

/-! ## Countable sum closure for `LowerSemicomputable` -/

namespace LowerSemicomputable

variable (g : ℕ → α → ℝ)

/-- If `g : ℕ → α → ℝ` is nonnegative and *uniformly* lower semicomputable, and for every `x`
the series `∑' i, g i x` is summable, then `x ↦ ∑' i, g i x` is lower semicomputable. -/
theorem tsum_of_nonneg
    (h0 : ∀ i x, 0 ≤ g i x)
    (hsum : ∀ x, Summable (fun i : ℕ => g i x))
    (hLSC : LowerSemicomputable (fun p : ℕ × α => g p.1 p.2)) :
    LowerSemicomputable (fun x : α => ∑' i : ℕ, g i x) := by
  classical
  rcases hLSC with ⟨a, ha_comp, ha_mono, ha_tendsto⟩
  -- Diagonal witness `A x n := ∑ i < n, a (i,x) n`.
  let A : α → ℕ → ℕ := fun x n => Nat.rec 0 (fun i acc => acc + a (i, x) n) n
  refine ⟨A, ?_, ?_, ?_⟩
  · -- Computability of `A`.
    -- Work with the uncurried function on `α × ℕ`.
    -- `A (x,n)` is computed by primitive recursion on `n`.
    let step : (α × ℕ) → ℕ × ℕ → ℕ :=
      fun p r => r.2 + a (r.1, p.1) p.2
    have hstep : Computable₂ step := by
      -- `step (x,n) (i,acc) = acc + a (i,x) n`.
      have hadd : Computable₂ ((· + ·) : ℕ → ℕ → ℕ) := (_root_.Primrec.nat_add).to_comp
      -- Uncurried `a` so we can compose it with projections.
      have ha_unc : Computable fun q : (ℕ × α) × ℕ => a q.1 q.2 := ha_comp
      have hAcc : Computable fun q : (α × ℕ) × (ℕ × ℕ) => q.2.2 :=
        (Computable.snd.comp Computable.snd)
      have hIx : Computable fun q : (α × ℕ) × (ℕ × ℕ) => (q.2.1, q.1.1) :=
        (Computable.pair (Computable.fst.comp Computable.snd) (Computable.fst.comp Computable.fst))
      have hN : Computable fun q : (α × ℕ) × (ℕ × ℕ) => q.1.2 :=
        (Computable.snd.comp Computable.fst)
      have ha_val : Computable fun q : (α × ℕ) × (ℕ × ℕ) => a (q.2.1, q.1.1) q.1.2 := by
        have hPair : Computable fun q : (α × ℕ) × (ℕ × ℕ) => ((q.2.1, q.1.1), q.1.2) :=
          (Computable.pair hIx hN)
        exact ha_unc.comp hPair
      exact (hadd.comp hAcc ha_val).to₂
    have hA_unc : Computable fun p : α × ℕ =>
        Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => step p (i, acc)) p.2 := by
      refine Computable.nat_rec (f := fun p : α × ℕ => p.2) (g := fun _ => (0 : ℕ))
        (h := step) (hf := Computable.snd) (hg := Computable.const 0) (hh := hstep)
    -- The curried function `A` is definitional equal to the uncurried recursion.
    simpa [A, step] using hA_unc.to₂
  · -- Monotonicity of the dyadic approximation sequence.
    intro x
    refine monotone_nat_of_le_succ ?_
    intro n
    have hEq_n :
        dyadic (A x n) n = ∑ i ∈ Finset.range n, dyadic (a (i, x) n) n := by
      -- Rewrite `A x n` to `sumRange` (so we can use `dyadic_sumRange`).
      have hA : A x n = sumRange (fun i => a (i, x) n) n := by
        -- Here `n` is *fixed*, so `fun i => a (i, x) n` is a constant function in the recursion.
        simpa [A] using congrArg (fun t => t n) (natRec_eq_sumRange (f := fun i => a (i, x) n))
      -- Avoid `simp` rewriting `sumRange_succ` before `dyadic_sumRange` can fire.
      simpa [hA] using (dyadic_sumRange (f := fun i => a (i, x) n) (n := n))
    have hEq_succ :
        dyadic (A x (n + 1)) (n + 1) =
          ∑ i ∈ Finset.range (n + 1), dyadic (a (i, x) (n + 1)) (n + 1) := by
      have hA : A x (n + 1) = sumRange (fun i => a (i, x) (n + 1)) (n + 1) := by
        simpa [A] using
          congrArg (fun t => t (n + 1)) (natRec_eq_sumRange (f := fun i => a (i, x) (n + 1)))
      -- Avoid `simp` rewriting `sumRange_succ` before `dyadic_sumRange` can fire.
      simpa [hA] using (dyadic_sumRange (f := fun i => a (i, x) (n + 1)) (n := n + 1))
    -- Compare the finite sums termwise.
    rw [hEq_n, hEq_succ]
    have hle_same :
        (∑ i ∈ Finset.range n, dyadic (a (i, x) n) n) ≤
          ∑ i ∈ Finset.range n, dyadic (a (i, x) (n + 1)) (n + 1) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have : i < n := by simpa [Finset.mem_range] using hi
      exact (ha_mono (i, x)) (Nat.le_succ n)
    have hnonneg_last : 0 ≤ dyadic (a (n, x) (n + 1)) (n + 1) := by
      unfold dyadic
      have : 0 ≤ ((a (n, x) (n + 1) : ℝ)) := by exact_mod_cast (Nat.zero_le _)
      have hpow : 0 < (2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
      exact div_nonneg this (le_of_lt hpow)
    -- Add the last term to extend from `range n` to `range (n+1)`.
    calc
      (∑ i ∈ Finset.range n, dyadic (a (i, x) n) n)
          ≤ ∑ i ∈ Finset.range n, dyadic (a (i, x) (n + 1)) (n + 1) := hle_same
      _ ≤ ∑ i ∈ Finset.range (n + 1), dyadic (a (i, x) (n + 1)) (n + 1) := by
            -- `∑_{i<n} t i ≤ ∑_{i<n} t i + t n = ∑_{i<n+1} t i`.
            have hsum_succ :
                (∑ i ∈ Finset.range n, dyadic (a (i, x) (n + 1)) (n + 1)) +
                    dyadic (a (n, x) (n + 1)) (n + 1) =
                  ∑ i ∈ Finset.range (n + 1), dyadic (a (i, x) (n + 1)) (n + 1) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                (Finset.sum_range_succ (fun i => dyadic (a (i, x) (n + 1)) (n + 1)) n).symm
            exact (le_trans (le_add_of_nonneg_right hnonneg_last) (le_of_eq hsum_succ))
  · -- Convergence to the infinite sum.
    intro x
    -- Define the diagonal approximant as a series with finite support.
    let f : ℕ → ℕ → ℝ :=
      fun n i => if i < n then dyadic (a (i, x) n) n else 0
    have hsum_eq (n : ℕ) : (∑' i : ℕ, f n i) = dyadic (A x n) n := by
      -- `f n i = 0` for `i ≥ n`, so `tsum` reduces to `Finset.range n`.
      have htsum :
          (∑' i : ℕ, f n i) = ∑ i ∈ Finset.range n, dyadic (a (i, x) n) n := by
        -- `tsum_eq_sum` wants the "outside the finset is 0" hypothesis.
        refine (tsum_eq_sum (s := Finset.range n) ?_).trans ?_
        · intro i hi
          have : ¬ i < n := by
            simpa [Finset.mem_range, not_lt] using hi
          simp [f, this]
        ·
          -- On `range n`, the guard `i < n` is always true.
          refine Finset.sum_congr rfl ?_
          intro i hi
          have : i < n := by simpa [Finset.mem_range] using hi
          simp [f, this]
      -- Rewrite the RHS via `dyadic_sumRange`.
      have hA :
          dyadic (A x n) n = ∑ i ∈ Finset.range n, dyadic (a (i, x) n) n := by
        have hA' : A x n = sumRange (fun i => a (i, x) n) n := by
          simpa [A] using congrArg (fun t => t n) (natRec_eq_sumRange (f := fun i => a (i, x) n))
        simp [hA', dyadic_sumRange]
      simpa [htsum] using hA.symm
    -- Apply Tannery's theorem (dominated convergence for series).
    have hab : ∀ i : ℕ, Tendsto (fun n => f n i) atTop (nhds (g i x)) := by
      intro i
      have ht : Tendsto (fun n => dyadic (a (i, x) n) n) atTop (nhds (g i x)) :=
        ha_tendsto (i, x)
      have hEq :
          (fun n => f n i) =ᶠ[atTop] fun n => dyadic (a (i, x) n) n := by
        refine (eventually_atTop.2 ⟨i + 1, ?_⟩)
        intro n hn
        have : i < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hn
        simp [f, this]
      exact Filter.Tendsto.congr' hEq.symm ht
    have h_bound : ∀ᶠ n in atTop, ∀ i : ℕ, ‖f n i‖ ≤ g i x := by
      refine Filter.Eventually.of_forall ?_
      intro n i
      have h_nonneg : 0 ≤ f n i := by
        by_cases h : i < n
        ·
          have hnum : 0 ≤ (a (i, x) n : ℝ) := by exact_mod_cast (Nat.zero_le _)
          have hden : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) _
          simpa [f, h, dyadic] using (div_nonneg hnum hden)
        · simp [f, h]
      have h_le : f n i ≤ g i x := by
        by_cases h : i < n
        · have hmono : Monotone (fun m => dyadic (a (i, x) m) m) := ha_mono (i, x)
          have htend : Tendsto (fun m => dyadic (a (i, x) m) m) atTop (nhds (g i x)) :=
            ha_tendsto (i, x)
          have hle' : dyadic (a (i, x) n) n ≤ g i x := hmono.ge_of_tendsto htend n
          simpa [f, h] using hle'
        · have : 0 ≤ g i x := h0 i x
          simpa [f, h] using this
      -- For nonnegative reals, `‖t‖ = t`.
      simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg] using h_le
    have hT :
        Tendsto (fun n => ∑' i : ℕ, f n i) atTop (nhds (∑' i : ℕ, g i x)) := by
      refine tendsto_tsum_of_dominated_convergence (h_sum := hsum x) ?_ ?_
      · intro i
        simpa using hab i
      · simpa using h_bound
    -- Replace `∑' i, f n i` by `dyadic (A x n) n`.
    have hEq' : (fun n => ∑' i : ℕ, f n i) = fun n => dyadic (A x n) n := by
      funext n
      exact hsum_eq n
    simpa [hEq'] using hT

end LowerSemicomputable

end Mettapedia.Computability.Hutter
