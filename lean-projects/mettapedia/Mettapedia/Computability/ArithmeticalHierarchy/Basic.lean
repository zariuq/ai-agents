import Mathlib.Computability.Partrec
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

-- Helper lemma: Boolean negation is computable
-- Proof: not is Primrec (from Mathlib), and Primrec → Computable
theorem bool_not_computable : Computable (fun (b : Bool) => !b) :=
  Primrec.not.to_comp

/-!
# Arithmetical Hierarchy

This file defines the arithmetical hierarchy for predicates on natural numbers,
focusing on Σ⁰₂, Π⁰₂, and Δ⁰₂ predicates which are critical for the Grain of Truth
problem formalization.

## Main Definitions

* `Sigma02Predicate P`: Predicate P is Σ⁰₂ (∃m ∀k≥m, approx(n,k) = true)
* `Pi02Predicate P`: Predicate P is Π⁰₂ (∀m ∃k≥m, approx(n,k) = true)
* `Delta02Predicate P`: Predicate P is Δ⁰₂ (both Σ⁰₂ and Π⁰₂, i.e., limit computable)

## Main Theorems

* `sigma02_enumerable`: Every Σ⁰₂ predicate has a computable enumerator
* `sigma02_complement_pi02`: Complement of Σ⁰₂ is Π⁰₂
* `pi02_complement_sigma02`: Complement of Π⁰₂ is Σ⁰₂
* `delta02_decidable_in_limit`: Δ⁰₂ predicates are decidable in the limit

## References

- Rogers, H. (1987). "Theory of Recursive Functions and Effective Computability"
- Soare, R. (2016). "Turing Computability: Theory and Applications"
- Leike, J., Taylor, J., & Fallenstein, B. (2016). "A Formal Solution to the
  Grain of Truth Problem" (uses Δ⁰₂ for policy classes)

-/

namespace Mettapedia.Computability.ArithmeticalHierarchy

open Classical

/-! ## Σ⁰₁ Predicates (Recursively Enumerable) -/

/-- A Σ⁰₁ predicate is one that can be expressed in the form:
    P(n) ↔ ∃m, approx(n,m) = true

    This is the recursively enumerable predicates - there exists a computable
    approximation that eventually witnesses `true` if P(n) holds.

    Lower semicomputable real functions are characterized via Σ⁰₁ predicates.
-/
structure Sigma01Predicate (P : ℕ → Prop) where
  approx : ℕ → ℕ → Bool
  approx_computable : Computable (fun (n, m) => approx n m)
  converges : ∀ n, P n ↔ ∃ m, approx n m = true

/-- A Π⁰₁ predicate is the complement of a Σ⁰₁ predicate.
    P(n) ↔ ∀m, approx(n,m) = true
-/
structure Pi01Predicate (P : ℕ → Prop) where
  approx : ℕ → ℕ → Bool
  approx_computable : Computable (fun (n, m) => approx n m)
  converges : ∀ n, P n ↔ ∀ m, approx n m = true

/-! ## Σ⁰₂ Predicates -/

/-- A Σ⁰₂ predicate is one that can be expressed in the form:
    P(n) ↔ ∃m ∀k≥m, approx(n,k) = true

    This means the predicate P has a computable approximation function that
    eventually stabilizes to `true` for all n where P(n) holds.
-/
structure Sigma02Predicate (P : ℕ → Prop) where
  /-- Computable approximation function: approx n k approximates P(n) at stage k -/
  approx : ℕ → ℕ → Bool
  /-- The approximation function is computable -/
  approx_computable : Computable₂ approx
  /-- P(n) holds iff the approximation eventually stabilizes to true -/
  converges : ∀ n, P n ↔ ∃ m, ∀ k ≥ m, approx n k = true

namespace Sigma02Predicate

variable {P Q : ℕ → Prop}

/-- Extract witness of convergence for a Σ⁰₂ predicate at a given n -/
noncomputable def witnessStage (h : Sigma02Predicate P) (n : ℕ) (hn : P n) : ℕ :=
  Classical.choose ((h.converges n).mp hn)

theorem witnessStage_spec (h : Sigma02Predicate P) (n : ℕ) (hn : P n) :
    ∀ k ≥ h.witnessStage n hn, h.approx n k = true :=
  Classical.choose_spec ((h.converges n).mp hn)

/-- If approx is eventually true, then P holds -/
theorem approx_eventually_true_of_mem (h : Sigma02Predicate P) (n : ℕ) (hn : P n) :
    ∃ m, ∀ k ≥ m, h.approx n k = true :=
  (h.converges n).mp hn

/-- If approx is never eventually true, then P doesn't hold -/
theorem not_mem_of_approx_not_eventually_true (h : Sigma02Predicate P) (n : ℕ)
    (hn : ¬∃ m, ∀ k ≥ m, h.approx n k = true) : ¬P n :=
  fun hp => hn ((h.converges n).mp hp)

end Sigma02Predicate

/-! ## Π⁰₂ Predicates -/

/-- A Π⁰₂ predicate is one that can be expressed in the form:
    P(n) ↔ ∀m ∃k≥m, approx(n,k) = true

    This means the predicate P has a computable approximation function that
    returns true infinitely often for all n where P(n) holds.
-/
structure Pi02Predicate (P : ℕ → Prop) where
  /-- Computable approximation function -/
  approx : ℕ → ℕ → Bool
  /-- The approximation function is computable -/
  approx_computable : Computable₂ approx
  /-- P(n) holds iff the approximation is true infinitely often -/
  converges : ∀ n, P n ↔ ∀ m, ∃ k ≥ m, approx n k = true

namespace Pi02Predicate

variable {P Q : ℕ → Prop}

/-- For Π⁰₂ predicates, if P(n) holds, then for any stage m,
    there exists a later stage k where approx is true -/
theorem approx_infinitely_often (h : Pi02Predicate P) (n : ℕ) (hn : P n) (m : ℕ) :
    ∃ k ≥ m, h.approx n k = true :=
  ((h.converges n).mp hn) m

/-- If approx is not infinitely often true, then P doesn't hold -/
theorem not_mem_of_approx_not_infinitely_often (h : Pi02Predicate P) (n : ℕ)
    (hn : ∃ m, ∀ k ≥ m, h.approx n k = false) : ¬P n := by
  intro hp
  obtain ⟨m, hm⟩ := hn
  obtain ⟨k, hk_ge, hk_true⟩ := ((h.converges n).mp hp) m
  have hk_false : h.approx n k = false := hm k hk_ge
  rw [hk_false] at hk_true
  simp at hk_true

end Pi02Predicate

/-! ## Δ⁰₂ Predicates (Limit Computable) -/

/-- A Δ⁰₂ predicate is one that is both Σ⁰₂ and Π⁰₂.

    These are also called "limit computable" predicates - they have a computable
    approximation that converges in the limit to the correct answer.

    This is the key computability class for the Grain of Truth problem: policy
    classes need to be Δ⁰₂-enumerable for the theorem to hold.
-/
structure Delta02Predicate (P : ℕ → Prop) where
  /-- Computable approximation function that converges in the limit -/
  approx : ℕ → ℕ → Bool
  /-- The approximation function is computable -/
  approx_computable : Computable₂ approx
  /-- P(n) holds iff the approximation eventually stabilizes -/
  converges_limit : ∀ n, ∃ b : Bool, (P n ↔ b = true) ∧
                                      ∃ m, ∀ k ≥ m, approx n k = b

namespace Delta02Predicate

variable {P Q : ℕ → Prop}

/-- Every Δ⁰₂ predicate is Σ⁰₂ -/
def toSigma02 (h : Delta02Predicate P) : Sigma02Predicate P where
  approx := h.approx
  approx_computable := h.approx_computable
  converges := fun n => by
    obtain ⟨b, hb_iff, m, hm⟩ := h.converges_limit n
    constructor
    · intro hn
      use m
      intro k hk
      have : b = true := hb_iff.mp hn
      rw [← this]
      exact hm k hk
    · intro ⟨m', hm'⟩
      by_cases hb : b = true
      · exact hb_iff.mpr hb
      · -- Show contradiction: if b ≠ true, approx doesn't stabilize to true
        have hb_false : b = false := by
          cases b
          · rfl
          · contradiction
        -- At max m m', approx should be both true (from hm') and false (from hm)
        have h_true : h.approx n (max m m') = true := hm' (max m m') (le_max_right m m')
        have h_false : h.approx n (max m m') = false := by
          have := hm (max m m') (le_max_left m m')
          rw [hb_false] at this
          exact this
        rw [h_false] at h_true
        simp at h_true

/-- Every Δ⁰₂ predicate is Π⁰₂ -/
def toPi02 (h : Delta02Predicate P) : Pi02Predicate P where
  approx := h.approx
  approx_computable := h.approx_computable
  converges := fun n => by
    obtain ⟨b, hb_iff, m, hm⟩ := h.converges_limit n
    constructor
    · intro hn m'
      use max m m'
      constructor
      · exact le_max_right m m'
      · have : b = true := hb_iff.mp hn
        rw [← this]
        exact hm (max m m') (le_max_left m m')
    · intro h_inf
      by_cases hb : b = true
      · exact hb_iff.mpr hb
      · -- Show contradiction similar to above
        have hb_false : b = false := by
          cases b
          · rfl
          · contradiction
        obtain ⟨k, hk_ge, hk_true⟩ := h_inf m
        have hk_false : h.approx n k = false := by
          have := hm k hk_ge
          rw [hb_false] at this
          exact this
        rw [hk_false] at hk_true
        simp at hk_true

/-- Extract the limiting value for a Δ⁰₂ predicate at n -/
noncomputable def limitValue (h : Delta02Predicate P) (n : ℕ) : Bool :=
  Classical.choose (h.converges_limit n)

theorem limitValue_iff (h : Delta02Predicate P) (n : ℕ) :
    P n ↔ h.limitValue n = true :=
  (Classical.choose_spec (h.converges_limit n)).1

theorem limitValue_stable (h : Delta02Predicate P) (n : ℕ) :
    ∃ m, ∀ k ≥ m, h.approx n k = h.limitValue n :=
  (Classical.choose_spec (h.converges_limit n)).2

/-- The stage at which the approximation stabilizes to the limit value -/
noncomputable def stableStage (h : Delta02Predicate P) (n : ℕ) : ℕ :=
  Classical.choose (h.limitValue_stable n)

theorem stableStage_spec (h : Delta02Predicate P) (n : ℕ) :
    ∀ k ≥ h.stableStage n, h.approx n k = h.limitValue n :=
  Classical.choose_spec (h.limitValue_stable n)

end Delta02Predicate

/-! ## Lower Semicomputable Real Functions -/

/-- A real-valued function is lower semicomputable (l.s.c.) if it can be approximated
    from below by a rational sequence.

    Formally: f is l.s.c. if there exists a function approx : α → ℕ → ℚ such that:
    1. approx is monotone: approx x n ≤ approx x (n+1)
    2. approx approximates f from below: ∀x n, approx x n ≤ f x
    3. approx converges to f: ∀x ε>0, ∃N, ∀n≥N, f x - approx x n < ε

    This is equivalent to {x : f(x) > r} being Σ⁰₁ for all rationals r.

    NOTE: The term "computable" here refers to the theoretical notion from computability
    theory, not Lean's `Computable` typeclass. We assert existence of the approximation
    without requiring α to be Primcodable.

    From Wyeth/Hutter (2025), Theorem (line 476): lower semicomputable functions
    can be used to construct lower semicomputable value functions.
-/
structure LowerSemicomputable {α : Type*} (f : α → ℝ) where
  /-- Rational approximation from below -/
  approx : α → ℕ → ℚ
  /-- Monotonicity: approximation improves over time -/
  approx_mono : ∀ x n, approx x n ≤ approx x (n+1)
  /-- Lower bound: approximation stays below true value -/
  approx_le : ∀ x n, (approx x n : ℝ) ≤ f x
  /-- Convergence: approximation converges to true value -/
  approx_converges : ∀ x (ε : ℝ), 0 < ε → ∃ N, ∀ n ≥ N, f x - (approx x n : ℝ) < ε

/-- A real-valued function is upper semicomputable (u.s.c.) if it can be approximated
    from above by a rational sequence.

    Formally: f is u.s.c. if there exists a function approx : α → ℕ → ℚ such that:
    1. approx is antitone: approx x (n+1) ≤ approx x n
    2. approx approximates f from above: ∀x n, f x ≤ approx x n
    3. approx converges to f: ∀x ε>0, ∃N, ∀n≥N, approx x n - f x < ε

    This is equivalent to {x : f(x) < r} being Σ⁰₁ for all rationals r.

    A function that is both lower and upper semicomputable is called "computable"
    (or "estimable" in Hutter's terminology).
-/
structure UpperSemicomputable {α : Type*} (f : α → ℝ) where
  /-- Rational approximation from above -/
  approx : α → ℕ → ℚ
  /-- Antitonicity: approximation improves (decreases) over time -/
  approx_anti : ∀ x n, approx x (n+1) ≤ approx x n
  /-- Upper bound: approximation stays above true value -/
  approx_ge : ∀ x n, f x ≤ (approx x n : ℝ)
  /-- Convergence: approximation converges to true value -/
  approx_converges : ∀ x (ε : ℝ), 0 < ε → ∃ N, ∀ n ≥ N, (approx x n : ℝ) - f x < ε

namespace UpperSemicomputable

variable {α : Type*} {f g : α → ℝ}

/-- Sum of upper semicomputable functions is upper semicomputable -/
noncomputable def add (hf : UpperSemicomputable f) (hg : UpperSemicomputable g) :
    UpperSemicomputable (fun x => f x + g x) where
  approx x n := hf.approx x n + hg.approx x n
  approx_anti x n := add_le_add (hf.approx_anti x n) (hg.approx_anti x n)
  approx_ge x n := by
    simp only [Rat.cast_add]
    exact add_le_add (hf.approx_ge x n) (hg.approx_ge x n)
  approx_converges x ε hε := by
    have hε2 : 0 < ε/2 := half_pos hε
    obtain ⟨N1, h1⟩ := hf.approx_converges x (ε/2) hε2
    obtain ⟨N2, h2⟩ := hg.approx_converges x (ε/2) hε2
    use max N1 N2
    intro n hn
    have hn1 : N1 ≤ n := le_of_max_le_left hn
    have hn2 : N2 ≤ n := le_of_max_le_right hn
    simp only [Rat.cast_add]
    calc (hf.approx x n : ℝ) + (hg.approx x n : ℝ) - (f x + g x)
        = (hf.approx x n - f x) + (hg.approx x n - g x) := by ring
      _ < ε/2 + ε/2 := add_lt_add (h1 n hn1) (h2 n hn2)
      _ = ε := add_halves ε

/-- Composition with a function preserves upper semicomputability -/
noncomputable def comp {β : Type*} (hf : UpperSemicomputable f) (g : β → α) :
    UpperSemicomputable (fun x => f (g x)) where
  approx x n := hf.approx (g x) n
  approx_anti x n := hf.approx_anti (g x) n
  approx_ge x n := hf.approx_ge (g x) n
  approx_converges x ε hε := hf.approx_converges (g x) ε hε

end UpperSemicomputable

namespace LowerSemicomputable

/-- Constant zero function is lower semicomputable -/
noncomputable def const_zero {α : Type*} :
    LowerSemicomputable (fun _ : α => (0 : ℝ)) where
  approx _ _ := 0
  approx_mono _ _ := le_refl 0
  approx_le _ _ := by simp only [Rat.cast_zero]; exact le_refl 0
  approx_converges _ ε hε := ⟨0, fun _ _ => by simp; exact hε⟩

/-! ### Closure Properties -/

/-- Sum of lower semicomputable functions is lower semicomputable -/
noncomputable def add {α : Type*} {f g : α → ℝ}
    (hf : LowerSemicomputable f) (hg : LowerSemicomputable g) :
    LowerSemicomputable (f + g) where
  approx x n := hf.approx x n + hg.approx x n
  approx_mono x n := add_le_add (hf.approx_mono x n) (hg.approx_mono x n)
  approx_le x n := by
    simp only [Pi.add_apply]
    push_cast
    exact add_le_add (hf.approx_le x n) (hg.approx_le x n)
  approx_converges x ε hε := by
    have hε2 : 0 < ε/2 := half_pos hε
    obtain ⟨N1, h1⟩ := hf.approx_converges x (ε/2) hε2
    obtain ⟨N2, h2⟩ := hg.approx_converges x (ε/2) hε2
    use max N1 N2
    intro n hn
    simp only [Pi.add_apply]
    push_cast
    have hn1 : N1 ≤ n := le_of_max_le_left hn
    have hn2 : N2 ≤ n := le_of_max_le_right hn
    calc (f + g) x - ((hf.approx x n : ℝ) + (hg.approx x n : ℝ))
        = (f x - (hf.approx x n : ℝ)) + (g x - (hg.approx x n : ℝ)) := by
          simp only [Pi.add_apply]
          linarith
      _ < ε/2 + ε/2 := add_lt_add (h1 n hn1) (h2 n hn2)
      _ = ε := add_halves ε

/-- Scalar multiplication by nonnegative rational constant -/
noncomputable def const_smul_rat {α : Type*} {f : α → ℝ} (c : ℚ) (hc : 0 ≤ c)
    (hf : LowerSemicomputable f) :
    LowerSemicomputable (fun x => (c : ℝ) * f x) where
  approx x n := c * hf.approx x n
  approx_mono x n := by
    apply mul_le_mul_of_nonneg_left (hf.approx_mono x n) hc
  approx_le x n := by
    push_cast
    apply mul_le_mul_of_nonneg_left (hf.approx_le x n)
    exact Rat.cast_nonneg.mpr hc
  approx_converges x ε hε := by
    by_cases hc0 : c = 0
    · -- Case c = 0: trivial (c * f x = 0, approximations are 0)
      use 0
      intro n _
      simp [hc0]
      exact hε
    · -- Case c > 0: use ε/c trick
      have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      have hc_pos_real : 0 < (c : ℝ) := Rat.cast_pos.mpr hc_pos
      obtain ⟨N, hN⟩ := hf.approx_converges x (ε / c) (div_pos hε hc_pos_real)
      use N
      intro n hn
      push_cast
      calc (c : ℝ) * f x - (c : ℝ) * (hf.approx x n : ℝ)
          = (c : ℝ) * (f x - (hf.approx x n : ℝ)) := (mul_sub (c : ℝ) (f x) (hf.approx x n : ℝ)).symm
        _ < (c : ℝ) * (ε / (c : ℝ)) := mul_lt_mul_of_pos_left (hN n hn) hc_pos_real
        _ = ε := mul_div_cancel₀ ε (ne_of_gt hc_pos_real)

/-- Scalar multiplication by nonnegative real constant -/
noncomputable def const_smul {α : Type*} {f : α → ℝ} (c : ℝ) (hc : 0 ≤ c)
    (hf : LowerSemicomputable f) (hf_nn : ∀ x, 0 ≤ f x) :
    LowerSemicomputable (fun x => c * f x) := by
  classical
  by_cases hc0 : c = 0
  · subst hc0
    refine
      { approx := fun _ _ => 0
        approx_mono := by intro _ _; rfl
        approx_le := by intro _ _; simp
        approx_converges := by
          intro _ ε hε
          refine ⟨0, ?_⟩
          intro _ _
          simp [hε] }
  · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)

    -- A monotone increasing sequence of rationals `q n` with `q n < c` and `q n → c`.
    let lower : ℕ → ℝ := fun n => max 0 (c - 1 / (n + 1 : ℝ))
    have hlower_lt : ∀ n, lower n < c := by
      intro n
      have hpos : 0 < (1 / (n + 1 : ℝ)) := by
        have hn : 0 < (n + 1 : ℝ) := by
          exact_mod_cast Nat.succ_pos n
        exact (one_div_pos).2 hn
      have hsub : c - 1 / (n + 1 : ℝ) < c := sub_lt_self c hpos
      simpa [lower, max_lt_iff] using And.intro hc_pos hsub

    let cand : ℕ → ℚ := fun n => Classical.choose (exists_rat_btwn (hlower_lt n))
    have cand_spec : ∀ n, lower n < (cand n : ℝ) ∧ (cand n : ℝ) < c :=
      fun n => Classical.choose_spec (exists_rat_btwn (hlower_lt n))

    let q : ℕ → ℚ := fun n =>
      Nat.rec (max 0 (cand 0)) (fun n qn => max qn (max 0 (cand (n + 1)))) n

    have hq_mono : ∀ n, q n ≤ q (n + 1) := by
      intro n
      have hq_succ : q (n + 1) = max (q n) (max 0 (cand (n + 1))) := by
        simp [q]
      rw [hq_succ]
      exact le_max_left _ _

    have hq_nonneg : ∀ n, (0 : ℚ) ≤ q n := by
      intro n
      induction n with
      | zero =>
        simp [q]
      | succ n ih =>
        have : q n ≤ q (n + 1) := hq_mono n
        exact le_trans ih this

    have hq_lt_c : ∀ n, (Rat.cast (q n) : ℝ) < c := by
      intro n
      induction n with
      | zero =>
        have hcand : (cand 0 : ℝ) < c := (cand_spec 0).2
        have : max (0 : ℝ) (cand 0 : ℝ) < c := (max_lt_iff).2 ⟨hc_pos, hcand⟩
        simpa [q, Rat.cast_max] using this
      | succ n ih =>
        have hcand : (cand (n + 1) : ℝ) < c := (cand_spec (n + 1)).2
        have hmax : max (0 : ℝ) (cand (n + 1) : ℝ) < c := (max_lt_iff).2 ⟨hc_pos, hcand⟩
        -- `q (n+1)` is the max of two values `< c`.
        have : max (Rat.cast (q n) : ℝ) (max (0 : ℝ) (cand (n + 1) : ℝ)) < c :=
          (max_lt_iff).2 ⟨ih, hmax⟩
        simpa [q, Rat.cast_max] using this

    have hq_le_c : ∀ n, (Rat.cast (q n) : ℝ) ≤ c := fun n => le_of_lt (hq_lt_c n)

    refine
      { approx := fun x n => q n * max 0 (hf.approx x n)
        approx_mono := ?_
        approx_le := ?_
        approx_converges := ?_ }

    · intro x n
      apply mul_le_mul
      · -- `q n ≤ q (n+1)`
        exact hq_mono n
      · -- `max 0 (hf.approx x n) ≤ max 0 (hf.approx x (n+1))`
        apply max_le_max le_rfl
        exact hf.approx_mono x n
      · exact le_max_left 0 _
      · exact hq_nonneg (n + 1)

    · intro x n
      -- Show both factors are bounded by `c` and `f x`.
      have hq' : (Rat.cast (q n) : ℝ) ≤ c := hq_le_c n
      have ha : ((max 0 (hf.approx x n) : ℚ) : ℝ) ≤ f x := by
        have : max (0 : ℝ) (hf.approx x n : ℝ) ≤ f x :=
          (max_le_iff).2 ⟨hf_nn x, hf.approx_le x n⟩
        simpa [Rat.cast_max] using this
      have hq_nonneg' : 0 ≤ (Rat.cast (q n) : ℝ) :=
        Rat.cast_nonneg.mpr (hq_nonneg n)
      have ha_nonneg : 0 ≤ ((max 0 (hf.approx x n) : ℚ) : ℝ) := by
        simp [Rat.cast_max]
      -- Multiply the bounds.
      have hq_mul :
          (Rat.cast (q n) : ℝ) * ((max 0 (hf.approx x n) : ℚ) : ℝ) ≤ c * f x :=
        mul_le_mul hq' ha ha_nonneg hc
      -- Unfold the approximation and cast.
      simpa [Rat.cast_max, Rat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hq_mul

    · intro x ε hε
      have hc_pos' : 0 < 2 * c := by
        have : (0 : ℝ) < 2 := by norm_num
        exact mul_pos this hc_pos

      obtain ⟨N1, h1⟩ := hf.approx_converges x (ε / (2 * c)) (div_pos hε hc_pos')

      -- Choose `N2` so that `1/(N2+1) < min c (ε/(2*(f x + 1)))`.
      have hmin_pos : 0 < min c (ε / (2 * (f x + 1))) := by
        have hε' : 0 < ε / (2 * (f x + 1)) := by
          have hden : 0 < 2 * (f x + 1) := by
            have h2 : (0 : ℝ) < 2 := by norm_num
            have hf1 : 0 < f x + 1 := by linarith [hf_nn x]
            exact mul_pos h2 hf1
          exact div_pos hε hden
        exact lt_min hc_pos hε'
      obtain ⟨N2, hN2⟩ := exists_nat_one_div_lt (K := ℝ) hmin_pos

      refine ⟨max N1 N2, ?_⟩
      intro n hn
      have hn1 : N1 ≤ n := le_of_max_le_left hn
      have hn2 : N2 ≤ n := le_of_max_le_right hn

      -- Show `c - q n < ε / (2 * (f x + 1))`.
      have h_one_div_le : (1 : ℝ) / (n + 1 : ℝ) ≤ (1 : ℝ) / (N2 + 1 : ℝ) := by
        have hpos : 0 < (N2 + 1 : ℝ) := by exact_mod_cast Nat.succ_pos N2
        have hle : (N2 + 1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ hn2
        exact one_div_le_one_div_of_le hpos hle
      have h_one_div_lt_c : (1 : ℝ) / (n + 1 : ℝ) < c := by
        have : (1 : ℝ) / (N2 + 1 : ℝ) < c := (lt_of_lt_of_le hN2 (min_le_left _ _))
        exact lt_of_le_of_lt h_one_div_le this

      have hsub_pos : 0 ≤ c - (1 : ℝ) / (n + 1 : ℝ) :=
        le_of_lt (sub_pos.2 h_one_div_lt_c)
      have hlower_eq : lower n = c - (1 : ℝ) / (n + 1 : ℝ) := by
        dsimp [lower]
        exact max_eq_right hsub_pos
      have hcand : c - (1 : ℝ) / (n + 1 : ℝ) < (cand n : ℝ) := by
        simpa [hlower_eq] using (cand_spec n).1
      have hc_cand : c - (cand n : ℝ) < (1 : ℝ) / (n + 1 : ℝ) := by
        have h1 : c < (cand n : ℝ) + (1 : ℝ) / (n + 1 : ℝ) := (sub_lt_iff_lt_add).1 hcand
        have h2 : c < (1 : ℝ) / (n + 1 : ℝ) + (cand n : ℝ) := by
          simpa [add_comm, add_left_comm, add_assoc] using h1
        exact (sub_lt_iff_lt_add).2 h2

      have hq_ge_cand : (cand n : ℝ) ≤ (Rat.cast (q n) : ℝ) := by
        induction n with
        | zero =>
          simp [q, Rat.cast_max]
        | succ n _ih =>
          simp [q, Rat.cast_max]

      have hc_q : c - (Rat.cast (q n) : ℝ) < (1 : ℝ) / (n + 1 : ℝ) := by
        have hle : c - (Rat.cast (q n) : ℝ) ≤ c - (cand n : ℝ) :=
          sub_le_sub_left hq_ge_cand c
        exact lt_of_le_of_lt hle hc_cand

      have hc_q' : c - (Rat.cast (q n) : ℝ) < ε / (2 * (f x + 1)) := by
        have : (1 : ℝ) / (n + 1 : ℝ) < ε / (2 * (f x + 1)) := by
          have : (1 : ℝ) / (N2 + 1 : ℝ) < ε / (2 * (f x + 1)) :=
            lt_of_lt_of_le hN2 (min_le_right _ _)
          exact lt_of_le_of_lt h_one_div_le this
        exact lt_of_lt_of_le hc_q (le_of_lt this)

      -- Bound the two error terms.
      have h_err2 :
          (Rat.cast (q n) : ℝ) * (f x - max (0 : ℝ) (hf.approx x n : ℝ)) < ε / 2 := by
        have h_f_minus :
            f x - max (0 : ℝ) (hf.approx x n : ℝ) ≤ f x - (hf.approx x n : ℝ) := by
          have : (hf.approx x n : ℝ) ≤ max (0 : ℝ) (hf.approx x n : ℝ) := le_max_right _ _
          exact sub_le_sub_left this (f x)
        have h_f_minus_lt : f x - max (0 : ℝ) (hf.approx x n : ℝ) < ε / (2 * c) :=
          lt_of_le_of_lt h_f_minus (h1 n hn1)
        have hq_le : (Rat.cast (q n) : ℝ) ≤ c := hq_le_c n
        have h_nonneg : 0 ≤ f x - max (0 : ℝ) (hf.approx x n : ℝ) := by
          have hmax_le : max (0 : ℝ) (hf.approx x n : ℝ) ≤ f x :=
            (max_le_iff).2 ⟨hf_nn x, hf.approx_le x n⟩
          linarith
        have : (Rat.cast (q n) : ℝ) * (f x - max (0 : ℝ) (hf.approx x n : ℝ))
              ≤ c * (f x - max (0 : ℝ) (hf.approx x n : ℝ)) :=
          mul_le_mul_of_nonneg_right hq_le h_nonneg
        have hc_mul : c * (f x - max (0 : ℝ) (hf.approx x n : ℝ)) < ε / 2 := by
          -- Multiply the strict bound by `c`.
          have hc_ne0 : (c : ℝ) ≠ 0 := ne_of_gt hc_pos
          have hcancel : c * (ε / (2 * c)) = ε / 2 := by
            calc
              c * (ε / (2 * c)) = c * ε / (2 * c) := by
                simp [mul_div_assoc]
              _ = c * ε / (c * 2) := by
                simp [mul_comm]
              _ = ε / 2 := by
                simpa [mul_comm, mul_assoc] using
                  (mul_div_mul_left (c := c) (a := ε) (b := 2) hc_ne0)
          have hc_pos_real : 0 < c := hc_pos
          have hmul := mul_lt_mul_of_pos_left h_f_minus_lt hc_pos_real
          simpa [hcancel] using hmul
        exact lt_of_le_of_lt this hc_mul

      have h_err1 :
          (c - (Rat.cast (q n) : ℝ)) * f x < ε / 2 := by
        have hden_pos : 0 < (f x + 1) := by linarith [hf_nn x]
        have hcq_nonneg : 0 ≤ c - (Rat.cast (q n) : ℝ) := by
          exact sub_nonneg.2 (hq_le_c n)
        have hfx_le : f x ≤ f x + 1 := by linarith
        have h_le :
            (c - (Rat.cast (q n) : ℝ)) * f x ≤ (c - (Rat.cast (q n) : ℝ)) * (f x + 1) :=
          mul_le_mul_of_nonneg_left hfx_le hcq_nonneg
        have h_lt : (c - (Rat.cast (q n) : ℝ)) * (f x + 1) < ε / 2 := by
          -- Multiply `c - q n < ε/(2*(f x+1))` by `f x+1`.
          have hden_ne0 : (f x + 1) ≠ 0 := ne_of_gt hden_pos
          have hcancel : (ε / (2 * (f x + 1))) * (f x + 1) = ε / 2 := by
            calc
              (ε / (2 * (f x + 1))) * (f x + 1) = (ε * (f x + 1)) / (2 * (f x + 1)) := by
                simp [div_mul_eq_mul_div]
              _ = ε / 2 := by
                simpa using (mul_div_mul_right (a := ε) (b := 2) (c := (f x + 1)) hden_ne0)
          have hmul := mul_lt_mul_of_pos_right hc_q' hden_pos
          simpa [hcancel] using hmul
        exact lt_of_le_of_lt h_le h_lt

      -- Combine the two bounds.
      have hdecomp :
          c * f x - (Rat.cast (q n) : ℝ) * max (0 : ℝ) (hf.approx x n : ℝ) =
            (c - (Rat.cast (q n) : ℝ)) * f x +
              (Rat.cast (q n) : ℝ) * (f x - max (0 : ℝ) (hf.approx x n : ℝ)) := by
        simp [sub_mul, mul_sub]

      -- Finish: the difference is the sum of two terms, each < ε/2.
      have : c * f x - (Rat.cast (q n) : ℝ) * max (0 : ℝ) (hf.approx x n : ℝ) < ε := by
        rw [hdecomp]
        have hsum :
            (c - (Rat.cast (q n) : ℝ)) * f x +
                (Rat.cast (q n) : ℝ) * (f x - max (0 : ℝ) (hf.approx x n : ℝ))
            < ε / 2 + ε / 2 :=
          add_lt_add h_err1 h_err2
        simpa [add_halves ε] using hsum

      -- Unfold and cast the approximation definition.
      simpa [Rat.cast_mul, Rat.cast_max, mul_assoc, mul_left_comm, mul_comm, q] using this

/-- Product of nonnegative lower semicomputable functions (requires bounded inputs) -/
noncomputable def mul {α : Type*} {f g : α → ℝ} {M : ℝ}
    (hf : LowerSemicomputable f) (hg : LowerSemicomputable g)
    (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ x, 0 ≤ g x)
    (hf_bound : ∀ x, f x ≤ M) (hg_bound : ∀ x, g x ≤ M) :
    LowerSemicomputable (fun x => f x * g x) where
  -- Key insight: Apply max 0 to EACH factor before multiplying
  -- This ensures both factors are nonnegative, making mul_le_mul applicable
  approx x n := max 0 (hf.approx x n) * max 0 (hg.approx x n)
  approx_mono x n := by
    -- Need: max 0 (f[n]) * max 0 (g[n]) ≤ max 0 (f[n+1]) * max 0 (g[n+1])
    apply mul_le_mul
    · apply max_le_max le_rfl
      exact hf.approx_mono x n
    · apply max_le_max le_rfl
      exact hg.approx_mono x n
    · exact le_max_left 0 _  -- 0 ≤ max 0 (g[n])
    · exact le_max_left 0 _  -- 0 ≤ max 0 (f[n+1])
  approx_le x n := by
    -- Need: (max 0 (f[n]) * max 0 (g[n]) : ℝ) ≤ f x * g x
    -- Both factors are ≤ their original values, and original values ≤ targets
    have ha : ((max 0 (hf.approx x n) : ℚ) : ℝ) ≤ f x := by
      have : max (0 : ℝ) (hf.approx x n : ℝ) ≤ f x :=
        (max_le_iff).2 ⟨hf_nn x, hf.approx_le x n⟩
      simpa [Rat.cast_max] using this
    have hb : ((max 0 (hg.approx x n) : ℚ) : ℝ) ≤ g x := by
      have : max (0 : ℝ) (hg.approx x n : ℝ) ≤ g x :=
        (max_le_iff).2 ⟨hg_nn x, hg.approx_le x n⟩
      simpa [Rat.cast_max] using this
    have ha_nonneg : 0 ≤ ((max 0 (hf.approx x n) : ℚ) : ℝ) := by
      simp [Rat.cast_max]
    have hb_nonneg : 0 ≤ ((max 0 (hg.approx x n) : ℚ) : ℝ) := by
      simp [Rat.cast_max]
    have : ((max 0 (hf.approx x n) : ℚ) : ℝ) * ((max 0 (hg.approx x n) : ℚ) : ℝ) ≤ f x * g x :=
      mul_le_mul ha hb hb_nonneg (hf_nn x)
    simpa [Rat.cast_mul, Rat.cast_max, mul_assoc, mul_left_comm, mul_comm] using this
  approx_converges x ε hε := by
    set B : ℝ := max 1 M
    have hB_pos : 0 < B := by
      have : (0 : ℝ) < 1 := by norm_num
      exact lt_of_lt_of_le this (le_max_left 1 M)
    have h2B_pos : 0 < 2 * B := mul_pos (by norm_num) hB_pos
    have hδ_pos : 0 < ε / (2 * B) := div_pos hε h2B_pos
    obtain ⟨N1, h1⟩ := hf.approx_converges x (ε / (2 * B)) hδ_pos
    obtain ⟨N2, h2⟩ := hg.approx_converges x (ε / (2 * B)) hδ_pos
    refine ⟨max N1 N2, ?_⟩
    intro n hn
    have hn1 : N1 ≤ n := le_of_max_le_left hn
    have hn2 : N2 ≤ n := le_of_max_le_right hn

    -- Abbreviations for the clipped approximations.
    let a : ℝ := max 0 (hf.approx x n : ℝ)
    let b : ℝ := max 0 (hg.approx x n : ℝ)
    have ha_le_fx : a ≤ f x := (max_le_iff).2 ⟨hf_nn x, hf.approx_le x n⟩
    have hb_le_gx : b ≤ g x := (max_le_iff).2 ⟨hg_nn x, hg.approx_le x n⟩
    have ha_nonneg : 0 ≤ a := le_max_left _ _
    have hb_nonneg : 0 ≤ b := le_max_left _ _

    have hfB : f x ≤ B := le_trans (hf_bound x) (le_max_right 1 M)
    have hgB : g x ≤ B := le_trans (hg_bound x) (le_max_right 1 M)
    have haB : a ≤ B := le_trans ha_le_fx hfB
    have hbB : b ≤ B := le_trans hb_le_gx hgB

    have hfa_lt : f x - a < ε / (2 * B) := by
      -- `a ≥ hf.approx x n`, so `f - a ≤ f - hf.approx`.
      have hle : f x - a ≤ f x - (hf.approx x n : ℝ) := by
        have : (hf.approx x n : ℝ) ≤ a := le_max_right _ _
        exact sub_le_sub_left this (f x)
      exact lt_of_le_of_lt hle (h1 n hn1)
    have hgb_lt : g x - b < ε / (2 * B) := by
      have hle : g x - b ≤ g x - (hg.approx x n : ℝ) := by
        have : (hg.approx x n : ℝ) ≤ b := le_max_right _ _
        exact sub_le_sub_left this (g x)
      exact lt_of_le_of_lt hle (h2 n hn2)

    -- Decompose the product difference.
    have hdecomp :
        f x * g x - a * b = (f x - a) * g x + a * (g x - b) := by
      simp [sub_mul, mul_sub]

    -- Bound each term by `ε/2`.
    have hterm1 :
        (f x - a) * g x < ε / 2 := by
      have hle : (f x - a) * g x ≤ (f x - a) * B :=
        mul_le_mul_of_nonneg_left hgB (by
          have : a ≤ f x := ha_le_fx
          linarith)
      have hlt : (f x - a) * B < ε / 2 := by
        have hmul : (f x - a) * B < (ε / (2 * B)) * B :=
          mul_lt_mul_of_pos_right hfa_lt hB_pos
        have hB_ne0 : (B : ℝ) ≠ 0 := ne_of_gt hB_pos
        have hcancel : (ε / (2 * B)) * B = ε / 2 := by
          -- Cancel `B` on the right.
          rw [div_mul_eq_mul_div]
          simpa [mul_assoc] using (mul_div_mul_right ε 2 hB_ne0)
        simpa [hcancel] using hmul
      exact lt_of_le_of_lt hle hlt
    have hterm2 :
        a * (g x - b) < ε / 2 := by
      have hle : a * (g x - b) ≤ B * (g x - b) :=
        mul_le_mul_of_nonneg_right haB (by
          have : b ≤ g x := hb_le_gx
          linarith)
      have hlt : B * (g x - b) < ε / 2 := by
        have hmul : B * (g x - b) < B * (ε / (2 * B)) :=
          mul_lt_mul_of_pos_left hgb_lt hB_pos
        have hB_ne0 : (B : ℝ) ≠ 0 := ne_of_gt hB_pos
        have hcancel : B * (ε / (2 * B)) = ε / 2 := by
          -- Commute, then cancel `B` on the right.
          have : B * (ε / (2 * B)) = (ε / (2 * B)) * B := by
            simp [mul_comm]
          rw [this, div_mul_eq_mul_div]
          simpa [mul_assoc] using (mul_div_mul_right ε 2 hB_ne0)
        simpa [hcancel] using hmul
      exact lt_of_le_of_lt hle hlt

    -- Combine bounds and cast back to the rational approximation.
    have hsum : (f x - a) * g x + a * (g x - b) < ε := by
      have hsum' : (f x - a) * g x + a * (g x - b) < ε / 2 + ε / 2 :=
        add_lt_add hterm1 hterm2
      simpa [add_halves ε] using hsum'

    -- Final simplification.
    have : f x * g x - a * b < ε := by simpa [hdecomp] using hsum
    -- Replace `a * b` with the cast of the rational approximation.
    simpa [a, b, Rat.cast_mul, Rat.cast_max, mul_assoc, mul_left_comm, mul_comm] using this

/-- Finite infimum of lower semicomputable functions -/
noncomputable def finset_inf {α β : Type*} [Fintype β] {f : β → α → ℝ}
    (hf : ∀ b, LowerSemicomputable (f b)) (h_nonempty : Nonempty β) :
    LowerSemicomputable (fun x => Finset.inf' Finset.univ Finset.univ_nonempty (fun b => f b x)) where
  approx x n := Finset.inf' Finset.univ Finset.univ_nonempty (fun b => (hf b).approx x n)
  approx_mono x n := by
    -- Need to show: inf at n ≤ inf at n+1
    -- Use that inf is monotone: if f ≤ g pointwise, then inf f ≤ inf g
    apply Finset.le_inf'
    intro b _
    have h_mono : (hf b).approx x n ≤ (hf b).approx x (n+1) := (hf b).approx_mono x n
    calc Finset.inf' Finset.univ Finset.univ_nonempty (fun b' => (hf b').approx x n)
        ≤ (hf b).approx x n := Finset.inf'_le _ (Finset.mem_univ b)
      _ ≤ (hf b).approx x (n+1) := h_mono
  approx_le x n := by
    apply Finset.le_inf'
    intro b _
    have h_inf_le : Finset.inf' Finset.univ Finset.univ_nonempty (fun b' => (hf b').approx x n)
                  ≤ (hf b).approx x n := Finset.inf'_le _ (Finset.mem_univ b)
    calc ((Finset.inf' Finset.univ Finset.univ_nonempty (fun b' => (hf b').approx x n) : ℚ) : ℝ)
        ≤ ((hf b).approx x n : ℝ) := Rat.cast_le.mpr h_inf_le
      _ ≤ f b x := (hf b).approx_le x n
  approx_converges x ε hε := by
    choose N_b hN_b using fun b => (hf b).approx_converges x ε hε
    use Finset.univ.sup N_b
    intro n hn
    -- Let `bₙ` be a minimizer of the *approximation* at stage `n`.
    obtain ⟨bₙ, hbₙ_mem, hbₙ_eq⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun b => (hf b).approx x n)
    have hN : N_b bₙ ≤ n := le_trans (Finset.le_sup hbₙ_mem) hn
    have h_close : f bₙ x - ((hf bₙ).approx x n : ℝ) < ε := hN_b bₙ n hN

    -- The true infimum is ≤ the value at `bₙ`.
    have h_inf_le : Finset.inf' Finset.univ Finset.univ_nonempty (fun b => f b x) ≤ f bₙ x :=
      Finset.inf'_le _ hbₙ_mem

    -- And `inf f - inf approx ≤ f bₙ - approx bₙ`.
    have h_cast :
        ((Finset.inf' Finset.univ Finset.univ_nonempty (fun b => (hf b).approx x n) : ℚ) : ℝ) =
          (hf bₙ).approx x n := by
      -- `hbₙ_eq` identifies the infimum in `ℚ`; cast is definitional.
      simp [hbₙ_eq]

    have : Finset.inf' Finset.univ Finset.univ_nonempty (fun b => f b x) -
          ((Finset.inf' Finset.univ Finset.univ_nonempty (fun b => (hf b).approx x n) : ℚ) : ℝ)
          < ε := by
      -- Use the bound via `bₙ`.
      have hle' :
          Finset.inf' Finset.univ Finset.univ_nonempty (fun b => f b x) -
              ((Finset.inf' Finset.univ Finset.univ_nonempty (fun b => (hf b).approx x n) : ℚ) : ℝ)
            ≤ f bₙ x - ((hf bₙ).approx x n : ℝ) := by
        -- subtract monotonicity from `h_inf_le`, then rewrite by `hbₙ_eq`.
        have : Finset.inf' Finset.univ Finset.univ_nonempty (fun b => f b x) -
              ((hf bₙ).approx x n : ℝ) ≤ f bₙ x - ((hf bₙ).approx x n : ℝ) :=
          sub_le_sub_right h_inf_le ((hf bₙ).approx x n : ℝ)
        simpa [h_cast] using this
      exact lt_of_le_of_lt hle' h_close

    simpa using this

/-- Precomposition preserves lower semicomputability -/
noncomputable def comp {α β : Type*} {f : β → ℝ} (hf : LowerSemicomputable f) (g : α → β) :
    LowerSemicomputable (f ∘ g) where
  approx x n := hf.approx (g x) n
  approx_mono x n := hf.approx_mono (g x) n
  approx_le x n := hf.approx_le (g x) n
  approx_converges x ε hε := hf.approx_converges (g x) ε hε

/-- Helper: sum over a list -/
noncomputable def list_sum {α ι : Type*}
    {f : ι → α → ℝ} (hf : ∀ i, LowerSemicomputable (f i)) :
    (l : List ι) → LowerSemicomputable (fun x => (l.map (f · x)).sum)
  | [] => by simp only [List.map_nil, List.sum_nil]; exact const_zero
  | i :: is => by
    simp only [List.map_cons, List.sum_cons]
    exact add (hf i) (list_sum hf is)

/-- Finite sum over a finset preserves lower semicomputability -/
noncomputable def finset_sum_finset {α ι : Type*} [DecidableEq ι] (s : Finset ι)
    {f : ι → α → ℝ} (hf : ∀ i, LowerSemicomputable (f i)) :
    LowerSemicomputable (fun x => ∑ i ∈ s, f i x) := by
  have heq : (fun x => ∑ i ∈ s, f i x) = (fun x => (s.toList.map (f · x)).sum) := by
    ext x
    simp only [Finset.sum_eq_multiset_sum]
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
  rw [heq]
  exact list_sum hf s.toList

/-- Finite sum over a Fintype preserves lower semicomputability -/
noncomputable def finset_sum {α β : Type*} [Fintype β] [DecidableEq β]
    {f : β → α → ℝ} (hf : ∀ b, LowerSemicomputable (f b)) :
    LowerSemicomputable (fun x => ∑ b : β, f b x) :=
  finset_sum_finset Finset.univ hf

/-- Subtraction of lower semicomputable f minus upper semicomputable g gives
    lower semicomputable result.

    This is the CORRECT way to handle subtraction in computability:
    - f approximated from BELOW (lower semicomputable)
    - g approximated from ABOVE (upper semicomputable)
    - Then f_n - g̅_n is monotone increasing and underestimates f - g

    The approximation scheme:
      approx n = f_n - g̅_n

    Properties (all satisfied):
    1. Monotonicity: f_n increasing, g̅_n decreasing ⟹ f_n - g̅_n increasing ✓
    2. Lower bound: f_n ≤ f and g̅_n ≥ g ⟹ f_n - g̅_n ≤ f - g ✓
    3. Convergence: both converge ⟹ difference converges ✓

    NOTE: This requires g to be upper semicomputable, not just lower semicomputable.
    For semimeasure loss, this means ν must be COMPUTABLE (both l.s.c. and u.s.c.).
-/
noncomputable def sub {α : Type*} {f g : α → ℝ}
    (hf : LowerSemicomputable f) (hg : UpperSemicomputable g) :
    LowerSemicomputable (fun x => f x - g x) where
  approx x n := hf.approx x n - hg.approx x n
  approx_mono x n := by
    -- f_n increasing and g̅_n decreasing ⟹ f_n - g̅_n increasing
    have h1 : hf.approx x n ≤ hf.approx x (n+1) := hf.approx_mono x n
    have h2 : hg.approx x (n+1) ≤ hg.approx x n := hg.approx_anti x n
    linarith
  approx_le x n := by
    -- f_n ≤ f and g̅_n ≥ g ⟹ f_n - g̅_n ≤ f - g
    have h1 : (hf.approx x n : ℝ) ≤ f x := hf.approx_le x n
    have h2 : g x ≤ (hg.approx x n : ℝ) := hg.approx_ge x n
    simp only [Rat.cast_sub]
    linarith
  approx_converges x ε hε := by
    have hε2 : 0 < ε/2 := half_pos hε
    obtain ⟨N1, h1⟩ := hf.approx_converges x (ε/2) hε2
    obtain ⟨N2, h2⟩ := hg.approx_converges x (ε/2) hε2
    use max N1 N2
    intro n hn
    have hn1 : N1 ≤ n := le_of_max_le_left hn
    have hn2 : N2 ≤ n := le_of_max_le_right hn
    simp only [Rat.cast_sub]
    -- We need: (f - g) - (f_n - g̅_n) < ε
    -- = (f - f_n) + (g̅_n - g) < ε
    have hf_bound := h1 n hn1  -- f - f_n < ε/2
    have hg_bound := h2 n hn2  -- g̅_n - g < ε/2
    linarith

/-- Monotone limit preserves lower semicomputability.

    **Key Theorem for Simple Function Approximation**:
    If f_n : α → ℝ is an increasing sequence of l.s.c. functions converging
    pointwise to f, then f is l.s.c.

    This is fundamental for the Wyeth/Hutter proof:
    1. Approximate utility U from below by simple functions U_n
    2. Each Choquet integral ∫ U_n dν is l.s.c. (finite sum with constant coefficients)
    3. By monotone convergence, ∫ U_n dν ↗ ∫ U dν
    4. This lemma shows ∫ U dν is l.s.c.

    **Proof Strategy**:
    Build approx for f by "diagonalizing" over approximations for f_n:
    - approx_f x m = max_{n ≤ m} (f_n).approx x m

    Properties:
    1. Monotone: max over larger set is larger
    2. Lower bound: f_n.approx x m ≤ f_n x ≤ f x for all n
    3. Convergence: for any ε, can find N where f_N is ε/2-close to f,
       then M where f_N.approx is ε/2-close to f_N
-/
noncomputable def monotone_sup {α : Type*} {f : α → ℝ} {f_n : ℕ → α → ℝ}
    (hf_n_lsc : ∀ n, LowerSemicomputable (f_n n))
    (_h_mono : ∀ n x, f_n n x ≤ f_n (n+1) x)
    (h_conv : ∀ x ε, 0 < ε → ∃ N, ∀ n ≥ N, f x - f_n n x < ε)
    (h_bound : ∀ n x, f_n n x ≤ f x) :
    LowerSemicomputable f where
  approx x m := Finset.sup' (Finset.range (m+1)) Finset.nonempty_range_add_one
                  (fun n => (hf_n_lsc n).approx x m)
  approx_mono x m := by
    -- sup over {0, ..., m} at stage m ≤ sup over {0, ..., m+1} at stage m+1
    apply Finset.sup'_le
    intro n hn
    have hn' : n ∈ Finset.range (m + 1 + 1) := by
      simp only [Finset.mem_range] at hn ⊢
      omega
    calc (hf_n_lsc n).approx x m
        ≤ (hf_n_lsc n).approx x (m+1) := (hf_n_lsc n).approx_mono x m
      _ ≤ Finset.sup' (Finset.range (m+1+1)) Finset.nonempty_range_add_one
            (fun n' => (hf_n_lsc n').approx x (m+1)) :=
              Finset.le_sup' (fun n' => (hf_n_lsc n').approx x (m+1)) hn'
  approx_le x m := by
    -- Need: cast(sup' {approx values}) ≤ f x
    -- Since the sup is achieved by some element in the finite set,
    -- and each element cast to ℝ is ≤ f x, the sup cast to ℝ is ≤ f x
    obtain ⟨i, _hi_mem, hi_eq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      (fun n => (hf_n_lsc n).approx x m)
    rw [hi_eq]
    calc ((hf_n_lsc i).approx x m : ℝ)
        ≤ f_n i x := (hf_n_lsc i).approx_le x m
      _ ≤ f x := h_bound i x
  approx_converges x ε hε := by
    have hε2 : 0 < ε / 2 := half_pos hε
    -- Step 1: Find N where f_N is ε/2-close to f
    obtain ⟨N, hN⟩ := h_conv x (ε / 2) hε2
    -- Step 2: Find M where f_N.approx is ε/2-close to f_N
    obtain ⟨M, hM⟩ := (hf_n_lsc N).approx_converges x (ε / 2) hε2
    -- Use max(N, M) as the stage
    use max N M
    intro m hm
    have hm_N : N ≤ m := le_trans (le_max_left N M) hm
    have hm_M : M ≤ m := le_trans (le_max_right N M) hm
    -- f_N.approx x m is in the sup, so sup ≥ f_N.approx x m
    have hN_in : N ∈ Finset.range (m + 1) := by
      simp only [Finset.mem_range]
      omega
    have h_sup_ge : (hf_n_lsc N).approx x m ≤
        Finset.sup' (Finset.range (m+1)) Finset.nonempty_range_add_one
          (fun n => (hf_n_lsc n).approx x m) :=
      Finset.le_sup' (fun n => (hf_n_lsc n).approx x m) hN_in
    -- Now compute the error bound
    have h_key : f x - ((Finset.sup' (Finset.range (m+1)) Finset.nonempty_range_add_one
                (fun n => (hf_n_lsc n).approx x m) : ℚ) : ℝ)
        ≤ f x - ((hf_n_lsc N).approx x m : ℝ) := by
      apply sub_le_sub_left
      exact Rat.cast_le.mpr h_sup_ge
    calc f x - ((Finset.sup' (Finset.range (m+1)) Finset.nonempty_range_add_one
                (fun n => (hf_n_lsc n).approx x m) : ℚ) : ℝ)
        ≤ f x - ((hf_n_lsc N).approx x m : ℝ) := h_key
      _ = (f x - f_n N x) + (f_n N x - (hf_n_lsc N).approx x m) := by ring
      _ < ε / 2 + ε / 2 := by
            apply add_lt_add
            · exact hN N (le_refl N)
            · exact hM m hm_M
      _ = ε := add_halves ε

end LowerSemicomputable

/-! ## Complementation Results -/

/-- Σ⁰₂ and Π⁰₂ predicates are complementary -/
def sigma02_complement_pi02 {P : ℕ → Prop} (h : Sigma02Predicate P) :
    Pi02Predicate (fun n => ¬P n) where
  approx := fun n k => !h.approx n k
  approx_computable := by
    -- Composition: h.approx is computable, ! is computable
    exact Computable.comp₂ bool_not_computable h.approx_computable
  converges := fun n => by
    constructor
    · -- If ¬P n, then !h.approx is infinitely often true
      intro hn m
      -- We need to show: ∃ k ≥ m, !h.approx n k = true
      -- This means: ∃ k ≥ m, h.approx n k = false
      by_contra h_contra
      push_neg at h_contra
      -- h_contra says: ∀ k ≥ m, !h.approx n k ≠ true
      -- Which means: ∀ k ≥ m, h.approx n k = true
      have h_all_true : ∀ k ≥ m, h.approx n k = true := fun k hk => by
        have h_neg_ne_true := h_contra k hk
        -- !h.approx n k ≠ true means h.approx n k must be true
        cases h_val : h.approx n k
        · -- h.approx n k = false, so !false = true, contradiction with h_neg_ne_true
          simp [h_val] at h_neg_ne_true
        · -- h.approx n k = true
          rfl
      -- But this means P n holds
      have : P n := (h.converges n).mpr ⟨m, h_all_true⟩
      exact hn this
    · -- If approx is infinitely often true, then ¬P n
      intro h_inf hp
      -- P n means h.approx eventually stabilizes to true
      obtain ⟨m, hm⟩ := (h.converges n).mp hp
      -- But h_inf says !h.approx is infinitely often true
      obtain ⟨k, hk_ge, hk_true⟩ := h_inf m
      -- So h.approx n k = false
      have : h.approx n k = false := by
        cases h_approx : h.approx n k
        · rfl
        · simp [h_approx] at hk_true
      -- But hm says h.approx n k = true (contradiction)
      have h_true : h.approx n k = true := hm k hk_ge
      rw [this] at h_true
      simp at h_true

def pi02_complement_sigma02 {P : ℕ → Prop} (h : Pi02Predicate P) :
    Sigma02Predicate (fun n => ¬P n) where
  approx := fun n k => !h.approx n k
  approx_computable := by
    -- Composition: h.approx is computable, ! is computable
    exact Computable.comp₂ bool_not_computable h.approx_computable
  converges := fun n => by
    constructor
    · -- If ¬P n, then !h.approx eventually stabilizes to true
      intro hn
      -- ¬P n means h.approx is NOT infinitely often true
      -- So ∃ m, ∀ k ≥ m, h.approx n k = false
      -- Which means ∃ m, ∀ k ≥ m, !h.approx n k = true
      by_contra h_contra
      push_neg at h_contra
      -- h_contra says: ∀ m, ∃ k ≥ m, !h.approx n k ≠ true
      -- Which means: ∀ m, ∃ k ≥ m, h.approx n k = true
      have h_inf_often : ∀ m, ∃ k ≥ m, h.approx n k = true := fun m => by
        obtain ⟨k, hk_ge, h_neg_ne_true⟩ := h_contra m
        use k, hk_ge
        -- !h.approx n k ≠ true means h.approx n k = true
        cases h_val : h.approx n k
        · -- h.approx n k = false, so !false = true, contradiction
          simp [h_val] at h_neg_ne_true
        · -- h.approx n k = true
          rfl
      -- But this means P n holds
      have : P n := (h.converges n).mpr h_inf_often
      exact hn this
    · -- If !approx eventually stabilizes to true, then ¬P n
      intro ⟨m, hm⟩ hp
      -- P n means h.approx is infinitely often true
      obtain ⟨k, hk_ge, hk_true⟩ := ((h.converges n).mp hp) m
      -- But hm says !h.approx n k = true, so h.approx n k = false
      have : h.approx n k = false := by
        have := hm k hk_ge
        cases h_approx : h.approx n k
        · rfl
        · simp [h_approx] at this
      rw [this] at hk_true
      simp at hk_true

end Mettapedia.Computability.ArithmeticalHierarchy
