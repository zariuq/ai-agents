import Mettapedia.Computability.HutterComputabilityClosure

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# ENNReal helpers for Hutter-style lower semicomputability

Hutter's `LowerSemicomputable` predicate is defined for real-valued functions via computable
monotone dyadic approximations.

In universal prediction, mixture semimeasures are often expressed as `ENNReal`-valued `tsum`s.
To connect those to `LowerSemicomputable`, we need a small bridge:

* rewrite `((∑' i, f i).toReal)` as `∑' i, (f i).toReal` (requires `f i ≠ ⊤`), and
* apply the real-valued `tsum` closure lemma.
 -/

namespace Mettapedia.Computability.Hutter

open scoped Classical BigOperators

namespace LowerSemicomputable

variable {α : Type*} [Primcodable α]

/-- `LowerSemicomputable` is stable under pointwise equality. -/
theorem congr {f g : α → ℝ} (hf : LowerSemicomputable f) (hfg : ∀ x, f x = g x) :
    LowerSemicomputable g := by
  rcases hf with ⟨a, ha, hmono, htendsto⟩
  refine ⟨a, ha, hmono, ?_⟩
  intro x
  simpa [hfg x] using htendsto x

/-- If `f : ℕ → α → ℝ≥0∞` is pointwise finite and the real-valued map `(n,x) ↦ (f n x).toReal`
is uniformly lower-semicomputable, then `x ↦ (∑' n, f n x).toReal` is lower semicomputable. -/
theorem tsum_toReal_of_nonneg (f : ℕ → α → ENNReal)
    (hf_ne_top : ∀ n x, f n x ≠ ⊤)
    (hsum : ∀ x, Summable (fun n : ℕ => (f n x).toReal))
    (hLSC : LowerSemicomputable (fun p : ℕ × α => (f p.1 p.2).toReal)) :
    LowerSemicomputable (fun x : α => (∑' n : ℕ, f n x).toReal) := by
  -- Convert `toReal (tsum ...)` to `tsum (toReal ...)`.
  have hEq : ∀ x, (∑' n : ℕ, f n x).toReal = ∑' n : ℕ, (f n x).toReal := by
    intro x
    simpa using (ENNReal.tsum_toReal_eq (f := fun n : ℕ => f n x) (hf := fun n => hf_ne_top n x))
  -- Apply the real-valued closure lemma.
  have h0 : ∀ n x, 0 ≤ (f n x).toReal := by
    intro n x
    exact ENNReal.toReal_nonneg
  have hLC : LowerSemicomputable (fun x : α => ∑' n : ℕ, (f n x).toReal) :=
    LowerSemicomputable.tsum_of_nonneg (g := fun n x => (f n x).toReal)
      (h0 := h0) (hsum := hsum) (hLSC := hLSC)
  -- Rewrite the target using `hEq`.
  exact congr (f := fun x : α => ∑' n : ℕ, (f n x).toReal)
    (g := fun x : α => (∑' n : ℕ, f n x).toReal) hLC (fun x => (hEq x).symm)

end LowerSemicomputable

end Mettapedia.Computability.Hutter

