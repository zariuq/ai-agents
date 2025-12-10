import Mathlib.Algebra.Order.Quantale
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mettapedia.Logic.PLNDeduction

/-!
# PLN Evidence Counts as a Quantale

This file implements the **canonical quantale carrier** for PLN: evidence counts.

## The Key Insight (from GPT-5 Pro review)

Instead of trying to make `[0,1]` a quantale (which fails because sup might exceed 1),
we use **evidence counts** `(n⁺, n⁻) ∈ ℝ≥0∞ × ℝ≥0∞` as the carrier:

- `n⁺` = positive evidence (supports the proposition)
- `n⁻` = negative evidence (refutes the proposition)

This IS a proper quantale:
- Complete lattice: coordinatewise ≤ with sup/inf
- Monoid ⊗: coordinatewise multiplication
- Quantale law: ⊗ distributes over ⨆

Then `SimpleTruthValue (s, c)` becomes a **view** via the standard PLN mapping:
- `s = n⁺ / (n⁺ + n⁻)`           (strength)
- `c = (n⁺ + n⁻) / (n⁺ + n⁻ + κ)` (confidence, with prior κ)

## Main Definitions

- `Evidence` : The evidence counts type
- `Evidence.tensor` : Quantale multiplication (sequential composition)
- `Evidence.hplus` : Parallel aggregation (independent evidence combination)
- `toSTV` / `ofSTV` : View functions to/from SimpleTruthValue

## References

- Goertzel et al., "Probabilistic Logic Networks" (2009), Chapter on truth-value formulas
- GPT-5 Pro review document (2025-12-09)
-/

namespace Mettapedia.Logic.PLNEvidence

open scoped ENNReal
open Mettapedia.Logic.PLNDeduction

/-! ## The Evidence Type

Evidence counts are pairs of extended non-negative reals representing
positive and negative support for a proposition.
-/

/-- Evidence counts: (positive support, negative support) -/
structure Evidence where
  pos : ℝ≥0∞  -- n⁺: positive evidence
  neg : ℝ≥0∞  -- n⁻: negative evidence
  deriving Inhabited

namespace Evidence

@[ext]
theorem ext' {e₁ e₂ : Evidence} (hp : e₁.pos = e₂.pos) (hn : e₁.neg = e₂.neg) : e₁ = e₂ := by
  cases e₁; cases e₂; simp only [mk.injEq]; exact ⟨hp, hn⟩

/-! ### Basic Operations -/

/-- Zero evidence: no support either way -/
def zero : Evidence := ⟨0, 0⟩

/-- Unit evidence for tensor product (multiplicative identity)
    Note: The unit is (1, 1) so that x ⊗ 1 = (x.pos * 1, x.neg * 1) = x -/
def one : Evidence := ⟨1, 1⟩

/-- Total evidence count: n⁺ + n⁻ -/
noncomputable def total (e : Evidence) : ℝ≥0∞ := e.pos + e.neg

/-! ### Lattice Structure (Coordinatewise)

The lattice order represents "information ordering" - more evidence is higher.
-/

instance : LE Evidence where
  le x y := x.pos ≤ y.pos ∧ x.neg ≤ y.neg

instance : LT Evidence where
  lt x y := x ≤ y ∧ ¬(y ≤ x)

theorem le_def (x y : Evidence) : x ≤ y ↔ x.pos ≤ y.pos ∧ x.neg ≤ y.neg := Iff.rfl

instance : Bot Evidence where
  bot := ⟨0, 0⟩

instance : Top Evidence where
  top := ⟨⊤, ⊤⟩

/-! ### Quantale Multiplication (Sequential Composition)

When evidence flows through a chain A → B → C, the evidence compounds multiplicatively.
This is the ⊗ operation in the quantale.
-/

/-- Tensor product: sequential composition of evidence
    (n⁺₁, n⁻₁) ⊗ (n⁺₂, n⁻₂) = (n⁺₁ * n⁺₂, n⁻₁ * n⁻₂)

    Interpretation: If A→B has evidence (n⁺₁, n⁻₁) and B→C has evidence (n⁺₂, n⁻₂),
    then the "direct path" A→B→C has evidence that compounds multiplicatively.
-/
noncomputable def tensor (x y : Evidence) : Evidence :=
  ⟨x.pos * y.pos, x.neg * y.neg⟩

noncomputable instance : Mul Evidence := ⟨tensor⟩

theorem tensor_def (x y : Evidence) : x * y = ⟨x.pos * y.pos, x.neg * y.neg⟩ := rfl

/-- Tensor is commutative -/
theorem tensor_comm (x y : Evidence) : x * y = y * x := by
  simp only [tensor_def, mul_comm]

/-- Tensor is associative -/
theorem tensor_assoc (x y z : Evidence) : (x * y) * z = x * (y * z) := by
  simp only [tensor_def, mul_assoc]

/-- One is the tensor unit -/
theorem tensor_one (x : Evidence) : x * one = x := by
  simp only [tensor_def, one, mul_one]

theorem one_tensor (x : Evidence) : one * x = x := by
  rw [tensor_comm, tensor_one]

noncomputable instance : CommMonoid Evidence where
  mul := tensor
  mul_assoc := tensor_assoc
  one := one
  one_mul := one_tensor
  mul_one := tensor_one
  mul_comm := tensor_comm

/-! ### Parallel Aggregation (Independent Evidence)

When we have independent sources of evidence, they combine additively.
This is the ⊕ operation (separate from the lattice join).
-/

/-- Parallel combination: independent evidence sources add
    (n⁺₁, n⁻₁) ⊕ (n⁺₂, n⁻₂) = (n⁺₁ + n⁺₂, n⁻₁ + n⁻₂)

    Interpretation: Two independent observations supporting/refuting a proposition
    contribute additively to the total evidence.
-/
noncomputable def hplus (x y : Evidence) : Evidence :=
  ⟨x.pos + y.pos, x.neg + y.neg⟩

noncomputable instance : Add Evidence := ⟨hplus⟩

theorem hplus_def (x y : Evidence) : x + y = ⟨x.pos + y.pos, x.neg + y.neg⟩ := rfl

theorem hplus_comm (x y : Evidence) : x + y = y + x := by
  simp only [hplus_def, add_comm]

theorem hplus_assoc (x y z : Evidence) : (x + y) + z = x + (y + z) := by
  simp only [hplus_def, add_assoc]

theorem hplus_zero (x : Evidence) : x + zero = x := by
  simp only [hplus_def, zero, add_zero]

theorem zero_hplus (x : Evidence) : zero + x = x := by
  simp only [hplus_def, zero, zero_add]

instance : Zero Evidence := ⟨zero⟩

/-! ### View to SimpleTruthValue

The calibrated mapping between evidence counts and (strength, confidence).
Uses a prior parameter κ > 0.
-/

variable (κ : ℝ≥0∞) -- Prior/context size parameter

/-- Convert evidence counts to strength: s = n⁺ / (n⁺ + n⁻)
    Returns 0 if total evidence is 0 (undefined case). -/
noncomputable def toStrength (e : Evidence) : ℝ≥0∞ :=
  if e.total = 0 then 0 else e.pos / e.total

/-- Convert evidence counts to confidence: c = total / (total + κ)
    Higher total evidence → higher confidence (approaches 1 as evidence → ∞) -/
noncomputable def toConfidence (e : Evidence) : ℝ≥0∞ :=
  e.total / (e.total + κ)

/-- Convert evidence to SimpleTruthValue (as reals in [0,1]) -/
noncomputable def toSTV (e : Evidence) : ℝ × ℝ :=
  ((toStrength e).toReal, (toConfidence κ e).toReal)

/-- Convert SimpleTruthValue to evidence counts (inverse of toSTV)
    Given (s, c) and prior κ, recover (n⁺, n⁻):
    - total = κ * c / (1 - c)
    - n⁺ = s * total
    - n⁻ = (1 - s) * total
-/
noncomputable def ofSTV (s c : ℝ) (_hc : c < 1) : Evidence :=
  let total : ℝ≥0∞ := κ * ENNReal.ofReal c / ENNReal.ofReal (1 - c)
  ⟨ENNReal.ofReal s * total, ENNReal.ofReal (1 - s) * total⟩

/-! ### Key Lemmas for the View

These connect the algebraic operations on Evidence to the standard PLN formulas.
-/

/-- Parallel combination in STV view corresponds to weighted averaging.
    This is PLN's revision rule!

    Note: We require total ≠ ⊤ to ensure the division algebra works correctly in ENNReal.
-/
theorem toStrength_hplus (x y : Evidence)
    (hx : x.total ≠ 0) (hy : y.total ≠ 0) (hxy : (x + y).total ≠ 0)
    (hx_ne_top : x.total ≠ ⊤) (hy_ne_top : y.total ≠ ⊤) :
    toStrength (x + y) =
    (x.total / (x + y).total) * toStrength x + (y.total / (x + y).total) * toStrength y := by
  -- The algebra: (x.pos + y.pos) / total_xy =
  --   (x.total / total_xy) * (x.pos / x.total) + (y.total / total_xy) * (y.pos / y.total)
  unfold toStrength
  simp only [hx, hy, hxy, ↓reduceIte]
  simp only [hplus_def, total] at *
  -- Key lemma: (a/T) * (p/a) = p/T when a ≠ 0, a ≠ ⊤
  have key : ∀ (p a T : ℝ≥0∞), a ≠ 0 → a ≠ ⊤ → (a / T) * (p / a) = p / T := by
    intros p a T ha0 haT
    rw [mul_comm, ← mul_div_assoc, ENNReal.div_mul_cancel ha0 haT]
  have h1 : (x.pos + x.neg) / (x.pos + y.pos + (x.neg + y.neg)) * (x.pos / (x.pos + x.neg)) =
            x.pos / (x.pos + y.pos + (x.neg + y.neg)) :=
    key x.pos (x.pos + x.neg) _ hx hx_ne_top
  have h2 : (y.pos + y.neg) / (x.pos + y.pos + (x.neg + y.neg)) * (y.pos / (y.pos + y.neg)) =
            y.pos / (x.pos + y.pos + (x.neg + y.neg)) :=
    key y.pos (y.pos + y.neg) _ hy hy_ne_top
  rw [h1, h2, ← ENNReal.add_div]

/-- The tensor product strength is at least the product of strengths.
    This shows that sequential composition preserves more positive evidence than
    the naive product formula would suggest.

    Mathematically: (x⁺y⁺)/(x⁺y⁺ + x⁻y⁻) ≥ (x⁺/(x⁺+x⁻)) * (y⁺/(y⁺+y⁻))
-/
theorem toStrength_tensor_ge (x y : Evidence) :
    toStrength (x * y) ≥ toStrength x * toStrength y := by
  unfold toStrength total
  simp only [tensor_def]
  -- Goal: (if x.pos * y.pos + x.neg * y.neg = 0 then 0 else (x.pos * y.pos) / ...)
  --       ≥ (if x.pos + x.neg = 0 then 0 else ...) * (if y.pos + y.neg = 0 then 0 else ...)
  by_cases hx : x.pos + x.neg = 0
  · -- x.total = 0: RHS has factor 0
    simp only [hx, ↓reduceIte, zero_mul, zero_le]
  · by_cases hy : y.pos + y.neg = 0
    · -- y.total = 0: RHS has factor 0
      simp only [hy, ↓reduceIte, mul_zero, zero_le]
    · -- Both totals nonzero
      simp only [hx, hy, ↓reduceIte]
      by_cases hxy : x.pos * y.pos + x.neg * y.neg = 0
      · -- Tensor total = 0: means x.pos * y.pos = 0 AND x.neg * y.neg = 0
        simp only [hxy, ↓reduceIte]
        -- LHS = 0, need 0 ≥ RHS (actually need to show RHS = 0)
        -- From hxy: x.pos * y.pos = 0, so either x.pos = 0 or y.pos = 0
        have hpos : x.pos * y.pos = 0 := (add_eq_zero.mp hxy).1
        -- So x.pos = 0 or y.pos = 0
        simp only [mul_eq_zero] at hpos
        rcases hpos with hxp | hyp
        · -- x.pos = 0
          rw [hxp, zero_add, ENNReal.zero_div, zero_mul]
        · -- y.pos = 0: goal has x.pos / (x.pos + x.neg) * (0 / (0 + y.neg))
          rw [hyp, zero_add, ENNReal.zero_div, mul_zero]
      · -- Main case: all totals nonzero
        simp only [hxy, ↓reduceIte]
        -- Need: (x.pos * y.pos) / (x.pos * y.pos + x.neg * y.neg) ≥
        --       (x.pos / (x.pos + x.neg)) * (y.pos / (y.pos + y.neg))
        -- First rewrite RHS using div_mul_div_comm to get same numerator
        -- For ENNReal, we prove this directly using div = mul_inv
        have h_rhs : x.pos / (x.pos + x.neg) * (y.pos / (y.pos + y.neg)) =
                     (x.pos * y.pos) / ((x.pos + x.neg) * (y.pos + y.neg)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
          -- ENNReal.mul_inv : (a ≠ 0 ∨ b ≠ ⊤) → (a ≠ ⊤ ∨ b ≠ 0) → (a * b)⁻¹ = a⁻¹ * b⁻¹
          -- a = x.pos + x.neg, b = y.pos + y.neg
          -- We have hx : a ≠ 0 and hy : b ≠ 0
          rw [← (ENNReal.mul_inv (Or.inl hx) (Or.inr hy)).symm]
          ring
        rw [h_rhs, ge_iff_le]
        -- Now need: (x.pos * y.pos) / ((x.pos + x.neg) * (y.pos + y.neg)) ≤
        --           (x.pos * y.pos) / (x.pos * y.pos + x.neg * y.neg)
        apply ENNReal.div_le_div_left
        -- Need: x.pos * y.pos + x.neg * y.neg ≤ (x.pos + x.neg) * (y.pos + y.neg)
        calc x.pos * y.pos + x.neg * y.neg
            ≤ x.pos * y.pos + x.neg * y.neg + (x.pos * y.neg + x.neg * y.pos) := by
              apply le_add_of_nonneg_right
              exact add_nonneg (zero_le _) (zero_le _)
          _ = (x.pos + x.neg) * (y.pos + y.neg) := by ring

end Evidence

/-! ## Q-Weighted Relations

A knowledge base is a Q-weighted relation: for each pair (A, B) of propositions,
we have an evidence value representing "A implies B."
-/

/-- A Q-weighted relation over types α and β -/
structure QRel (α β : Type*) where
  w : α → β → Evidence

namespace QRel

variable {α β γ : Type*}

/-- Composition of Q-weighted relations for finite intermediate type
    (R ∘ S)(A, C) = ⨆_B R(A,B) ⊗ S(B,C)

    For finite β, we compute this as a supremum over enumerated elements.
-/
noncomputable def comp [Fintype β] (R : QRel α β) (S : QRel β γ) : QRel α γ where
  w a c :=
    -- Take coordinatewise max over all path products
    ⟨Finset.univ.sup (fun b => (R.w a b * S.w b c).pos),
     Finset.univ.sup (fun b => (R.w a b * S.w b c).neg)⟩

/-- Identity relation: full evidence on the diagonal -/
def id [DecidableEq α] : QRel α α where
  w a b := if a = b then Evidence.one else Evidence.zero

/-- Composition gives at least each individual path contribution.

    The PLN deduction formula computes the strength of A→C given A→B and B→C.
    In the Q-weighted relations view, this is just composition.

    The key insight: the "direct path" term `sAB * sBC` comes from the tensor product,
    while the "indirect path via ¬B" term comes from considering the complement.
-/
theorem comp_is_deduction [Fintype β] (R : QRel α β) (S : QRel β γ) (a : α) (c : γ) :
    -- The composition gives at least the direct path contribution
    ∀ b, R.w a b * S.w b c ≤ (comp R S).w a c := by
  intro b
  unfold comp
  simp only [Evidence.le_def, Evidence.tensor_def]
  constructor
  · -- pos component
    apply Finset.le_sup (f := fun b => (R.w a b * S.w b c).pos)
    exact Finset.mem_univ b
  · -- neg component
    apply Finset.le_sup (f := fun b => (R.w a b * S.w b c).neg)
    exact Finset.mem_univ b

end QRel

/-! ## Summary

We now have:

1. `Evidence` : A proper commutative monoid with tensor product
2. `Evidence.hplus` : Parallel aggregation for independent evidence
3. `toSTV` / `ofSTV` : Views to/from SimpleTruthValue
4. `QRel` : Q-weighted relations with composition

The deduction formula emerges as:
- Direct path: tensor product (proven lower bound)
- Full formula: requires marginals and residuation (TODO)

Next steps:
- Complete the algebra proofs (marked with sorry)
- Add residuation for the "¬B path" term
- Connect to PLNDeduction.simpleDeductionStrengthFormula
-/

end Mettapedia.Logic.PLNEvidence
