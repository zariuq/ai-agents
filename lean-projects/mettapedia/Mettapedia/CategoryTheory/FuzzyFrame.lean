import Mathlib.Order.Heyting.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Order.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Literature.Residuated

/-!
# The Unit Interval [0,1] as a Frame

This file proves that the unit interval [0,1] ⊂ ℝ forms a Frame
(complete Heyting algebra), which we use as the fiber for PLN truth values.

## Main Result

We prove that `unitInterval := {x : ℝ | 0 ≤ x ∧ x ≤ 1}` has:
1. Complete lattice structure (inf, sup, Inf, Sup)
2. Heyting implication (⇨)
3. Frame law: a ⊓ sSup S = sSup ((a ⊓ ·) '' S)

## Fuzzy Logic Interpretation

For fuzzy logic / many-valued logic:
- Meet (⊓): Product t-norm `a ⊓ b = a * b` (or min)
- Join (⊔): `a ⊔ b = max a b`
- Implication (⇨): Gödel implication `a ⇨ b = if a ≤ b then 1 else b/a`
  (or Łukasiewicz: `min(1, 1 - a + b)`)

## References

- Hájek, "Metamathematics of Fuzzy Logic" (1998)
- Goguen, "L-fuzzy sets" (1967)
- Wikipedia: T-norm fuzzy logics
-/

namespace Mettapedia.CategoryTheory.FuzzyFrame

open Set Classical

/-! ## Step 1: Define the Unit Interval

We use a subtype of ℝ for the unit interval.
-/

/-- The unit interval [0,1] as a subtype of ℝ -/
def UnitInterval : Type := {x : ℝ // 0 ≤ x ∧ x ≤ 1}

notation "𝕀" => UnitInterval

namespace UnitInterval

/-- Extensionality for unit interval -/
@[ext]
theorem ext {a b : 𝕀} (h : a.val = b.val) : a = b := Subtype.ext h

/-- Coercion to ℝ -/
instance : Coe 𝕀 ℝ := ⟨Subtype.val⟩

/-- Zero in the unit interval -/
def zero : 𝕀 := ⟨0, by norm_num, by norm_num⟩

/-- One in the unit interval -/
def one : 𝕀 := ⟨1, by norm_num, by norm_num⟩

instance : Zero 𝕀 := ⟨zero⟩
instance : One 𝕀 := ⟨one⟩

/-- Decidable equality for unit interval -/
noncomputable instance : DecidableEq 𝕀 := inferInstance

/-- Order on the unit interval (inherited from ℝ) -/
instance : LE 𝕀 := ⟨fun a b => a.val ≤ b.val⟩

/-- Partial order on the unit interval -/
instance : PartialOrder 𝕀 where
  le := fun a b => a.val ≤ b.val
  le_refl a := le_refl a.val
  le_trans a b c := le_trans
  le_antisymm a b hab hba := by
    ext
    exact le_antisymm hab hba

/-! ## Step 2: Lattice Operations

We define meet (min) and join (max).
-/

/-- Meet: minimum of two values -/
def inf (a b : 𝕀) : 𝕀 :=
  ⟨min a.val b.val, by
    constructor
    · exact le_min a.prop.1 b.prop.1
    · exact min_le_iff.mpr (Or.inl a.prop.2)⟩

/-- Join: maximum of two values -/
def sup (a b : 𝕀) : 𝕀 :=
  ⟨max a.val b.val, by
    constructor
    · exact le_max_iff.mpr (Or.inl a.prop.1)
    · exact max_le a.prop.2 b.prop.2⟩

instance : Min 𝕀 := ⟨inf⟩
instance : Max 𝕀 := ⟨sup⟩

/-- The unit interval is a bounded lattice -/
instance : BoundedOrder 𝕀 where
  top := one
  le_top a := a.prop.2
  bot := zero
  bot_le a := a.prop.1

/-! ## Step 3: Complete Lattice Structure

We define Inf and Sup for arbitrary sets.
-/

/-- Infimum of a set in `[0,1]`, computed via `sInf` on the real image. -/
noncomputable def sInf' (S : Set 𝕀) : 𝕀 :=
  by
    classical
    by_cases h : S.Nonempty
    · let T : Set ℝ := Subtype.val '' S
      have hTnonempty : T.Nonempty := by
        rcases h with ⟨x, hx⟩
        exact ⟨x.val, ⟨x, hx, rfl⟩⟩
      have hTbdd : BddBelow T := by
        refine ⟨0, ?_⟩
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact x.prop.1
      have h0 : 0 ≤ sInf T := by
        exact le_csInf hTnonempty (by
          intro y hy
          rcases hy with ⟨x, hx, rfl⟩
          exact x.prop.1)
      have h1 : sInf T ≤ 1 := by
        rcases hTnonempty with ⟨y, hy⟩
        exact (csInf_le hTbdd hy).trans (by
          rcases hy with ⟨x, hx, rfl⟩
          exact x.prop.2)
      exact ⟨sInf T, ⟨h0, h1⟩⟩
    · -- Empty set has Inf = ⊤.
      exact one

/-- Supremum of a set in `[0,1]`, computed via `sSup` on the real image. -/
noncomputable def sSup' (S : Set 𝕀) : 𝕀 :=
  by
    classical
    by_cases h : S.Nonempty
    · let T : Set ℝ := Subtype.val '' S
      have hTnonempty : T.Nonempty := by
        rcases h with ⟨x, hx⟩
        exact ⟨x.val, ⟨x, hx, rfl⟩⟩
      have hTbdd : BddAbove T := by
        refine ⟨1, ?_⟩
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact x.prop.2
      have h0 : 0 ≤ sSup T := by
        rcases hTnonempty with ⟨y, hy⟩
        have hy0 : 0 ≤ y := by
          rcases hy with ⟨x, hx, rfl⟩
          exact x.prop.1
        exact hy0.trans (le_csSup hTbdd hy)
      have h1 : sSup T ≤ 1 := by
        exact csSup_le hTnonempty (by
          intro y hy
          rcases hy with ⟨x, hx, rfl⟩
          exact x.prop.2)
      exact ⟨sSup T, ⟨h0, h1⟩⟩
    · -- Empty set has Sup = ⊥.
      exact zero

noncomputable instance : InfSet 𝕀 := ⟨sInf'⟩
noncomputable instance : SupSet 𝕀 := ⟨sSup'⟩

/-- `[0,1]` inherits a complete lattice structure from interval subtypes. -/
noncomputable instance : CompleteLattice 𝕀 := by
  change CompleteLattice (Set.Icc (0 : ℝ) 1)
  infer_instance

/-- `[0,1]` is a frame (finite meets distribute over arbitrary joins). -/
noncomputable instance : Order.Frame 𝕀 := by
  change Order.Frame (Set.Icc (0 : ℝ) 1)
  infer_instance

/-! ## Step 4: Product T-Norm (Meet for Fuzzy Logic)

For the quantale structure, we use the product t-norm as our meet.
This gives us the tensor product for the quantale.
-/

/-- Product t-norm: a ⊗ b = a * b -/
def product (a b : 𝕀) : 𝕀 :=
  ⟨a.val * b.val, by
    constructor
    · exact mul_nonneg a.prop.1 b.prop.1
    · calc a.val * b.val
        _ ≤ 1 * 1 := mul_le_mul a.prop.2 b.prop.2 b.prop.1 (by norm_num)
        _ = 1 := by norm_num⟩

instance : Mul 𝕀 := ⟨product⟩

@[simp] theorem product_val (a b : 𝕀) : (a * b).val = a.val * b.val := rfl

/-- Product is commutative -/
theorem product_comm (a b : 𝕀) : a * b = b * a := by
  ext
  exact mul_comm a.val b.val

/-- Product is associative -/
theorem product_assoc (a b c : 𝕀) : a * b * c = a * (b * c) := by
  ext
  exact mul_assoc a.val b.val c.val

/-- One is the unit for product -/
theorem product_one (a : 𝕀) : a * 1 = a := by
  ext
  exact mul_one a.val

/-- One is the left unit for product. -/
theorem one_product (a : 𝕀) : (1 : 𝕀) * a = a := by
  ext
  exact one_mul a.val

instance : CommMonoid 𝕀 where
  mul := (· * ·)
  one := 1
  mul_assoc := product_assoc
  one_mul := one_product
  mul_one := product_one
  mul_comm := product_comm

/-! ## Step 5: Heyting Implication

We use the Gödel implication: a ⇨ b = if a ≤ b then 1 else b/a
(But for product t-norm, we should use: a ⇨ b = min(1, b/a))
-/

/-- Gödel implication (residuation for min) -/
noncomputable def himp (a b : 𝕀) : 𝕀 :=
  if a.val ≤ b.val then
    one
  else
    b  -- For min-based logic

/-- Product implication (residuation for product t-norm) -/
noncomputable def productImp (a b : 𝕀) : 𝕀 :=
  if a.val = 0 then
    one
  else
    ⟨min 1 (b.val / a.val), by
      constructor
      · exact le_min (by norm_num) (div_nonneg b.prop.1 a.prop.1)
      · exact min_le_left 1 _⟩

@[simp] theorem productImp_val_of_eq (a b : 𝕀) (ha : a.val = 0) :
    (productImp a b).val = 1 := by
  simp [productImp, ha, one]

@[simp] theorem productImp_val_of_ne (a b : 𝕀) (ha : a.val ≠ 0) :
    (productImp a b).val = min 1 (b.val / a.val) := by
  simp [productImp, ha]

/-! ## Step 6: Frame Laws

We need to prove that the unit interval satisfies the Frame axioms.

The proofs are non-trivial and involve ℝ analysis. For theorems that
require these structures, we use section variables (explicit hypotheses)
rather than global axioms.
-/

/-! ## Step 7: Residuation for Product T-Norm

The key property: a * b ≤ c ↔ b ≤ a ⇨ c (where ⇨ is productImp).
-/

theorem product_residuation (a b c : 𝕀) :
    a * b ≤ c ↔ b ≤ productImp a c := by
  by_cases ha : a.val = 0
  · constructor
    · intro _
      change b.val ≤ (productImp a c).val
      simpa [productImp, ha] using b.prop.2
    · intro _
      change a.val * b.val ≤ c.val
      simpa [ha] using c.prop.1
  · have ha0 : 0 < a.val := lt_of_le_of_ne a.prop.1 (Ne.symm ha)
    constructor
    · intro hab
      change b.val ≤ (productImp a c).val
      rw [productImp_val_of_ne _ _ ha]
      refine le_min b.prop.2 ?_
      exact (le_div_iff₀ ha0).2 (by simpa [mul_comm] using hab)
    · intro hbc
      change a.val * b.val ≤ c.val
      have hbc' : b.val ≤ c.val / a.val := by
        have hmin : b.val ≤ min 1 (c.val / a.val) := by
          have hbval : b.val ≤ (productImp a c).val := hbc
          simpa [productImp, ha] using hbval
        exact (le_min_iff.mp hmin).2
      have hmul : b.val * a.val ≤ c.val := (le_div_iff₀ ha0).1 hbc'
      simpa [mul_comm] using hmul

/-- Product implication is right adjoint to product t-norm. -/
theorem productImp_adjoint (a b c : 𝕀) :
    a * b ≤ c ↔ b ≤ productImp a c :=
  product_residuation a b c

/-- Product t-norm is bounded by meet on `[0,1]`. -/
theorem product_le_inf (a b : 𝕀) : a * b ≤ a ⊓ b := by
  refine le_inf ?_ ?_
  · change a.val * b.val ≤ a.val
    exact mul_le_of_le_one_right a.prop.1 b.prop.2
  · change a.val * b.val ≤ b.val
    simpa [mul_comm] using (mul_le_of_le_one_right b.prop.1 a.prop.2)

noncomputable instance : Mettapedia.ProbabilityTheory.KnuthSkilling.Literature.ResiduatedMonoid 𝕀 where
  res := productImp
  adj := product_residuation

/-- Exchange law for product residuation:
`(a * b) ⇒ c = a ⇒ (b ⇒ c)`. -/
theorem productImp_exchange (a b c : 𝕀) :
    productImp (a * b) c = productImp a (productImp b c) := by
  simpa using
    (Mettapedia.ProbabilityTheory.KnuthSkilling.Literature.ResiduatedMonoidLemmas.exchange
      (α := 𝕀) a b c)

end UnitInterval

/-! ## Summary

We've defined the unit interval [0,1] with:
1. ✅ Basic structure (0, 1, min, max)
2. ✅ Product t-norm (multiplication)
3. ✅ Product implication operation
4. ✅ Complete lattice structure (via interval instance)
5. ✅ Frame structure (via interval instance)
6. ✅ Product-residuation law (`product_residuation`)

For now, this gives us enough structure to use [0,1] as the fiber
for PLN truth values in the lambda theory framework.
-/

end Mettapedia.CategoryTheory.FuzzyFrame
