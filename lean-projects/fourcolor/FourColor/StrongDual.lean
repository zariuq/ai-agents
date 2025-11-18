import FourColor.Triangulation
import FourColor.KernelExtras

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false


namespace FourColor

open scoped BigOperators
open Classical

noncomputable section

/-!
# Strong Dual and Orthogonality

This module establishes the **Strong Dual** property (Theorem 4.9 in the paper):
zero-boundary chains are orthogonal to the annihilator of the face boundary span.

The key insight: if generators `{∂f}` are orthogonal to some y, then any
finite XOR-sum of those generators is also orthogonal to y (by linearity of
chainDot). Combined with Lemma 4.5 (zeroBoundarySet ⊆ faceBoundarySpan),
this yields zeroBoundarySet ⊆ (annihilator of generators)⊥.

## Main definitions

* `isOrthogonalTo`: x ⊥ y when chainDot x y = 0
* `annihilatorOf`: the set of chains orthogonal to a given set
* `strongDualProperty`: zeroBoundarySet ⊆ annihilator⊥ of face generators

## Main results

* `chainDot_sum_left`: chainDot distributes over finite sums on the left
* `chainDot_sum_right`: chainDot distributes over finite sums on the right
* `span_orthogonal_to`: if generators are orthogonal to y, so is their span
* `strongDual_from_facialBasis`: Lemma 4.5 + generator orthogonality ⟹ Strong Dual

-/

section Orthogonality

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Two chains are orthogonal when their dot product is zero. -/
def isOrthogonalTo (x y : E → Color) : Prop :=
  Color.chainDot x y = 0

notation:50 x " ⊥ " y => isOrthogonalTo x y

/-- The annihilator of a set S: all chains orthogonal to every element of S. -/
def annihilatorOf (S : Set (E → Color)) : Set (E → Color) :=
  {y | ∀ x ∈ S, x ⊥ y}

notation:50 S "⊥" => annihilatorOf S

/-- The orthogonal complement of the annihilator (the "double orthogonal"). -/
def doubleOrthogonal (S : Set (E → Color)) : Set (E → Color) :=
  annihilatorOf (annihilatorOf S)

notation:50 S "⊥⊥" => doubleOrthogonal S

namespace Orthogonal

/-- Orthogonality is symmetric. -/
lemma symm {x y : E → Color} (h : x ⊥ y) : y ⊥ x := by
  unfold isOrthogonalTo Color.chainDot at *
  simp only [Color.dot_comm]
  exact h

/-- The zero chain is orthogonal to everything. -/
@[simp]
lemma zero_left (y : E → Color) : (zeroChain (E := E)) ⊥ y := by
  unfold isOrthogonalTo
  simp [Color.chainDot, zeroChain, Color.dot_zero_left]

@[simp]
lemma zero_right (x : E → Color) : x ⊥ (zeroChain (E := E)) := by
  exact symm (zero_left x)

/-- If x ⊥ y and x ⊥ z, then x ⊥ (y + z). -/
lemma add_right {x y z : E → Color} (hy : x ⊥ y) (hz : x ⊥ z) :
    x ⊥ (y + z) := by
  unfold isOrthogonalTo at *
  simp [Color.chainDot_add_right, hy, hz]

/-- If x ⊥ z and y ⊥ z, then (x + y) ⊥ z. -/
lemma add_left {x y z : E → Color} (hx : x ⊥ z) (hy : y ⊥ z) :
    (x + y) ⊥ z := by
  unfold isOrthogonalTo at *
  simp [Color.chainDot_add_left, hx, hy]

/-- chainDot of zero chain on left is zero. -/
lemma chainDot_zero_left (y : E → Color) :
    Color.chainDot (zeroChain (E := E)) y = 0 := by
  unfold Color.chainDot zeroChain
  simp [Color.dot_zero_left]

/-- chainDot distributes over finite sums on the left. -/
lemma chainDot_sum_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (f : ι → E → Color) (y : E → Color) :
    Color.chainDot (∑ i ∈ S, f i) y = ∑ i ∈ S, Color.chainDot (f i) y := by
  classical
  induction' S using Finset.induction with i S hi ih
  · simp only [Finset.sum_empty]
    exact chainDot_zero_left y
  · calc
      Color.chainDot (∑ j ∈ insert i S, f j) y
          = Color.chainDot (f i + ∑ j ∈ S, f j) y := by
              simp [Finset.sum_insert hi]
      _ = Color.chainDot (f i) y + Color.chainDot (∑ j ∈ S, f j) y := by
              simp [Color.chainDot_add_left]
      _ = Color.chainDot (f i) y + ∑ j ∈ S, Color.chainDot (f j) y := by
              simp [ih]
      _ = ∑ j ∈ insert i S, Color.chainDot (f j) y := by
              simp [Finset.sum_insert hi]

/-- chainDot with zero chain on right is zero. -/
lemma chainDot_zero_right (x : E → Color) :
    Color.chainDot x (zeroChain (E := E)) = 0 := by
  unfold Color.chainDot zeroChain
  simp [Color.dot_zero_right]

/-- chainDot distributes over finite sums on the right. -/
lemma chainDot_sum_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : E → Color) (S : Finset ι) (f : ι → E → Color) :
    Color.chainDot x (∑ i ∈ S, f i) = ∑ i ∈ S, Color.chainDot x (f i) := by
  classical
  induction' S using Finset.induction with i S hi ih
  · simp only [Finset.sum_empty]
    exact chainDot_zero_right x
  · calc
      Color.chainDot x (∑ j ∈ insert i S, f j)
          = Color.chainDot x (f i + ∑ j ∈ S, f j) := by
              simp [Finset.sum_insert hi]
      _ = Color.chainDot x (f i) + Color.chainDot x (∑ j ∈ S, f j) := by
              simp [Color.chainDot_add_right]
      _ = Color.chainDot x (f i) + ∑ j ∈ S, Color.chainDot x (f j) := by
              simp [ih]
      _ = ∑ j ∈ insert i S, Color.chainDot x (f j) := by
              simp [Finset.sum_insert hi]

/-- If each generator in S is orthogonal to y, then any finite sum of
generators from S is also orthogonal to y. -/
lemma sum_orthogonal_of_each {ι : Type*} [Fintype ι] [DecidableEq ι]
    {generators : ι → E → Color} {S : Finset ι} {y : E → Color}
    (h : ∀ i ∈ S, (generators i) ⊥ y) :
    (∑ i ∈ S, generators i) ⊥ y := by
  unfold isOrthogonalTo
  -- Delegate to chainDot_sum_left_vanish from KernelExtras
  exact chainDot_sum_left_vanish (E := E) (z := y) (f := generators) (S := S) h

end Orthogonal

end Orthogonality

section StrongDual

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- If face boundary generators are orthogonal to y, then their entire span
is orthogonal to y. This is the key linearity step for the Strong Dual. -/
lemma faceBoundarySpan_orthogonal_of_generators
    {γ : Color} {faces : Finset (Finset E)} {y : E → Color}
    (h : ∀ f ∈ faces, isOrthogonalTo (faceBoundaryChain (γ := γ) f) y) :
    ∀ x ∈ faceBoundarySpan γ faces, isOrthogonalTo x y := by
  intro x ⟨S, hS, hx⟩
  rw [hx]
  apply Orthogonal.sum_orthogonal_of_each
  intro f hf
  exact h f (hS hf)

/-- **Theorem 4.9 (Strong Dual Property)**: If the zero-boundary set lies in
the face boundary span (Lemma 4.5) and face boundaries are orthogonal to some
set of generators, then the zero-boundary set is orthogonal to those generators.

This establishes that zeroBoundarySet ⊆ S⊥⊥ when face boundaries ⊆ S⊥,
which is the foundation for the Kauffman reachability argument. -/
theorem strongDual_from_facialBasis
    (dual : LeafPeelData V E)
    (generators : Set (E → Color))
    (h_orth : ∀ f ∈ dual.internalFaces,
      ∀ g ∈ generators, isOrthogonalTo (faceBoundaryChain (γ := dual.gamma) f) g) :
    ∀ x ∈ dual.zero.zeroBoundarySet,
      ∀ g ∈ generators, isOrthogonalTo x g := by
  intro x hx g hg
  -- By Lemma 4.5, x is in the face boundary span
  have : x ∈ faceBoundarySpan dual.gamma dual.internalFaces :=
    dual.facialBasis_zeroBoundary_in_span hx
  -- Unpack the span: x = ∑_{f∈S} faceBoundaryChain γ f for some S ⊆ faces
  rcases this with ⟨S, hS, hx_sum⟩
  rw [hx_sum]
  -- Each face boundary in the sum is orthogonal to g
  apply Orthogonal.sum_orthogonal_of_each
  intro f hf
  exact h_orth f (hS hf) g hg

/-- Corollary: zeroBoundarySet is contained in the double orthogonal of
the face boundary generators. -/
theorem zeroBoundarySet_subset_doubleOrthogonal
    (dual : LeafPeelData V E) :
    dual.zero.zeroBoundarySet ⊆
      doubleOrthogonal {x | ∃ f ∈ dual.internalFaces,
        x = faceBoundaryChain (γ := dual.gamma) f} := by
  intro x hx
  unfold doubleOrthogonal annihilatorOf
  intro y hy
  -- y is in the annihilator of face boundaries, i.e., ∂f ⊥ y for all f
  -- We need to show y ⊥ x (note: annihilator definition has x ⊥ y order)
  -- By Lemma 4.5, x is in the face boundary span
  have hspan : x ∈ faceBoundarySpan dual.gamma dual.internalFaces :=
    dual.facialBasis_zeroBoundary_in_span hx
  -- Each face boundary is orthogonal to y (from hy)
  have h_orth : ∀ f ∈ dual.internalFaces, isOrthogonalTo (faceBoundaryChain (γ := dual.gamma) f) y := by
    intro f hf
    have hmem : faceBoundaryChain (γ := dual.gamma) f ∈ {x | ∃ f ∈ dual.internalFaces, x = faceBoundaryChain (γ := dual.gamma) f} := by
      simp only [Set.mem_setOf]
      exact ⟨f, hf, rfl⟩
    exact hy (faceBoundaryChain (γ := dual.gamma) f) hmem
  -- Therefore x (which is in the span) is also orthogonal to y
  have : isOrthogonalTo x y := faceBoundarySpan_orthogonal_of_generators h_orth x hspan
  exact Orthogonal.symm this

end StrongDual

end -- noncomputable section

end FourColor
