import Mathlib.CategoryTheory.Category.Preorder
import Mettapedia.ProbabilityTheory.Hypercube.Taxonomy

/-!
# Weakness Order on Probability Hypercube Vertices

Goertzel’s Weakness notes define a “weakness preorder” on objects of a category:

> `C ⪯ D`  iff  there exists a morphism `C ⟶ D`,
> so `C` is *weaker / less restrictive* than `D`.

See `literature/Goertzel Articles/Weakness-Book/Weakness-Theory-10.tex` (Definition “Weakness Ordering”).

## This repo’s conventions

`Mettapedia/ProbabilityTheory/Hypercube/Taxonomy.lean` installs `≤` on `ProbabilityVertex` as the
**strength / specificity** order:

- `V ≤ W` means: `V` assumes *at least* the constraints that `W` assumes
  (equivalently, `W` is at least as weak/general as `V`).

This file packages the **Goertzel-style weakness order** as the order dual:

- `WeakVertex := ProbabilityVertexᵒᵈ`

Then the preorder-category structure on `WeakVertex` has morphisms exactly when the source vertex
is weaker than the target vertex, matching Goertzel’s `⪯`.

To use the infix notation `V ≼ W` in downstream files, `open scoped HypercubeWeakness`.
-/

namespace Mettapedia.ProbabilityTheory.Hypercube

open CategoryTheory

/-- Vertices equipped with the **strength/specificity** order from `Taxonomy.lean`. -/
abbrev StrengthVertex := ProbabilityVertex

/-- Vertices equipped with the **weakness** order (`OrderDual` of the strength order). -/
abbrev WeakVertex := StrengthVertexᵒᵈ

/-- Goertzel-style weakness predicate on vertices: “`V` is weaker than `W`”.

This is definitionally the same as `Basic.lean`’s `isMoreGeneral`.
-/
def IsWeaker (V W : StrengthVertex) : Prop :=
  isMoreGeneral V W

scoped[HypercubeWeakness] notation:50 V " ≼ " W =>
  _root_.Mettapedia.ProbabilityTheory.Hypercube.IsWeaker V W

open scoped HypercubeWeakness

/-- The weakness relation is the opposite of the strength-order `≤` (from `Taxonomy.lean`). -/
theorem isWeaker_iff_le (V W : StrengthVertex) : (V ≼ W) ↔ (W ≤ V) := by
  -- `W ≤ V ↔ isMoreGeneral V W` (Taxonomy), so just swap sides.
  simpa [IsWeaker] using (le_iff_isMoreGeneral (V := W) (W := V)).symm

/-- Weakness order equals the `≤` relation in the `OrderDual` poset. -/
theorem isWeaker_iff_dual_le (V W : StrengthVertex) :
    (V ≼ W) ↔ (OrderDual.toDual V : WeakVertex) ≤ OrderDual.toDual W := by
  -- In the order dual, `toDual V ≤ toDual W` is definitional to `W ≤ V`.
  simp [isWeaker_iff_le (V := V) (W := W)]

/-- In the weakness category (`WeakVertex` as a preorder category), a morphism exists
iff the source vertex is weaker than the target vertex. -/
theorem weakness_hom_nonempty_iff (V W : StrengthVertex) :
    Nonempty (OrderDual.toDual V ⟶ OrderDual.toDual W) ↔ (V ≼ W) := by
  constructor
  · rintro ⟨f⟩
    have hVW : (OrderDual.toDual V : WeakVertex) ≤ OrderDual.toDual W :=
      CategoryTheory.leOfHom f
    -- Convert the dual inequality back to the weakness predicate.
    exact (isWeaker_iff_dual_le (V := V) (W := W)).2 hVW
  · intro hVW
    have hVW' : (OrderDual.toDual V : WeakVertex) ≤ OrderDual.toDual W :=
      (isWeaker_iff_dual_le (V := V) (W := W)).1 hVW
    exact ⟨CategoryTheory.homOfLE hVW'⟩

end Mettapedia.ProbabilityTheory.Hypercube
