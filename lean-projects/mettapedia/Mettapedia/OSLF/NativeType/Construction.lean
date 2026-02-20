import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Subobject.Basic
import Mettapedia.CategoryTheory.LambdaTheory

/-!
# Native Type Construction (Built on Mathlib + LambdaTheory)

This file formalizes the core construction from Williams & Stay's
"Native Type Theory" (ACT 2021), building on:

1. **Mathlib's CategoryTheory** - Yoneda, Subobject, Grothendieck
2. **Our LambdaTheory.lean** - SubobjectFibration with Frame fibers

## The NT Functor

The Native Type functor NT : λThyₑq^op → Topos is defined as:

  NT(T) = ∫ (Sub ∘ y)

where:
- T is a λ-theory (CCC with finite limits/colimits)
- y : T → Psh(T) is the Yoneda embedding
- Sub : Psh(T) → Set is the subobject functor
- ∫ is the Grothendieck construction

## Construction Strategy

We build NT in two layers:

1. **Abstract NT** (this file): Uses our SubobjectFibration from LambdaTheory.lean,
   which has Frame-structured fibers (complete Heyting algebras).

2. **Concrete NT**: Would use Mathlib's `CategoryTheory.Grothendieck` with
   a functor `Sub ∘ y : T ⥤ Cat` (requires more infrastructure).

## References

- Williams & Stay, "Native Type Theory" (ACT 2021) §3
- Meredith & Stay, "Operational Semantics in Logical Form"
- Johnstone, "Sketches of an Elephant" Vol 1, §1.1 (Grothendieck construction)
- Our LambdaTheory.lean for SubobjectFibration structure
-/

namespace Mettapedia.OSLF.NativeType

open CategoryTheory
open Mettapedia.CategoryTheory.LambdaTheories

/-! ## Native Types over a Lambda Theory

A native type is a pair (S, φ) where:
- S is a sort (object of the lambda theory's base)
- φ is a predicate (element of the fiber Sub(S))

This directly uses our SubobjectFibration structure from LambdaTheory.lean,
which gives us Frame-structured fibers (complete Heyting algebras).
-/

/-- A native type over a lambda theory L is a pair (S, φ) where
    S is a sort and φ is a predicate in the fiber over S.

    This is an object of the Grothendieck construction ∫ Sub.
-/
structure NatType (L : LambdaTheory) where
  /-- The underlying sort (base object) -/
  sort : L.Obj
  /-- The predicate (element of the fiber, which is a Frame) -/
  pred : L.fibration.Sub sort

namespace NatType

variable {L : LambdaTheory}

/-- The full type over a sort (⊤ in the fiber) -/
def full (S : L.Obj) : NatType L where
  sort := S
  pred := ⊤

/-- The empty type over a sort (⊥ in the fiber) -/
def empty (S : L.Obj) : NatType L where
  sort := S
  pred := ⊥

/-- Comprehension: restrict a native type by intersecting with a predicate.
    Uses meet (⊓) from the Frame structure. -/
def comprehension (A : NatType L) (φ : L.fibration.Sub A.sort) : NatType L where
  sort := A.sort
  pred := A.pred ⊓ φ

/-- Union of native types with the same sort.
    Uses join (⊔) from the Frame structure. -/
def union (A B : NatType L) (h : A.sort = B.sort) : NatType L where
  sort := A.sort
  pred := A.pred ⊔ (h ▸ B.pred)

/-- Arbitrary join of native types with the same sort.
    Uses sSup from the Frame (complete lattice) structure. -/
noncomputable def sSup' (S : L.Obj) (types : Set (L.fibration.Sub S)) : NatType L where
  sort := S
  pred := sSup types

end NatType

/-! ## Native Type Morphisms

For native types with the same sort, the morphisms are simply the
ordering on predicates (subobject inclusion).

For the full Grothendieck construction with different sorts,
we would need a base morphism f : S → S' and a proof that
the induced map preserves the predicate. See `NativeTypeTheory.lean`
for the PLN-specific version using Mathlib's category machinery.
-/

/-- Native types over a fixed sort S form a preorder via predicate inclusion.
    This is the fiber of the Grothendieck construction over S. -/
def NatTypeFiber (L : LambdaTheory) (S : L.Obj) := L.fibration.Sub S

instance (L : LambdaTheory) (S : L.Obj) : Preorder (NatTypeFiber L S) :=
  inferInstanceAs (Preorder (L.fibration.Sub S))

instance (L : LambdaTheory) (S : L.Obj) : PartialOrder (NatTypeFiber L S) :=
  inferInstanceAs (PartialOrder (L.fibration.Sub S))

/-- The fiber over S has Frame structure (complete Heyting algebra) -/
instance (L : LambdaTheory) (S : L.Obj) : Order.Frame (NatTypeFiber L S) :=
  L.fibration.frame S

/-- For same-sort native types, morphisms are predicate inclusion -/
def NatTypeLeq {L : LambdaTheory} (A B : NatType L) (h : A.sort = B.sort) : Prop :=
  A.pred ≤ (h ▸ B.pred)

theorem NatTypeLeq.refl {L : LambdaTheory} (A : NatType L) : NatTypeLeq A A rfl :=
  le_refl _

/-! ## Connection to Mathlib's Grothendieck Construction

To use Mathlib's `CategoryTheory.Grothendieck` directly, we would need:

1. A functor `SubFunctor : L.Obj ⥤ Cat` where `SubFunctor.obj S = L.fibration.Sub S`
2. This requires making each fiber into a category (poset category from Frame)
3. Then `Grothendieck SubFunctor` gives us the full construction

For now, our simplified construction suffices for connecting to OSLF semantics.
The key insight is that the Frame structure on fibers gives us all the
lattice operations needed for type formation rules.

### What Mathlib's Grothendieck Would Give Us

```
-- Pseudocode for full construction:
def SubFunctor (L : LambdaTheory) : L.Obj ⥤ Cat where
  obj S := Cat.of (L.fibration.Sub S)  -- Poset category
  map f := ... -- Change-of-base functor

def NT (L : LambdaTheory) : Type* := Grothendieck (SubFunctor L)
```

This would automatically give us:
- Objects: Sigma pairs (S, φ)
- Morphisms: Pairs (f, g) with coherence
- Category instance from Mathlib
- Functoriality of the construction

### Connection to Yoneda

For presheaf toposes (which is the setting of Native Type Theory),
Sub(P) is classified by morphisms P → Ω where Ω is the subobject classifier.

The key diagram:
```
        y
    T ────→ Psh(T)
            │
         Sub│
            ↓
           Set
```

Where `Sub ∘ y` sends each S : T to the set of subobjects of y(S).
-/

/-! ## Type Formation Rules

The Frame structure on fibers gives us the type formation rules from OSLF:
-/

section TypeFormation

variable (L : LambdaTheory)

/-- Σ-types (existential): join in the fiber -/
noncomputable def sigmaType (S : L.Obj) (types : Set (L.fibration.Sub S)) :
    L.fibration.Sub S :=
  sSup types

/-- Π-types (universal): meet in the fiber -/
noncomputable def piType (S : L.Obj) (types : Set (L.fibration.Sub S)) :
    L.fibration.Sub S :=
  sInf types

/-- Implication type: Heyting implication -/
def implType (S : L.Obj) (φ ψ : L.fibration.Sub S) : L.fibration.Sub S :=
  φ ⇨ ψ

/-- The key property: Heyting implication is right adjoint to meet.
    This is the residuation law that makes the fiber a quantale! -/
theorem impl_adjoint (S : L.Obj) (φ ψ χ : L.fibration.Sub S) :
    φ ⊓ ψ ≤ χ ↔ φ ≤ ψ ⇨ χ :=
  le_himp_iff.symm

end TypeFormation

/-! ## Theory Translation Contracts (Π/Ω Preservation)

This section makes the Native Type route explicit about what it means for a
theory translation to preserve:
- `Π` (fiber meets / `sInf`)
- `Ω`-truth (fiber top / `⊤`)

The contract is intentionally structural and sort-indexed so downstream
consumers can depend on a single endpoint theorem instead of ad-hoc wrappers.
-/

section TheoryMorphism

variable {L₁ L₂ : LambdaTheory}

/-- Native Type translation contract between lambda theories.

`mapPred` is sort-indexed and must preserve the key fiber operations used by
Native Type formation: arbitrary joins (`Σ`), arbitrary meets (`Π`), and top
(`Ω`-truth object in the fiber logic view). -/
structure TheoryMorphism (L₁ L₂ : LambdaTheory) where
  mapSort : L₁.Obj → L₂.Obj
  mapPred : ∀ {S : L₁.Obj}, L₁.fibration.Sub S → L₂.fibration.Sub (mapSort S)
  map_sSup :
    ∀ {S : L₁.Obj} (types : Set (L₁.fibration.Sub S)),
      mapPred (sSup types) = sSup (mapPred '' types)
  map_sInf :
    ∀ {S : L₁.Obj} (types : Set (L₁.fibration.Sub S)),
      mapPred (sInf types) = sInf (mapPred '' types)
  map_top :
    ∀ {S : L₁.Obj},
      mapPred (⊤ : L₁.fibration.Sub S) = (⊤ : L₂.fibration.Sub (mapSort S))

namespace TheoryMorphism

variable (F : TheoryMorphism L₁ L₂)

/-- Action on native types. -/
def mapNatType (A : NatType L₁) : NatType L₂ where
  sort := F.mapSort A.sort
  pred := F.mapPred A.pred

/-- Translation preserves Σ-types (`sSup`). -/
theorem preserves_sigmaType
    (S : L₁.Obj) (types : Set (L₁.fibration.Sub S)) :
    F.mapPred (sigmaType L₁ S types) =
      sigmaType L₂ (F.mapSort S) (F.mapPred '' types) := by
  simpa [sigmaType] using (F.map_sSup (S := S) types)

/-- Translation preserves Π-types (`sInf`). -/
theorem preserves_piType
    (S : L₁.Obj) (types : Set (L₁.fibration.Sub S)) :
    F.mapPred (piType L₁ S types) =
      piType L₂ (F.mapSort S) (F.mapPred '' types) := by
  simpa [piType] using (F.map_sInf (S := S) types)

/-- Translation preserves Ω-truth (`⊤`) at every sort. -/
theorem preserves_omegaTop (S : L₁.Obj) :
    F.mapPred (⊤ : L₁.fibration.Sub S) =
      (⊤ : L₂.fibration.Sub (F.mapSort S)) := by
  simpa using (F.map_top (S := S))

/-- Equivalent Ω-preservation phrasing at the `NatType.full` level. -/
theorem preserves_fullNatType_pred (S : L₁.Obj) :
    (F.mapNatType (NatType.full (L := L₁) S)).pred =
      (NatType.full (L := L₂) (F.mapSort S)).pred := by
  simpa [mapNatType, NatType.full] using F.preserves_omegaTop S

/-- Canonical Native Type translation endpoint for Π/Ω preservation.

This is the theorem-level contract consumed by FULLStatus/CoreMain: once a
translation satisfies `TheoryMorphism`, Π and Ω preservation are immediate. -/
theorem piOmega_translation_endpoint
    (S : L₁.Obj) (types : Set (L₁.fibration.Sub S)) :
    F.mapPred (piType L₁ S types) =
      piType L₂ (F.mapSort S) (F.mapPred '' types)
    ∧
    (F.mapNatType (NatType.full (L := L₁) S)).pred =
      (NatType.full (L := L₂) (F.mapSort S)).pred := by
  exact ⟨F.preserves_piType S types, F.preserves_fullNatType_pred S⟩

/-- Identity translation on a lambda theory satisfies the Π/Ω contract. -/
def id (L : LambdaTheory) : TheoryMorphism L L where
  mapSort := fun S => S
  mapPred := fun {_S} φ => φ
  map_sSup := by
    intro S types
    simp
  map_sInf := by
    intro S types
    simp
  map_top := by intro S; rfl

/-- Concrete sanity canary: the identity translation preserves Π/Ω by
definition. -/
theorem id_piOmega_translation_endpoint
    (L : LambdaTheory) (S : L.Obj) (types : Set (L.fibration.Sub S)) :
    (id L).mapPred (piType L S types) =
      piType L ((id L).mapSort S) ((id L).mapPred '' types)
    ∧
    ((id L).mapNatType (NatType.full (L := L) S)).pred =
      (NatType.full (L := L) ((id L).mapSort S)).pred := by
  simpa using (TheoryMorphism.piOmega_translation_endpoint (F := id L) S types)

end TheoryMorphism
end TheoryMorphism

/-! ## Modal Types (Placeholder)

Modal types ⟨Cj⟩_{xk::Ak} B from OSLF are constructed via comprehension.
The actual construction requires the reduction relation from the lambda theory.

See `Mettapedia/CategoryTheory/LambdaTheory.lean` for:
- `RewriteRule` - base rewrites
- `RewriteContext` - one-hole contexts
- `ModalTypeSpec` - specification of modal types
- `modalType` - construction of modal types
-/

/-! ## Summary

This file establishes the Native Type construction built on existing foundations:

1. **Uses LambdaTheory.lean**: SubobjectFibration with Frame fibers
2. **NatType**: Objects of NT as (sort, predicate) pairs
3. **Type formation**: Σ, Π, → via Frame operations (sSup, sInf, ⇨)
4. **Key insight**: Frame structure = complete Heyting algebra = quantale

**What's needed from Phases 1-2:**

### From Phase 1 (Categorical Foundations):
- Full λ-theory structure (CCC with finite limits/colimits)
- Currently we have simplified `LambdaTheory` with just objects and fibration
- Need: Morphisms, composition, Yoneda embedding

### From Phase 2 (Topos Structure):
- Change-of-base functors for SubobjectFibration
- Direct/inverse image adjunctions (∃f ⊣ f* ⊣ ∀f)
- Subobject classifier Ω with χ : Sub(P) ≅ Hom(P, Ω)

**What we have now:**
- ✅ Frame-structured fibers (complete Heyting algebras)
- ✅ NatType as (sort, predicate) pairs
- ✅ Type formation rules via Frame operations
- ✅ Residuation law (quantale structure)
- ✅ Connection to modal types via LambdaTheory.lean

**Next steps:**
- Add morphisms to LambdaTheory (making it a proper category)
- Connect to Mathlib's Yoneda for presheaf construction
- Use Mathlib's Grothendieck for full NT construction
-/

end Mettapedia.OSLF.NativeType
