import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.GSLT.Core.LambdaTheoryCategory
import Mathlib.CategoryTheory.Category.GaloisConnection
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# OSLF Category-Theoretic Bridge

Lifts the Set-level OSLF construction to categorical infrastructure
using Mathlib's `CategoryTheory` library.

## Main Results

1. **Monotonicity**: `langDiamond` and `langBox` are monotone (as
   left/right adjoints of a Galois connection).

2. **Modal adjunction**: The Galois connection `langDiamond ⊣ langBox`
   lifts to a categorical `Adjunction` between monotone functors on the
   predicate preorder category (via `GaloisConnection.adjunction`).

3. **Sort category**: For any `RewriteSystem`, the sorts form a discrete
   category `Discrete R.Sorts`.

4. **Predicate fibration**: Each sort `s` is assigned the fiber
   `R.Term s → Prop`, forming a `SubobjectFibration` over the sort category.

## The Categorical Picture

The reduction relation R gives a span:
```
        E (reduction graph)
       / \
  src /   \ tgt
     /     \
    v       v
   Proc    Proc
```

Modal operators arise from change-of-base along this span:
  diamond(phi) = exists_src . tgt*,  box(phi) = forall_tgt . src*

The Galois connection diamond -| box follows from composing adjunctions.
In a preorder category, this IS a categorical adjunction (Mathlib's
`GaloisConnection.adjunction`).

## References

- Meredith & Stay, "Operational Semantics in Logical Form" sections 4, 6
- Williams & Stay, "Native Type Theory" (ACT 2021) section 3
-/

namespace Mettapedia.OSLF.Framework.CategoryBridge

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ## Set-Level Results (from DerivedModalities.lean) -/

/-- The generic Galois connection for any reduction span. -/
example (span : ReductionSpan X) :
    GaloisConnection (derivedDiamond span) (derivedBox span) :=
  derived_galois span

/-- The rho-calculus Galois connection as a corollary. -/
example : GaloisConnection
    Mettapedia.OSLF.RhoCalculus.Reduction.possiblyProp
    Mettapedia.OSLF.RhoCalculus.Reduction.relyProp :=
  rho_galois_from_span

/-! ## Monotonicity of Modal Operators

A `GaloisConnection l u` implies `Monotone l` and `Monotone u`.
This is the first step toward viewing the modal operators as functors.
-/

/-- `langDiamond` is monotone: if φ ≤ ψ then ◇φ ≤ ◇ψ. -/
theorem langDiamond_monotone (lang : LanguageDef) :
    Monotone (langDiamond lang) :=
  (langGalois lang).monotone_l

/-- `langBox` is monotone: if φ ≤ ψ then □φ ≤ □ψ. -/
theorem langBox_monotone (lang : LanguageDef) :
    Monotone (langBox lang) :=
  (langGalois lang).monotone_u

/-- `possiblyProp` is monotone. -/
theorem possiblyProp_monotone :
    Monotone Mettapedia.OSLF.RhoCalculus.Reduction.possiblyProp :=
  rho_galois_from_span.monotone_l

/-- `relyProp` is monotone. -/
theorem relyProp_monotone :
    Monotone Mettapedia.OSLF.RhoCalculus.Reduction.relyProp :=
  rho_galois_from_span.monotone_u

/-! ## Categorical Lift: Galois Connection → Adjunction

A `GaloisConnection` between preorders lifts to a categorical `Adjunction`
between the associated preorder categories. Mathlib provides this via:
- `Monotone.functor`: monotone map → functor on preorder category
- `GaloisConnection.adjunction`: Galois connection → adjunction
- `Adjunction.gc`: adjunction → Galois connection (inverse direction)

The predicate type `(Pattern → Prop)` has a `CompleteLattice` structure
(hence `Preorder`), which gives it a thin category via
`Preorder.smallCategory`. However, `Pattern → Prop` also inherits a
`CategoryTheory.Pi` instance, creating an instance diamond.

To avoid this ambiguity, we use a dedicated type wrapper `PredLattice`
for the predicate preorder category.
-/

/-- The predicate lattice over Pattern, viewed as a preorder.

    Using `def` (not `abbrev`) prevents instance diamonds between
    `Preorder.smallCategory` and `CategoryTheory.Pi` on `Pattern → Prop`. -/
def PredLattice : Type := Pattern → Prop

noncomputable instance : CompleteLattice PredLattice := Pi.instCompleteLattice

/-- Wrap a predicate as a `PredLattice` element. -/
def PredLattice.mk (φ : Pattern → Prop) : PredLattice := φ

/-- Unwrap a `PredLattice` element to a predicate. -/
def PredLattice.get (φ : PredLattice) : Pattern → Prop := φ

/-- Lift `langDiamond` to operate on `PredLattice`. -/
def langDiamondL (lang : LanguageDef) : PredLattice → PredLattice :=
  fun φ => langDiamond lang φ.get

/-- Lift `langBox` to operate on `PredLattice`. -/
def langBoxL (lang : LanguageDef) : PredLattice → PredLattice :=
  fun φ => langBox lang φ.get

/-- The lifted langDiamond is monotone. -/
theorem langDiamondL_monotone (lang : LanguageDef) :
    Monotone (langDiamondL lang) := by
  intro φ ψ h
  exact (langGalois lang).monotone_l h

/-- The lifted langBox is monotone. -/
theorem langBoxL_monotone (lang : LanguageDef) :
    Monotone (langBoxL lang) := by
  intro φ ψ h
  exact (langGalois lang).monotone_u h

/-- The Galois connection lifts to `PredLattice`. -/
theorem langGaloisL (lang : LanguageDef) :
    GaloisConnection (langDiamondL lang) (langBoxL lang) := by
  intro φ ψ
  exact langGalois lang φ.get ψ.get

/-- The modal adjunction ◇ ⊣ □ for any `LanguageDef`, as a categorical
    `Adjunction` between endofunctors on the predicate preorder category.

    This lifts the order-theoretic Galois connection to category theory. -/
noncomputable def langModalAdjunction (lang : LanguageDef) :
    (langGaloisL lang).monotone_l.functor ⊣
    (langGaloisL lang).monotone_u.functor :=
  (langGaloisL lang).adjunction

/-- The rho-calculus modal adjunction: instantiate the generic one for `rhoCalc`. -/
noncomputable def rhoModalAdjunction :=
  langModalAdjunction rhoCalc

/-! ## Sort Category and Predicate Fibration

For any `RewriteSystem R`, we build:
1. A discrete category on `R.Sorts`
2. A `SubobjectFibration` assigning `(R.Term s → Prop)` to each sort `s`
-/

/-- The sort category: the discrete category on the sorts of a rewrite system.

    In the full topos-theoretic picture, this would be replaced by the
    lambda-theory category. The discrete category is the minimal categorical
    structure that assigns an object to each sort. -/
abbrev SortCategory (R : RewriteSystem) := CategoryTheory.Discrete R.Sorts

/-- The predicate fibration for a rewrite system.

    Each sort `s` is assigned the fiber `R.Term s → Prop` (predicates on
    terms at sort `s`), which is a `Frame` (complete Heyting algebra).

    This is the discrete approximation to the full subobject fibration
    `Sub : Set^{T^op} → Set` from Native Type Theory. -/
noncomputable def predFibration (R : RewriteSystem) :
    Mettapedia.GSLT.Core.SubobjectFibration (SortCategory R) where
  Sub := fun ⟨s⟩ => R.Term s → Prop
  frame := fun ⟨_⟩ => Pi.instFrame

/-- Construct a `SubobjectFibration` over the sort category from an
    `OSLFTypeSystem`, using the predicate types `sys.Pred s` as fibers. -/
def oslf_fibration (R : RewriteSystem) (sys : OSLFTypeSystem R) :
    Mettapedia.GSLT.Core.SubobjectFibration (SortCategory R) where
  Sub := fun ⟨s⟩ => sys.Pred s
  frame := fun ⟨s⟩ => sys.frame s

/-- The predicate fibration for the rho-calculus. -/
noncomputable def rhoPredFibration :
    Mettapedia.GSLT.Core.SubobjectFibration
      (SortCategory (langRewriteSystem rhoCalc "Proc")) :=
  predFibration (langRewriteSystem rhoCalc "Proc")

-- Verify the key constructions type-check
#check @langModalAdjunction
#check @rhoModalAdjunction
#check @predFibration
#check @oslf_fibration

/-! ## Summary

**0 sorries. 0 axioms.**

### Proven Results

1. **Monotonicity**: `langDiamond_monotone`, `langBox_monotone`,
   `possiblyProp_monotone`, `relyProp_monotone`
2. **Modal adjunction**: `langModalAdjunction` (for any `LanguageDef`),
   `rhoModalAdjunction` (for rho-calculus)
3. **Sort category**: `SortCategory R = Discrete R.Sorts`
4. **Predicate fibration**: `predFibration` and `oslf_fibration` construct
   `SubobjectFibration` instances over the sort category

### Connection to GSLT

The `SubobjectFibration` structure bridges to `GSLT/Core/`:
- `LambdaTheoryCategory.lean`: Defines `SubobjectFibration` with
  CartesianMonoidalCategory, MonoidalClosed, HasFiniteLimits
- `ChangeOfBase.lean`: The adjoint triple `∃_f ⊣ f* ⊣ ∀_f` at the
  categorical level

### What Remains (Full Topos Lift)

To go from discrete-category fibers to the full topos-theoretic picture:
1. Replace `Discrete R.Sorts` with a proper lambda-theory category
2. Express the reduction relation as a subobject in the presheaf topos
3. Show `ChangeOfBase.stepForward` restricts to `derivedDiamond` on fibers
4. Prove the Beck-Chevalley condition for substitution commutativity
-/

end Mettapedia.OSLF.Framework.CategoryBridge
