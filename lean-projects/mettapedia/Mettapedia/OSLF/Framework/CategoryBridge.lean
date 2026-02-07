import Mettapedia.OSLF.Framework.DerivedModalities

/-!
# OSLF Category-Theoretic Bridge

This file documents the categorical interpretation of the OSLF construction
and how the concrete Set-level derivation (DerivedModalities.lean) relates to
the full categorical picture (GSLT/Core/).

## The Categorical Picture

In the topos-theoretic setting (Williams & Stay, "Native Type Theory"):

1. A lambda-theory T gives a presheaf topos T-hat = Set^{T^op}
2. The Yoneda embedding y : T -> T-hat sends each sort to its representable presheaf
3. The subobject functor Sub : T-hat -> Set sends each presheaf to its set of subobjects
4. The Native Type functor NT = integral (Sub . y) is the Grothendieck construction

## Modal Operators via Change-of-Base

Per OSLF section 4 + section 6:

The reduction relation R ⊆ Proc × Proc gives a span:

```
        E (reduction graph)
       / \
  src /   \ tgt
     /     \
    v       v
   Proc    Proc
```

The modal operators arise from change-of-base along this span:

  diamond(phi) = exists_src (pullback_tgt phi)  = exists_src . tgt*
  box(phi)     = forall_tgt (pullback_src phi)  = forall_tgt . src*

The Galois connection diamond -| box follows from composing adjunctions:
  diamond(phi) <= psi  <->  tgt*(phi) <= src*(psi)  <->  phi <= box(psi)

## What IS Proven (in DerivedModalities.lean)

The Set-level realization of this construction:

1. `di_pb_adj` / `pb_ui_adj`: The adjoint triple `exists_f -| f* -| forall_f`
   on `(X -> Prop)` fibers, for any function `f : E -> X`

2. `derived_galois`: For ANY `ReductionSpan`, the derived diamond/box form
   a Galois connection by composing the two adjunctions

3. `derived_diamond_eq_possiblyProp` / `derived_box_eq_relyProp`:
   For the rho-calculus span, the derived operators equal the hand-written ones

4. `rho_galois_from_span`: The rho-calculus Galois connection as a corollary

## Connection Points

- **GSLT/Core/LambdaTheoryCategory.lean**: Proper Mathlib-based SubobjectFibration with
  categories, CartesianMonoidalCategory, MonoidalClosed, HasFiniteLimits

- **GSLT/Core/ChangeOfBase.lean**: The adjoint triple exists_f -| f* -| forall_f
  at the categorical level, with `stepForward` and `secureStepForward`

- **Framework/DerivedModalities.lean**: The same adjoint triple at the Set level,
  with proven equivalence to possiblyProp/relyProp for the rho-calculus

## What Remains (Categorical Lifting)

To lift from Set-level (DerivedModalities) to full categorical (GSLT):

1. **Categorical RewriteSystem**: Embed RewriteSystem into a category with
   proper products, so the reduction span lives in the topos

2. **Reduction as morphism**: Express the reduction relation R as a
   subobject in the presheaf topos, giving the span `E -> Proc x Proc`

3. **Lifting theorem**: Show that the categorical `ChangeOfBase.stepForward`
   from GSLT/Core/ restricts to the Set-level `derivedDiamond` on fibers

4. **Beck-Chevalley**: Show the GSLT `BeckChevalley` condition holds for
   the OSLF span (enables substitution-commutes-with-modality)

## References

- Meredith & Stay, "Operational Semantics in Logical Form" sections 4, 6
- Williams & Stay, "Native Type Theory" (ACT 2021) section 3
- Johnstone, "Sketches of an Elephant" Vol 1, section 1.1
-/

namespace Mettapedia.OSLF.Framework.CategoryBridge

open Mettapedia.OSLF.Framework.DerivedModalities

/-! ## Re-export Key Results

The concrete derivation is in `DerivedModalities.lean`. We re-export
the key theorem here for visibility.
-/

/-- The generic Galois connection for any reduction span,
    proven by composing the adjoint triple `∃_f ⊣ f* ⊣ ∀_f`.
    See `DerivedModalities.derived_galois` for the proof. -/
example (span : ReductionSpan X) : GaloisConnection (derivedDiamond span) (derivedBox span) :=
  derived_galois span

/-- The rho-calculus Galois connection as a corollary of the generic construction.
    See `DerivedModalities.rho_galois_from_span` for the proof. -/
example : GaloisConnection
    Mettapedia.OSLF.RhoCalculus.Reduction.possiblyProp
    Mettapedia.OSLF.RhoCalculus.Reduction.relyProp :=
  rho_galois_from_span

end Mettapedia.OSLF.Framework.CategoryBridge
