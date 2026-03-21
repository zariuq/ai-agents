import Mathlib.Logic.Relation
import Mettapedia.GSLT.Core.GSLT

/-!
# GSLT: Paper-Aligned Abstract Framework

Paper-aligned presentation of Meredith (2026), Definitions 2.1–2.2.

This file layers on top of `Mettapedia.GSLT.Core.GSLT`:
- Re-exports the core GSLT definition (T, E, R triple with coherence)
- Connects `GSLT.MultiStep` to Mathlib's `Relation.ReflTransGen`
- Defines `GSLTHom` as a named alias for `GSLT.Morphism` (Def 2.2)

## References

- Meredith, "Computation, Causality, and Consciousness" (2026), §2, Defs 2.1–2.2
-/

namespace Mettapedia.GSLT.Meredith

open Mettapedia.GSLT

/-! ## Transitivity of Multi-Step Reduction -/

/-- Multi-step reduction is transitive.

    Needed to connect Mathlib's `tail`-cons `ReflTransGen` with the
    `head`-cons `GSLT.MultiStep`.
-/
theorem multiStep_trans (S : GSLT) {a b c : S.Term}
    (h1 : GSLT.MultiStep S a b) (h2 : GSLT.MultiStep S b c) : GSLT.MultiStep S a c := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact GSLT.MultiStep.step hs (ih h2)

/-! ## Mathlib-Standard Reflexive-Transitive Closure -/

/-- Multi-step reduction via Mathlib's `Relation.ReflTransGen`.

    Definition 2.1 (Meredith 2026): the rewrite relation R generates a
    reflexive-transitive closure on T/≡ used to define traces (Def 3.1)
    and causal structure. Using `ReflTransGen` gives access to Mathlib's
    rewriting library.
-/
def GSLTMultiStep (S : GSLT) : S.Term → S.Term → Prop :=
  Relation.ReflTransGen S.rewrites

/-- `GSLT.MultiStep` and `Relation.ReflTransGen` coincide.

    Both capture exactly the finite sequences of one-step rewrites.
    The difference is only in the direction of cons:
    - `MultiStep` is head-consing: step then rest
    - `ReflTransGen` is tail-appending: rest then step
-/
theorem multiStep_iff_reflTransGen (S : GSLT) (t u : S.Term) :
    GSLT.MultiStep S t u ↔ GSLTMultiStep S t u := by
  constructor
  · intro h
    induction h with
    | refl t => exact Relation.ReflTransGen.refl
    | step hs _ ih => exact Relation.ReflTransGen.head hs ih
  · intro h
    induction h with
    | refl => exact GSLT.MultiStep.refl _
    | tail htu hr ih =>
        exact multiStep_trans S ih (GSLT.MultiStep.step hr (GSLT.MultiStep.refl _))

/-! ## GSLT Homomorphisms -/

/-- A GSLT homomorphism: a bisimilarity-preserving map between GSLTs.

    Definition 2.2 (Meredith 2026): A morphism f : S → S' preserves
    bisimilarity — u₁ ∼ u₂ ⟹ f(u₁) ∼ f(u₂).

    This is a named alias for `GSLT.Morphism`.
-/
abbrev GSLTHom (S S' : GSLT) := GSLT.Morphism S S'

/-- The identity GSLT homomorphism. -/
def GSLTHom.id (S : GSLT) : GSLTHom S S := GSLT.Morphism.id S

/-- Composition of GSLT homomorphisms. -/
def GSLTHom.comp {S S' S'' : GSLT}
    (g : GSLTHom S' S'') (f : GSLTHom S S') : GSLTHom S S'' :=
  GSLT.Morphism.comp g f

/-- Identity is left-neutral for composition.

    `id ∘ f = f` for GSLT homomorphisms.
-/
theorem GSLTHom.id_comp {S S' : GSLT} (f : GSLTHom S S') :
    GSLTHom.comp (GSLTHom.id S') f = f :=
  GSLT.Morphism.id_comp f

/-- Identity is right-neutral for composition.

    `f ∘ id = f` for GSLT homomorphisms.
-/
theorem GSLTHom.comp_id {S S' : GSLT} (f : GSLTHom S S') :
    GSLTHom.comp f (GSLTHom.id S) = f :=
  GSLT.Morphism.comp_id f

/-- Composition of GSLT homomorphisms is associative. -/
theorem GSLTHom.comp_assoc {S₁ S₂ S₃ S₄ : GSLT}
    (h : GSLTHom S₃ S₄) (g : GSLTHom S₂ S₃) (f : GSLTHom S₁ S₂) :
    GSLTHom.comp h (GSLTHom.comp g f) = GSLTHom.comp (GSLTHom.comp h g) f :=
  rfl

end Mettapedia.GSLT.Meredith
