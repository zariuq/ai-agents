import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzExponential
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzFullTypedContexts
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzTypedFragment

/-!
# Full Typed Topological Interpretation

This file extends the simple typed fragment to interpret the full HOL type syntax,
including arrow types via exponential étale spaces.

## Main Definitions

* `TopologicalInterpretation` - Full interpretation of HOL types as étale spaces
* `TopologicalInterpretation.space` - Interprets any type τ as an étale space
* `TopologicalInterpretation.ctxSpace` - Interprets contexts as iterated fiber products
* `TopologicalInterpretation.termInterpretation` - Interprets terms in context

## Key Construction

For arrow types `τ → υ`, the interpretation is:
  `⟦τ → υ⟧ = exp(⟦τ⟧, ⟦υ⟧)`

where `exp` is the exponential (internal hom) of étale spaces.

## References

* Awodey-Butz (2000), "Topological Completeness for Higher-Order Logic", Section 3
-/

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL
open Function TopologicalSpace TopologicalSpace.Opens Topology CategoryTheory

universe u v w

/--
Full topological interpretation of HOL types as étale spaces.

This extends `SimpleTopologicalInterpretation` to handle arrow types by using
exponential étale spaces.
-/
structure TopologicalInterpretation
    (Base : Type u) (Const : Ty Base → Type v)
    (X : Type w) [TopologicalSpace X]
    extends EtaleSpace.BasicTopologicalInterpretation Base Const X where
  /-- Interpretation of the proposition type. -/
  propSpace : EtaleSpace X
  /-- Interpretation of base types. -/
  baseSpace : Base → EtaleSpace X
  /-- The proposition type is interpreted by `propSpace`. -/
  space_prop : space .prop = propSpace
  /-- Base types are interpreted by `baseSpace`. -/
  space_base : ∀ b : Base, space (.base b) = baseSpace b
  /-- Arrow types are interpreted by exponential etale spaces. -/
  space_arr : ∀ τ υ : Ty Base, space (.arr τ υ) = EtaleSpace.exp (space τ) (space υ)

attribute [simp] TopologicalInterpretation.space_prop
attribute [simp] TopologicalInterpretation.space_base
attribute [simp] TopologicalInterpretation.space_arr

namespace TopologicalInterpretation

variable {I : TopologicalInterpretation Base Const X}
variable {X : Type w} [TopologicalSpace X]

/-- Restrict the full typed interpretation to the supported simple fragment. -/
noncomputable def constProp (I : TopologicalInterpretation Base Const X)
    (c : Const (.prop)) : I.propSpace.GlobalSection := by
  simpa using (I.const (τ := .prop) c)

/-- Restrict the full typed interpretation to a base-type constant. -/
noncomputable def constBase (I : TopologicalInterpretation Base Const X)
    {b : Base} (c : Const (.base b)) : (I.baseSpace b).GlobalSection := by
  simpa using (I.const (τ := .base b) c)

/-- Context interpretation, reusing the already-live full HOL context layer. -/
abbrev ctxSpace (I : TopologicalInterpretation Base Const X) :
    Ctx Base → EtaleSpace X :=
  EtaleSpace.BasicTopologicalInterpretation.ctxSpace I.toBasicTopologicalInterpretation

@[simp] theorem ctxSpace_nil (I : TopologicalInterpretation Base Const X) :
    I.ctxSpace [] = EtaleSpace.terminal X := by
  simpa [TopologicalInterpretation.ctxSpace] using
    EtaleSpace.BasicTopologicalInterpretation.ctxSpace_nil I.toBasicTopologicalInterpretation

@[simp] theorem ctxSpace_cons (I : TopologicalInterpretation Base Const X)
    (τ : Ty Base) (Γ : Ctx Base) :
    I.ctxSpace (τ :: Γ) = EtaleSpace.prod (I.space τ) (I.ctxSpace Γ) := by
  simpa [TopologicalInterpretation.ctxSpace] using
    EtaleSpace.BasicTopologicalInterpretation.ctxSpace_cons
      I.toBasicTopologicalInterpretation τ Γ

/-- Context morphisms over the already-live full HOL context interpretation. -/
abbrev CtxHom (I : TopologicalInterpretation Base Const X)
    (Γ Δ : Ctx Base) :=
  EtaleSpace.BasicTopologicalInterpretation.CtxHom I.toBasicTopologicalInterpretation Γ Δ

/-- Context-indexed terms over the already-live full HOL context interpretation. -/
abbrev CtxTerm (I : TopologicalInterpretation Base Const X)
    (Γ : Ctx Base) (τ : Ty Base) :=
  EtaleSpace.BasicTopologicalInterpretation.CtxTerm I.toBasicTopologicalInterpretation Γ τ

namespace CtxHom

variable {Γ Δ Ξ : Ctx Base}

/-- Identity context morphism. -/
abbrev id (I : TopologicalInterpretation Base Const X) (Γ : Ctx Base) :
    I.CtxHom Γ Γ :=
  EtaleSpace.BasicTopologicalInterpretation.CtxHom.id I.toBasicTopologicalInterpretation Γ

/-- Composition of context morphisms. -/
abbrev comp (σ : I.CtxHom Γ Δ) (ρ : I.CtxHom Δ Ξ) : I.CtxHom Γ Ξ :=
  EtaleSpace.BasicTopologicalInterpretation.CtxHom.comp σ ρ

@[simp] theorem id_apply (x : (I.ctxSpace Γ).Carrier) :
    (CtxHom.id I Γ).toContinuousMap x = x := by
  rfl

end CtxHom

namespace CtxTerm

variable {Γ Δ : Ctx Base} {τ υ : Ty Base}

/-- Reindex a term along a context morphism. -/
abbrev reindex (t : I.CtxTerm Δ τ) (σ : I.CtxHom Γ Δ) : I.CtxTerm Γ τ :=
  EtaleSpace.BasicTopologicalInterpretation.CtxTerm.reindex t σ

/-- The head variable of a nonempty context (de Bruijn index 0). -/
abbrev var0 (I : TopologicalInterpretation Base Const X)
    (τ : Ty Base) (Γ : Ctx Base) :
    I.CtxTerm (τ :: Γ) τ :=
  EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
    I.toBasicTopologicalInterpretation τ Γ

/--
Lambda abstraction: given a term `t : Γ, τ ⊢ υ`, produce a term `λ t : Γ ⊢ τ → υ`.

This uses currying in the category of étale spaces.
-/
noncomputable def lam {I : TopologicalInterpretation Base Const X}
    {Γ : Ctx Base} {τ υ : Ty Base}
    (t : I.CtxTerm (τ :: Γ) υ) :
    I.CtxTerm Γ (.arr τ υ) := by
  let f : C((EtaleSpace.prod (I.ctxSpace Γ) (I.space τ)).Carrier, (I.space υ).Carrier) :=
    t.toContinuousMap.comp (EtaleSpace.prodSwap (I.ctxSpace Γ) (I.space τ))
  have hf : (I.space υ).proj ∘ f = (EtaleSpace.prod (I.ctxSpace Γ) (I.space τ)).proj := by
    funext p
    have ht := congrFun t.proj_comp (EtaleSpace.prodSwap (I.ctxSpace Γ) (I.space τ) p)
    simp only [f, Function.comp_apply] at ht ⊢
    exact ht.trans (EtaleSpace.prodSwap_proj (I.ctxSpace Γ) (I.space τ) p)
  refine
    { toContinuousMap := ?_
      proj_comp := ?_ }
  · simpa using
      (EtaleSpace.curry f hf :
        C((I.ctxSpace Γ).Carrier, (EtaleSpace.exp (I.space τ) (I.space υ)).Carrier))
  · funext x
    simpa using congrFun (EtaleSpace.curry_proj f hf) x

/--
Application: given terms `f : Γ ⊢ τ → υ` and `a : Γ ⊢ τ`, produce `f a : Γ ⊢ υ`.

This uses evaluation in the category of étale spaces.
-/
noncomputable def app {I : TopologicalInterpretation Base Const X}
    {Γ : Ctx Base} {τ υ : Ty Base}
    (f : I.CtxTerm Γ (.arr τ υ))
    (a : I.CtxTerm Γ τ) :
    I.CtxTerm Γ υ := by
  let fExp : C((I.ctxSpace Γ).Carrier, (EtaleSpace.exp (I.space τ) (I.space υ)).Carrier) := by
    simpa using f.toContinuousMap
  have hfExp :
      (EtaleSpace.exp (I.space τ) (I.space υ)).proj ∘ fExp = (I.ctxSpace Γ).proj := by
    funext γ
    simpa [fExp] using congrFun f.proj_comp γ
  -- Projection compatibility for pairing f and a
  have hp : ∀ γ : (I.ctxSpace Γ).Carrier,
      (EtaleSpace.exp (I.space τ) (I.space υ)).proj (fExp γ) =
      (I.space τ).proj (a.toContinuousMap γ) := fun γ => by
    have hf := congrFun hfExp γ
    have ha := congrFun a.proj_comp γ
    exact hf.trans ha.symm
  -- The pair map (f, a) : Γ → exp(τ, υ) ×_X τ
  let pair :
      C((I.ctxSpace Γ).Carrier,
        (EtaleSpace.prod (EtaleSpace.exp (I.space τ) (I.space υ)) (I.space τ)).Carrier) :=
    ⟨fun γ => ⟨(fExp γ, a.toContinuousMap γ), hp γ⟩,
    (f.toContinuousMap.continuous.prodMk a.toContinuousMap.continuous).subtype_mk (hp ·)⟩
  exact {
    toContinuousMap := (EtaleSpace.evalMorphism (I.space τ) (I.space υ)).comp pair
    proj_comp := by
      funext γ
      have hEval := EtaleSpace.evalMorphism_proj (I.space τ) (I.space υ) (pair γ)
      simp only [Function.comp_apply, ContinuousMap.coe_comp] at hEval ⊢
      exact hEval.trans (congrFun hfExp γ)
  }

end CtxTerm

/--
Convert a full topological interpretation to a simple one (forgetting arrow type support).
-/
def toSimple (I : TopologicalInterpretation Base Const X) :
    SimpleTopologicalInterpretation Base Const X where
  propSpace := I.propSpace
  baseSpace := I.baseSpace
  constProp := I.constProp
  constBase := fun c => I.constBase c

/--
The full interpretation agrees with the simple interpretation on supported types.
-/
theorem space_eq_simple_space (I : TopologicalInterpretation Base Const X)
    (τ : SimpleTy Base) :
    I.space τ.toTy = I.toSimple.space τ := by
  cases τ <;> simp [SimpleTopologicalInterpretation.space, TopologicalInterpretation.toSimple]

end TopologicalInterpretation

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
