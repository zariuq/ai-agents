import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzTypedContexts

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

universe u v w

namespace SimpleTopologicalInterpretation

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

/--
Predicates in context are exactly terms of proposition type in that context.

This is the first live Jacobs-style bridge from the Awodey-Butz topological
route to a fibred higher-order logic viewpoint.
-/
abbrev Pred
    (I : SimpleTopologicalInterpretation Base Const X)
    (Γ : List (SimpleTy Base)) : Type _ :=
  I.CtxTerm Γ .prop

/-- The generic variable in an extended context is the head projection. -/
def genericVar
    (I : SimpleTopologicalInterpretation Base Const X)
    (τ : SimpleTy Base) (Γ : List (SimpleTy Base)) :
    I.CtxTerm (τ :: Γ) τ :=
  CtxTerm.head I τ Γ

/-- The generic proposition in an extended context. -/
abbrev genericProp
    (I : SimpleTopologicalInterpretation Base Const X)
    (Γ : List (SimpleTy Base)) : I.Pred (.prop :: Γ) :=
  genericVar I .prop Γ

namespace CtxHom

variable {I : SimpleTopologicalInterpretation Base Const X}
variable {Γ Δ : List (SimpleTy Base)} {τ : SimpleTy Base}

/--
The generic variable together with weakening reconstructs the identity on an
extended context.
-/
@[simp] theorem cons_head_tail (I : SimpleTopologicalInterpretation Base Const X)
    (τ : SimpleTy Base) (Γ : List (SimpleTy Base)) :
    CtxTerm.cons (CtxTerm.head I τ Γ) (tail I τ Γ) = id I (τ :: Γ) := by
  ext x
  apply Subtype.ext
  apply Prod.ext <;> rfl

/--
Any substitution into an extended context is determined by its head term and
its tail substitution.
-/
@[simp] theorem cons_reconstruct (σ : I.CtxHom Γ (τ :: Δ)) :
    CtxTerm.cons ((CtxTerm.head I τ Δ).reindex σ) (σ.comp (tail I τ Δ)) = σ := by
  ext x
  apply Subtype.ext
  apply Prod.ext <;> rfl

end CtxHom

namespace CtxTerm

variable {I : SimpleTopologicalInterpretation Base Const X}
variable {Γ Δ : List (SimpleTy Base)} {τ υ : SimpleTy Base}

/-- Weaken a term by adding a new head variable to the context. -/
def weaken (t : I.CtxTerm Γ τ) (υ : SimpleTy Base) :
    I.CtxTerm (υ :: Γ) τ :=
  t.reindex (CtxHom.tail I υ Γ)

@[simp] theorem weaken_apply (t : I.CtxTerm Γ τ) (υ : SimpleTy Base)
    (x : (I.ctxSpace (υ :: Γ)).Carrier) :
    (t.weaken υ).toContinuousMap x = t.toContinuousMap ((CtxHom.tail I υ Γ).toContinuousMap x) :=
  rfl

@[simp] theorem genericVar_reindex_cons
    (t : I.CtxTerm Γ τ) (σ : I.CtxHom Γ Δ) :
    (genericVar I τ Δ).reindex (cons t σ) = t := by
  unfold genericVar
  exact head_reindex_cons (I := I) t σ

@[simp] theorem genericProp_reindex_cons
    (p : I.Pred Γ) (σ : I.CtxHom Γ Δ) :
    (genericProp I Δ).reindex (cons p σ) = p := by
  unfold genericProp genericVar
  exact genericVar_reindex_cons (I := I) (τ := .prop) p σ

end CtxTerm

end SimpleTopologicalInterpretation

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
