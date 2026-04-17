import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzPredicateFibration

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

universe u v w

/--
De Bruijn variables for the live simple typed fragment of the Awodey-Butz route.
-/
inductive SimpleVar (Base : Type u) : List (SimpleTy Base) → SimpleTy Base → Type u where
  | vz : SimpleVar Base (τ :: Γ) τ
  | vs : SimpleVar Base Γ τ → SimpleVar Base (υ :: Γ) τ

namespace SimpleTopologicalInterpretation

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

namespace CtxTerm

variable {I : SimpleTopologicalInterpretation Base Const X}
variable {Γ Δ : List (SimpleTy Base)} {τ υ : SimpleTy Base}

/-- Interpret a de Bruijn variable as a term in context. -/
def var (I : SimpleTopologicalInterpretation Base Const X) :
    {Γ : List (SimpleTy Base)} → {τ : SimpleTy Base} →
      SimpleVar Base Γ τ → I.CtxTerm Γ τ
  | _ :: _, _, .vz => genericVar I _ _
  | _ :: _, _, .vs x => (var I x).weaken _

@[simp] theorem var_vz (τ : SimpleTy Base) (Γ : List (SimpleTy Base)) :
    var I (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ) = genericVar I τ Γ :=
  rfl

@[simp] theorem var_vs (υ : SimpleTy Base) (x : SimpleVar Base Γ τ) :
    var I (SimpleVar.vs (υ := υ) x) = (var I x).weaken υ :=
  rfl

@[simp] theorem var_vz_reindex_cons
    (t : I.CtxTerm Δ τ) (σ : I.CtxHom Δ Γ) :
    (var I (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ)).reindex (cons t σ) = t := by
  exact genericVar_reindex_cons (I := I) (Γ := Δ) (Δ := Γ) (τ := τ) t σ

@[simp] theorem var_vs_reindex_cons
    (x : SimpleVar Base Γ υ) (t : I.CtxTerm Δ τ) (σ : I.CtxHom Δ Γ) :
    (var I (SimpleVar.vs (υ := τ) x)).reindex (cons t σ) = (var I x).reindex σ := by
  simp [weaken, reindex_comp]

end CtxTerm

end SimpleTopologicalInterpretation

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
