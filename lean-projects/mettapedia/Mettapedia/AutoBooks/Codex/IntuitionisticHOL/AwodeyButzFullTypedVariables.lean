import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Terms
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzFullTypedContexts

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w

namespace EtaleSpace.BasicTopologicalInterpretation

variable {Base : Type u} {Const : Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

namespace CtxTerm

variable {I : EtaleSpace.BasicTopologicalInterpretation Base Const X}
variable {Γ Δ : Ctx Base} {τ υ : Ty Base}

/-- Interpret a native de Bruijn variable as a term in context. -/
def var (I : EtaleSpace.BasicTopologicalInterpretation Base Const X) :
    {Γ : Ctx Base} → {τ : Ty Base} →
      Var Γ τ → I.CtxTerm Γ τ
  | _ :: _, _, .vz => head I _ _
  | _ :: _, _, .vs x => (var I x).weaken _

@[simp] theorem var_vz (τ : Ty Base) (Γ : Ctx Base) :
    var I (Var.vz : Var (τ :: Γ) τ) = head I τ Γ :=
  rfl

@[simp] theorem var_vs (υ : Ty Base) (x : Var Γ τ) :
    var I (Var.vs (σ := υ) x) = (var I x).weaken υ :=
  rfl

@[simp] theorem var_vz_reindex_cons
    (t : I.CtxTerm Δ τ) (σ : I.CtxHom Δ Γ) :
    (var I (Var.vz : Var (τ :: Γ) τ)).reindex (cons t σ) = t := by
  exact head_reindex_cons (I := I) (Γ := Δ) (Δ := Γ) (τ := τ) t σ

@[simp] theorem var_vs_reindex_cons
    (x : Var Γ υ) (t : I.CtxTerm Δ τ) (σ : I.CtxHom Δ Γ) :
    (var I (Var.vs (σ := τ) x)).reindex (cons t σ) = (var I x).reindex σ := by
  simp [weaken, reindex_comp]

end CtxTerm

end EtaleSpace.BasicTopologicalInterpretation

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
