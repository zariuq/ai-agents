import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSimpleTerms

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

universe u v w

namespace SimpleSubst

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {Γ Δ : List (SimpleTy Base)} {τ : SimpleTy Base}

/-- The head term of a substitution into an extended context. -/
def head (σs : SimpleSubst Base Const (τ :: Γ) Δ) : SimpleTerm Base Const Δ τ :=
  σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ)

@[simp] theorem head_cons (t : SimpleTerm Base Const Δ τ) (σs : SimpleSubst Base Const Γ Δ) :
    head (cons t σs) = t :=
  rfl

/-- Any substitution into an extended context is determined by its head and tail. -/
@[simp] theorem cons_head_tail (σs : SimpleSubst Base Const (τ :: Γ) Δ)
    {υ : SimpleTy Base} (x : SimpleVar Base (τ :: Γ) υ) :
    cons (head σs) (tail σs) x = σs x := by
  cases x <;> rfl

/-- Substitutions into the empty context carry no data. -/
def toEmptyEquivPUnit (Base : Type u) (Const : Mettapedia.Logic.HOL.Ty Base → Type v)
    (Δ : List (SimpleTy Base)) :
    SimpleSubst Base Const [] Δ ≃ PUnit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => fun {_} x => nomatch x
  left_inv := by
    intro σs
    funext τ x
    cases x
  right_inv := by
    intro u
    cases u
    rfl

/--
Substitutions into an extended context are equivalently a head term together
with a tail substitution.
-/
def splitEquiv (Base : Type u) (Const : Mettapedia.Logic.HOL.Ty Base → Type v)
    (Γ : List (SimpleTy Base)) (τ : SimpleTy Base) (Δ : List (SimpleTy Base)) :
    SimpleSubst Base Const (τ :: Γ) Δ ≃
      (SimpleTerm Base Const Δ τ × SimpleSubst Base Const Γ Δ) where
  toFun := fun σs => (head σs, (tail σs : SimpleSubst Base Const Γ Δ))
  invFun := fun p => (cons p.1 p.2 : SimpleSubst Base Const (τ :: Γ) Δ)
  left_inv := by
    intro σs
    funext υ x
    exact cons_head_tail (σs := σs) x
  right_inv := by
    intro p
    rcases p with ⟨t, σs⟩
    rfl

@[simp] theorem splitEquiv_apply
    (σs : SimpleSubst Base Const (τ :: Γ) Δ) :
    splitEquiv Base Const Γ τ Δ σs = (head σs, (tail σs : SimpleSubst Base Const Γ Δ)) :=
  rfl

@[simp] theorem splitEquiv_symm_apply
    (t : SimpleTerm Base Const Δ τ) (σs : SimpleSubst Base Const Γ Δ)
    {υ : SimpleTy Base} (x : SimpleVar Base (τ :: Γ) υ) :
    (splitEquiv Base Const Γ τ Δ).symm (t, σs) x = cons t σs x :=
  rfl

end SimpleSubst

namespace SimpleTopologicalInterpretation

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

namespace SimpleSubst

variable {I : SimpleTopologicalInterpretation Base Const X}
variable {Γ Δ : List (SimpleTy Base)} {τ : SimpleTy Base}

@[simp] theorem eval_splitEquiv
    (σs : Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst Base Const (τ :: Γ) Δ) :
    CtxHom.splitEquiv I Δ τ Γ (eval I σs) =
      (SimpleTerm.eval I (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.head σs),
        eval I (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.tail σs)) := by
  simp [CtxHom.splitEquiv, eval,
    Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.head]

@[simp] theorem eval_splitEquiv_symm
    (t : SimpleTerm Base Const Δ τ)
    (σs : Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst Base Const Γ Δ) :
    eval I (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.cons t σs) =
      (CtxHom.splitEquiv I Δ τ Γ).symm (SimpleTerm.eval I t, eval I σs) := by
  rfl

end SimpleSubst

end SimpleTopologicalInterpretation

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
