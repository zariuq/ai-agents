import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSimpleSubstitutionFibration

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

universe u v w

namespace SimpleSubst

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {Γ : List (SimpleTy Base)}

/-- The unique substitution out of the empty context. -/
def empty (Base : Type u) (Const : Mettapedia.Logic.HOL.Ty Base → Type v)
    (Γ : List (SimpleTy Base)) : SimpleSubst Base Const [] Γ :=
  fun {_} x => nomatch x

@[simp] theorem toEmptyEquivPUnit_empty :
    toEmptyEquivPUnit Base Const Γ (empty Base Const Γ) = PUnit.unit :=
  rfl

@[simp] theorem toEmptyEquivPUnit_symm_unit_apply
    {τ : SimpleTy Base} (x : SimpleVar Base [] τ) :
    (toEmptyEquivPUnit Base Const Γ).symm PUnit.unit x = empty Base Const Γ x := by
  cases x

end SimpleSubst

namespace SimpleTerm

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {Γ : List (SimpleTy Base)}

/--
Syntactic proposition terms in context are equivalently substitutions into the
one-variable proposition context.
-/
def predSubstEquiv (Base : Type u) (Const : Mettapedia.Logic.HOL.Ty Base → Type v)
    (Γ : List (SimpleTy Base)) :
    SimpleSubst Base Const [.prop] Γ ≃ SimpleTerm Base Const Γ .prop where
  toFun := fun σs => SimpleSubst.head σs
  invFun := fun p => (SimpleSubst.cons p (SimpleSubst.empty Base Const Γ) :
    SimpleSubst Base Const [.prop] Γ)
  left_inv := by
    intro σs
    funext τ x
    cases x with
    | vz => rfl
    | vs x => cases x
  right_inv := by
    intro p
    rfl

@[simp] theorem predSubstEquiv_apply (σs : SimpleSubst Base Const [.prop] Γ) :
    predSubstEquiv Base Const Γ σs = SimpleSubst.head σs :=
  rfl

@[simp] theorem predSubstEquiv_symm_vz (p : SimpleTerm Base Const Γ .prop) :
    (predSubstEquiv Base Const Γ).symm p (SimpleVar.vz : SimpleVar Base [.prop] .prop) = p :=
  rfl

end SimpleTerm

namespace SimpleTopologicalInterpretation

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

namespace SimpleSubst

variable {I : SimpleTopologicalInterpretation Base Const X}
variable {Γ : List (SimpleTy Base)}

/--
Evaluating a syntactic substitution into the proposition context and then
classifying it semantically recovers the evaluation of its proposition term.
-/
@[simp] theorem predContextEquiv_eval
    (σs : Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst Base Const [.prop] Γ) :
    predContextEquiv I Γ (eval I σs) =
      SimpleTerm.eval I (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.head σs) := by
  simp [predContextEquiv, genericProp, genericVar,
    Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.head]

/--
The inverse syntactic predicate packaging evaluates to the inverse semantic
predicate classifier.
-/
@[simp] theorem eval_predSubstEquiv_symm
    (p : Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm Base Const Γ .prop) :
    eval I ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm.predSubstEquiv
      Base Const Γ).symm p) =
      (predContextEquiv I Γ).symm (SimpleTerm.eval I p) := by
  rfl

end SimpleSubst

end SimpleTopologicalInterpretation

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
