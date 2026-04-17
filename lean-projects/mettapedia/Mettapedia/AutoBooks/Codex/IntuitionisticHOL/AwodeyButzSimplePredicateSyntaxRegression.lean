import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSimplePredicateSyntax
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSimpleTermsRegression

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

namespace AwodeyButzSimplePredicateSyntaxRegression

open SimpleTopologicalInterpretation
open AwodeyButzGenericPredicatesRegression
open AwodeyButzSimpleTermsRegression

abbrev DBase := AwodeyButzGenericPredicatesRegression.DemoBase
abbrev DConst := AwodeyButzGenericPredicatesRegression.DemoConst

local notation "atomTy" => (SimpleTy.base AwodeyButzGenericPredicatesRegression.DemoBase.atom)

def truthWeakTerm : SimpleTerm DBase DConst [.prop, atomTy] .prop :=
  .const AwodeyButzGenericPredicatesRegression.DemoConst.truth

def propWeakTruthSubst : SimpleSubst DBase DConst [.prop] [.prop, atomTy] :=
  (SimpleTerm.predSubstEquiv DBase DConst [.prop, atomTy]).symm truthWeakTerm

theorem predSubstEquiv_propWeakSubst :
    SimpleTerm.predSubstEquiv DBase DConst [.prop, atomTy] propWeakSubst = propVarTerm :=
  rfl

theorem predSubstEquiv_symm_truthConst_vz :
    (SimpleTerm.predSubstEquiv DBase DConst []).symm truthConstTerm
      (SimpleVar.vz : SimpleVar DBase [.prop] .prop) = truthConstTerm :=
  rfl

theorem predSubstEquiv_symm_truthWeak_vz :
    propWeakTruthSubst (SimpleVar.vz : SimpleVar DBase [.prop] .prop) = truthWeakTerm :=
  rfl

theorem predSubstEquiv_propWeak_ne_truthWeak :
    SimpleTerm.predSubstEquiv DBase DConst [.prop, atomTy] propWeakSubst ≠ truthWeakTerm := by
  intro h
  cases h

theorem predContextEquiv_eval_propWeak :
    predContextEquiv demoInterp [.prop, atomTy]
        (SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp propWeakSubst) =
      SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp propVarTerm := by
  exact
    SimpleTopologicalInterpretation.SimpleSubst.predContextEquiv_eval
      (I := demoInterp) (σs := propWeakSubst)

theorem eval_predSubstEquiv_symm_truthWeak :
    SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp propWeakTruthSubst =
      (predContextEquiv demoInterp [.prop, atomTy]).symm
        (SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp truthWeakTerm) := by
  exact
    SimpleTopologicalInterpretation.SimpleSubst.eval_predSubstEquiv_symm
      (I := demoInterp) (p := truthWeakTerm)

end AwodeyButzSimplePredicateSyntaxRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
