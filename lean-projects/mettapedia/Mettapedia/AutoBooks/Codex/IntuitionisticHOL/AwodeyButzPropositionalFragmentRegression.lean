import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzPropositionalFragment
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSimplePredicateSyntaxRegression

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

namespace AwodeyButzPropositionalFragmentRegression

open SimpleTopologicalInterpretation
open AwodeyButzGenericPredicatesRegression
open AwodeyButzSimpleTermsRegression
open AwodeyButzSimplePredicateSyntaxRegression

abbrev DBase := AwodeyButzGenericPredicatesRegression.DemoBase
abbrev DConst := AwodeyButzGenericPredicatesRegression.DemoConst

local notation "atomTy" => (SimpleTy.base AwodeyButzGenericPredicatesRegression.DemoBase.atom)

def demoPropInterp : SimplePropositionalInterpretation DBase DConst Bool where
  toSimple := demoInterp
  topPred := truthTerm
  botPred := truthTerm
  andPred := genericProp demoInterp [.prop]
  orPred := CtxTerm.var demoInterp
    (SimpleVar.vs (SimpleVar.vz : SimpleVar DBase [.prop] .prop))
  impPred := CtxTerm.const demoInterp [.prop, .prop] .prop
    AwodeyButzGenericPredicatesRegression.DemoConst.truth

def propAtomFormula : SimplePropFormula DBase DConst [.prop, atomTy] :=
  .atom propVarTerm

def truthFormula : SimplePropFormula DBase DConst [] :=
  .atom truthConstTerm

def conjFormula : SimplePropFormula DBase DConst [.prop, atomTy] :=
  .conj propAtomFormula .top

def implFormula : SimplePropFormula DBase DConst [.prop, atomTy] :=
  .impl .top propAtomFormula

theorem subst_propAtomFormula :
    SimplePropFormula.subst propAtomSynSubst propAtomFormula = .atom truthConstTerm :=
  rfl

theorem subst_conjFormula :
    SimplePropFormula.subst propAtomSynSubst conjFormula = .conj (.atom truthConstTerm) .top :=
  rfl

theorem subst_implFormula_ne_top :
    SimplePropFormula.subst propAtomSynSubst implFormula ≠ .top := by
  intro h
  cases h

theorem eval_propAtomFormula :
    SimplePropFormula.SimplePropositionalInterpretation.eval demoPropInterp propAtomFormula =
      SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp propVarTerm :=
  rfl

theorem eval_conjFormula :
    SimplePropFormula.SimplePropositionalInterpretation.eval demoPropInterp conjFormula =
      demoPropInterp.conj
        (SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp propVarTerm)
        (demoPropInterp.top [.prop, atomTy]) :=
  rfl

theorem eval_subst_conjFormula :
    SimplePropFormula.SimplePropositionalInterpretation.eval demoPropInterp
        (SimplePropFormula.subst propAtomSynSubst conjFormula) =
      (SimplePropFormula.SimplePropositionalInterpretation.eval demoPropInterp conjFormula).reindex
        (SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp propAtomSynSubst) := by
  exact
    SimplePropFormula.SimplePropositionalInterpretation.eval_subst
      (I := demoPropInterp) (σs := propAtomSynSubst) (φ := conjFormula)

theorem eval_subst_implFormula :
    SimplePropFormula.SimplePropositionalInterpretation.eval demoPropInterp
        (SimplePropFormula.subst propAtomSynSubst implFormula) =
      (SimplePropFormula.SimplePropositionalInterpretation.eval demoPropInterp implFormula).reindex
        (SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp propAtomSynSubst) := by
  exact
    SimplePropFormula.SimplePropositionalInterpretation.eval_subst
      (I := demoPropInterp) (σs := propAtomSynSubst) (φ := implFormula)

end AwodeyButzPropositionalFragmentRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
