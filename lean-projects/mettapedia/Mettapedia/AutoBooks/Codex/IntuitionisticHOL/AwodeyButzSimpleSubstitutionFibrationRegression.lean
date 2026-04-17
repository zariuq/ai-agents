import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSimpleSubstitutionFibration
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSimpleTermsRegression

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

namespace AwodeyButzSimpleSubstitutionFibrationRegression

open SimpleTopologicalInterpretation
open AwodeyButzGenericPredicatesRegression
open AwodeyButzSimpleTermsRegression

abbrev DBase := AwodeyButzGenericPredicatesRegression.DemoBase
abbrev DConst := AwodeyButzGenericPredicatesRegression.DemoConst

local notation "atomTy" => (SimpleTy.base AwodeyButzGenericPredicatesRegression.DemoBase.atom)

def emptySynSubst : SimpleSubst DBase DConst [] [] :=
  SimpleSubst.id (Base := DBase) (Const := DConst) (Γ := [])

def atomEmptySubst : SimpleSubst DBase DConst [atomTy] [] :=
  SimpleSubst.cons atomConstTerm emptySynSubst

def truthWeakTerm : SimpleTerm DBase DConst [.prop, atomTy] .prop :=
  .const AwodeyButzGenericPredicatesRegression.DemoConst.truth

theorem toEmptyEquivPUnit_emptySynSubst :
    SimpleSubst.toEmptyEquivPUnit DBase DConst [] emptySynSubst = PUnit.unit :=
  rfl

theorem toEmptyEquivPUnit_symm_unit :
    SimpleSubst.toEmptyEquivPUnit DBase DConst []
      ((SimpleSubst.toEmptyEquivPUnit DBase DConst []).symm PUnit.unit) = PUnit.unit :=
  rfl

theorem splitEquiv_propAtomSynSubst :
    SimpleSubst.splitEquiv DBase DConst [atomTy] .prop [] propAtomSynSubst =
      (truthConstTerm, (atomEmptySubst : SimpleSubst DBase DConst [atomTy] [])) :=
  rfl

theorem splitEquiv_symm_propAtomSynSubst_vz :
    (SimpleSubst.splitEquiv DBase DConst [atomTy] .prop []).symm
      (truthConstTerm, (atomEmptySubst : SimpleSubst DBase DConst [atomTy] []))
      (SimpleVar.vz : SimpleVar DBase [.prop, atomTy] .prop) =
      truthConstTerm :=
  rfl

theorem splitEquiv_symm_propAtomSynSubst_vs :
    (SimpleSubst.splitEquiv DBase DConst [atomTy] .prop []).symm
      (truthConstTerm, (atomEmptySubst : SimpleSubst DBase DConst [atomTy] []))
      (SimpleVar.vs (SimpleVar.vz : SimpleVar DBase [atomTy] atomTy)) =
      atomConstTerm :=
  rfl

theorem splitEquiv_roundtrip_propAtomSynSubst_vz :
    (SimpleSubst.splitEquiv DBase DConst [atomTy] .prop []).symm
      ((SimpleSubst.splitEquiv DBase DConst [atomTy] .prop []) propAtomSynSubst)
      (SimpleVar.vz : SimpleVar DBase [.prop, atomTy] .prop) =
      propAtomSynSubst (SimpleVar.vz : SimpleVar DBase [.prop, atomTy] .prop) :=
  rfl

theorem splitEquiv_roundtrip_propAtomSynSubst_vs :
    (SimpleSubst.splitEquiv DBase DConst [atomTy] .prop []).symm
      ((SimpleSubst.splitEquiv DBase DConst [atomTy] .prop []) propAtomSynSubst)
      (SimpleVar.vs (SimpleVar.vz : SimpleVar DBase [atomTy] atomTy)) =
      propAtomSynSubst
        (SimpleVar.vs (SimpleVar.vz : SimpleVar DBase [atomTy] atomTy)) :=
  rfl

theorem head_propWeakSubst :
    SimpleSubst.head propWeakSubst = propVarTerm :=
  rfl

theorem head_propWeakSubst_ne_truthWeakTerm :
    SimpleSubst.head propWeakSubst ≠ truthWeakTerm := by
  intro h
  cases h

theorem eval_splitEquiv_propAtomSynSubst :
    CtxHom.splitEquiv demoInterp [] .prop [atomTy]
        (SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp propAtomSynSubst) =
      (truthTerm,
        SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp
          (SimpleSubst.tail propAtomSynSubst)) := by
  exact
    SimpleTopologicalInterpretation.SimpleSubst.eval_splitEquiv
      (I := demoInterp) (σs := propAtomSynSubst)

theorem eval_splitEquiv_symm_propAtomTail :
    SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp propAtomSynSubst =
      (CtxHom.splitEquiv demoInterp [] .prop [atomTy]).symm
        (truthTerm,
          SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp
            (SimpleSubst.tail propAtomSynSubst)) := by
  change
    SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp
        (SimpleSubst.cons truthConstTerm (SimpleSubst.tail propAtomSynSubst)) =
      (CtxHom.splitEquiv demoInterp [] .prop [atomTy]).symm
        (SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp truthConstTerm,
          SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp
            (SimpleSubst.tail propAtomSynSubst))
  simpa [propAtomSynSubst] using
    (SimpleTopologicalInterpretation.SimpleSubst.eval_splitEquiv_symm
      (I := demoInterp) (t := truthConstTerm) (σs := SimpleSubst.tail propAtomSynSubst))

end AwodeyButzSimpleSubstitutionFibrationRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
