import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSimpleTerms
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzGenericPredicatesRegression

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

namespace AwodeyButzSimpleTermsRegression

open SimpleTopologicalInterpretation
open AwodeyButzGenericPredicatesRegression

def truthConstTerm : SimpleTerm DemoBase DemoConst [] .prop :=
  .const DemoConst.truth

def atomConstTerm : SimpleTerm DemoBase DemoConst [] (.base .atom) :=
  .const DemoConst.atomWitness

def propVarTerm : SimpleTerm DemoBase DemoConst [.prop, .base .atom] .prop :=
  .var (SimpleVar.vz : SimpleVar DemoBase [.prop, .base .atom] .prop)

def atomVarTerm : SimpleTerm DemoBase DemoConst [.prop, .base .atom] (.base .atom) :=
  .var (SimpleVar.vs (SimpleVar.vz : SimpleVar DemoBase [.base .atom] (.base .atom)))

def propSingleVarTerm : SimpleTerm DemoBase DemoConst [.prop] .prop :=
  .var (SimpleVar.vz : SimpleVar DemoBase [.prop] .prop)

def propAtomSynSubst : SimpleSubst DemoBase DemoConst [.prop, .base .atom] [] :=
  SimpleSubst.cons truthConstTerm
    (SimpleSubst.cons atomConstTerm
      (SimpleSubst.id (Base := DemoBase) (Const := DemoConst) (Γ := [])))

def propWeakSubst : SimpleSubst DemoBase DemoConst [.prop] [.prop, .base .atom]
  | _, .vz => propVarTerm

theorem eval_truthConstTerm :
    SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp truthConstTerm = truthTerm :=
  rfl

theorem eval_atomConstTerm :
    SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp atomConstTerm = atomTerm :=
  rfl

theorem subst_id_propSingleVar :
    SimpleTerm.subst (SimpleSubst.id (Base := DemoBase) (Const := DemoConst) (Γ := [.prop]))
      propSingleVarTerm = propSingleVarTerm :=
  rfl

theorem subst_propVar_propAtom :
    SimpleTerm.subst propAtomSynSubst propVarTerm = truthConstTerm :=
  rfl

theorem subst_atomVar_propAtom :
    SimpleTerm.subst propAtomSynSubst atomVarTerm = atomConstTerm :=
  rfl

theorem comp_propWeak_propAtom_vz :
    SimpleSubst.comp propWeakSubst propAtomSynSubst
      (SimpleVar.vz : SimpleVar DemoBase [.prop] .prop) = truthConstTerm :=
  rfl

theorem subst_comp_propSingleVar :
    SimpleTerm.subst propAtomSynSubst (SimpleTerm.subst propWeakSubst propSingleVarTerm) =
      SimpleTerm.subst (SimpleSubst.comp propWeakSubst propAtomSynSubst) propSingleVarTerm := by
  exact SimpleTerm.subst_comp (σs := propWeakSubst) (τs := propAtomSynSubst) propSingleVarTerm

theorem eval_propVar_propAtom :
    SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp
      (SimpleTerm.subst propAtomSynSubst propVarTerm) = truthTerm :=
  rfl

theorem eval_atomVar_propAtom :
    SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp
      (SimpleTerm.subst propAtomSynSubst atomVarTerm) = atomTerm :=
  rfl

theorem term_eval_subst_propVar :
    SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp
        (SimpleTerm.subst propAtomSynSubst propVarTerm) =
      (SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp propVarTerm).reindex
        (SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp propAtomSynSubst) := by
  exact
    (SimpleTopologicalInterpretation.SimpleSubst.term_eval_subst
      (I := demoInterp) (σs := propAtomSynSubst) (t := propVarTerm))

theorem term_eval_subst_atomVar :
    SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp
        (SimpleTerm.subst propAtomSynSubst atomVarTerm) =
      (SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp atomVarTerm).reindex
        (SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp propAtomSynSubst) := by
  exact
    (SimpleTopologicalInterpretation.SimpleSubst.term_eval_subst
      (I := demoInterp) (σs := propAtomSynSubst) (t := atomVarTerm))

theorem eval_comp_propWeak_propAtom :
    SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp
        (SimpleSubst.comp propWeakSubst propAtomSynSubst) =
      (SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp propAtomSynSubst).comp
        (SimpleTopologicalInterpretation.SimpleSubst.eval demoInterp propWeakSubst) := by
  exact
    (SimpleTopologicalInterpretation.SimpleSubst.eval_comp
      (I := demoInterp) (σs := propWeakSubst) (τs := propAtomSynSubst))

theorem eval_propSingleVar_false :
    (SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp propSingleVarTerm).toContinuousMap
      falsePropPoint = false := by
  simpa [propSingleVarTerm, SimpleTopologicalInterpretation.SimpleTerm.eval, CtxTerm.var,
    genericProp, genericVar] using genericProp_apply_false

theorem eval_propSingleVar_false_not_true :
    (SimpleTopologicalInterpretation.SimpleTerm.eval demoInterp propSingleVarTerm).toContinuousMap
      falsePropPoint ≠ true := by
  simpa [propSingleVarTerm, SimpleTopologicalInterpretation.SimpleTerm.eval, CtxTerm.var,
    genericProp, genericVar] using genericProp_apply_false_not_true

end AwodeyButzSimpleTermsRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
