import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSimpleVariables
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzGenericPredicatesRegression

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

namespace AwodeyButzSimpleVariablesRegression

open SimpleTopologicalInterpretation
open AwodeyButzGenericPredicatesRegression

def propAtomSubst : demoInterp.CtxHom [] [.prop, .base .atom] :=
  CtxTerm.cons truthTerm (CtxTerm.cons atomTerm (CtxHom.terminal demoInterp []))

def propVar : demoInterp.CtxTerm [.prop, .base .atom] .prop :=
  CtxTerm.var demoInterp (SimpleVar.vz : SimpleVar DemoBase [.prop, .base .atom] .prop)

def atomVar : demoInterp.CtxTerm [.prop, .base .atom] (.base .atom) :=
  CtxTerm.var demoInterp
    (SimpleVar.vs (SimpleVar.vz : SimpleVar DemoBase [.base .atom] (.base .atom)))

theorem propVar_eq_genericProp :
    propVar = genericProp demoInterp [.base .atom] :=
  rfl

theorem propVar_reindex_propAtomSubst :
    propVar.reindex propAtomSubst = truthTerm := by
  simp [propVar, propAtomSubst]

theorem atomVar_reindex_propAtomSubst :
    atomVar.reindex propAtomSubst = atomTerm := by
  simp [atomVar, propAtomSubst, CtxTerm.weaken, CtxTerm.reindex_comp]

theorem propSingleVar_apply_false :
    (CtxTerm.var demoInterp (SimpleVar.vz : SimpleVar DemoBase [.prop] .prop)).toContinuousMap
      falsePropPoint = false := by
  simpa [CtxTerm.var, genericProp, genericVar] using genericProp_apply_false

theorem propSingleVar_apply_false_not_true :
    (CtxTerm.var demoInterp (SimpleVar.vz : SimpleVar DemoBase [.prop] .prop)).toContinuousMap
      falsePropPoint ≠ true := by
  simpa [CtxTerm.var, genericProp, genericVar] using genericProp_apply_false_not_true

end AwodeyButzSimpleVariablesRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
