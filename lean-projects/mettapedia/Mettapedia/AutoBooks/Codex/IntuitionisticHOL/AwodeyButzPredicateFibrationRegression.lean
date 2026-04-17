import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzPredicateFibration
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzGenericPredicatesRegression

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

namespace AwodeyButzPredicateFibrationRegression

open SimpleTopologicalInterpretation
open AwodeyButzGenericPredicatesRegression

theorem toEmptyEquivPUnit_terminal :
    CtxHom.toEmptyEquivPUnit demoInterp [.prop] (CtxHom.terminal demoInterp [.prop]) = PUnit.unit :=
  rfl

theorem toEmptyEquivPUnit_symm_unit :
    (CtxHom.toEmptyEquivPUnit demoInterp [.prop]).symm PUnit.unit =
      CtxHom.terminal demoInterp [.prop] :=
  rfl

theorem splitEquiv_truthSubst :
    (CtxHom.splitEquiv demoInterp [] .prop []) truthSubst =
      (truthTerm, CtxHom.terminal demoInterp []) := by
  simp [CtxHom.splitEquiv, truthSubst]

theorem splitEquiv_symm_truthPair :
    (CtxHom.splitEquiv demoInterp [] .prop []).symm
      (truthTerm, CtxHom.terminal demoInterp []) = truthSubst :=
  rfl

theorem splitEquiv_roundtrip_truthSubst :
    (CtxHom.splitEquiv demoInterp [] .prop []).symm
      ((CtxHom.splitEquiv demoInterp [] .prop []) truthSubst) = truthSubst :=
  (CtxHom.splitEquiv demoInterp [] .prop []).left_inv truthSubst

theorem predContextEquiv_truthSubst :
    predContextEquiv demoInterp [] truthSubst = truthTerm := by
  simpa [predContextEquiv] using genericProp_reindex_truthSubst

theorem predContextEquiv_symm_truthTerm :
    (predContextEquiv demoInterp []).symm truthTerm = truthSubst :=
  rfl

theorem predContextEquiv_id_prop :
    predContextEquiv demoInterp [.prop] (CtxHom.id demoInterp [.prop]) =
      genericProp demoInterp [] := by
  rw [predContextEquiv]
  exact CtxTerm.reindex_id (t := genericProp demoInterp [])

theorem predContextEquiv_id_prop_apply_false :
    (predContextEquiv demoInterp [.prop] (CtxHom.id demoInterp [.prop])).toContinuousMap
      falsePropPoint = false := by
  simpa [predContextEquiv_id_prop] using genericProp_apply_false

theorem predContextEquiv_id_prop_false_not_true :
    (predContextEquiv demoInterp [.prop] (CtxHom.id demoInterp [.prop])).toContinuousMap
      falsePropPoint ≠ true := by
  simpa [predContextEquiv_id_prop] using genericProp_apply_false_not_true

end AwodeyButzPredicateFibrationRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
