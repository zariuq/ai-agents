import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzGenericPredicates

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

namespace AwodeyButzGenericPredicatesRegression

open SimpleTopologicalInterpretation

local instance : TopologicalSpace Bool := ⊥

inductive DemoBase where
  | atom
  deriving DecidableEq, Repr

inductive DemoConst : Ty DemoBase → Type where
  | truth : DemoConst .prop
  | atomWitness : DemoConst (.base .atom)

def demoInterp : SimpleTopologicalInterpretation DemoBase DemoConst Bool where
  propSpace := EtaleSpace.refl Bool
  baseSpace := fun _ => EtaleSpace.refl Bool
  constProp := fun _ => EtaleSpace.GlobalSection.terminal Bool
  constBase := fun _ => EtaleSpace.GlobalSection.terminal Bool

def truthTerm : demoInterp.CtxTerm [] .prop :=
  CtxTerm.const demoInterp [] .prop DemoConst.truth

def atomTerm : demoInterp.CtxTerm [] (.base .atom) :=
  CtxTerm.const demoInterp [] (.base .atom) DemoConst.atomWitness

def truthSubst : demoInterp.CtxHom [] [.prop] :=
  CtxTerm.cons truthTerm (CtxHom.terminal demoInterp [])

def atomSubst : demoInterp.CtxHom [] [.base .atom] :=
  CtxTerm.cons atomTerm (CtxHom.terminal demoInterp [])

def falsePropPoint : (demoInterp.ctxSpace [.prop]).Carrier :=
  ⟨(false, false), rfl⟩

def truePropPoint : (demoInterp.ctxSpace [.prop]).Carrier :=
  ⟨(true, true), rfl⟩

def falseAtomPoint : (demoInterp.ctxSpace [.base .atom]).Carrier :=
  ⟨(false, false), rfl⟩

theorem cons_head_tail_id_prop :
    CtxTerm.cons (genericProp demoInterp []) (CtxHom.tail demoInterp .prop []) =
      CtxHom.id demoInterp [.prop] := by
  unfold genericProp genericVar
  exact CtxHom.cons_head_tail (I := demoInterp) .prop []

theorem cons_head_tail_id_atom :
    CtxTerm.cons (genericVar demoInterp (.base .atom) []) (CtxHom.tail demoInterp (.base .atom) []) =
      CtxHom.id demoInterp [.base .atom] := by
  unfold genericVar
  exact CtxHom.cons_head_tail (I := demoInterp) (.base .atom) []

theorem genericProp_reindex_truthSubst :
    (genericProp demoInterp []).reindex truthSubst = truthTerm := by
  unfold truthSubst
  exact CtxTerm.genericProp_reindex_cons (I := demoInterp)
    (Γ := []) (Δ := []) truthTerm (CtxHom.terminal demoInterp [])

theorem genericVar_reindex_atomSubst :
    (genericVar demoInterp (.base .atom) []).reindex atomSubst = atomTerm := by
  unfold atomSubst genericVar
  exact CtxTerm.genericVar_reindex_cons (I := demoInterp)
    (Γ := []) (Δ := []) (τ := (.base .atom))
    atomTerm (CtxHom.terminal demoInterp [])

theorem genericProp_apply_false :
    (genericProp demoInterp []).toContinuousMap falsePropPoint = false := by
  rfl

theorem genericProp_apply_true :
    (genericProp demoInterp []).toContinuousMap truePropPoint = true := by
  rfl

theorem genericVar_apply_falseAtom :
    (genericVar demoInterp (.base .atom) []).toContinuousMap falseAtomPoint = false := by
  rfl

theorem genericProp_apply_false_not_true :
    (genericProp demoInterp []).toContinuousMap falsePropPoint ≠ true := by
  rw [genericProp_apply_false]
  intro h
  cases h

end AwodeyButzGenericPredicatesRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
