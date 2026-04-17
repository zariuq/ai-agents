import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzTypedFragment

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

namespace AwodeyButzTypedFragmentRegression

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

def atomSection : (demoInterp.space (.base .atom)).GlobalSection :=
  demoInterp.constSection (.base .atom) DemoConst.atomWitness

def propSection : (demoInterp.space .prop).GlobalSection :=
  demoInterp.constSection .prop DemoConst.truth

def singletonCtxSection :
    (demoInterp.ctxSpace [.base .atom]).GlobalSection :=
  EtaleSpace.GlobalSection.pair atomSection (EtaleSpace.GlobalSection.terminal Bool)

theorem prop_space_is_refl :
    demoInterp.space .prop = EtaleSpace.refl Bool :=
  rfl

theorem atom_space_is_refl :
    demoInterp.space (.base .atom) = EtaleSpace.refl Bool :=
  rfl

theorem propSection_apply (b : Bool) :
    propSection.toContinuousMap b = b :=
  rfl

theorem atomSection_apply (b : Bool) :
    atomSection.toContinuousMap b = b :=
  rfl

theorem ctxSpace_nil_is_terminal :
    demoInterp.ctxSpace [] = EtaleSpace.terminal Bool :=
  rfl

theorem ctxSpace_singleton_is_prod :
    demoInterp.ctxSpace [.base .atom] =
      EtaleSpace.prod (EtaleSpace.refl Bool) (EtaleSpace.terminal Bool) :=
  rfl

theorem singletonCtxSection_fst :
    singletonCtxSection.fst = atomSection := by
  simp [singletonCtxSection, atomSection]

theorem singletonCtxSection_apply_fst (b : Bool) :
    Function.Pullback.fst (singletonCtxSection.toContinuousMap b) = b := by
  rfl

theorem singletonCtxSection_apply_snd_false :
    Function.Pullback.snd (singletonCtxSection.toContinuousMap false) = false := by
  rfl

theorem singletonCtxSection_apply_snd_not_true :
    Function.Pullback.snd (singletonCtxSection.toContinuousMap false) ≠ true := by
  rw [singletonCtxSection_apply_snd_false]
  intro h
  cases h

end AwodeyButzTypedFragmentRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
