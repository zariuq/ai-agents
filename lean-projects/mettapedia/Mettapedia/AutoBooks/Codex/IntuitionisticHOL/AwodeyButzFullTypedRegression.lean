import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzFullTyped

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

namespace AwodeyButzFullTypedRegression

noncomputable section

local instance : TopologicalSpace Bool := ⊥

inductive DemoBase where
  | atom
  deriving DecidableEq, Repr

inductive DemoConst : Ty DemoBase → Type where
  | truth : DemoConst .prop
  | atomWitness : DemoConst (.base .atom)

noncomputable def demoSpace : Ty DemoBase → EtaleSpace Bool
  | .prop => EtaleSpace.refl Bool
  | .base _ => EtaleSpace.refl Bool
  | .arr τ υ => EtaleSpace.exp (demoSpace τ) (demoSpace υ)

noncomputable def demoConstSection : {τ : Ty DemoBase} → DemoConst τ → (demoSpace τ).GlobalSection
  | .prop, .truth => by
      simpa [demoSpace] using (EtaleSpace.GlobalSection.terminal Bool : (EtaleSpace.refl Bool).GlobalSection)
  | .base _, .atomWitness => by
      simpa [demoSpace] using (EtaleSpace.GlobalSection.terminal Bool : (EtaleSpace.refl Bool).GlobalSection)

noncomputable def demoInterp : TopologicalInterpretation DemoBase DemoConst Bool where
  space := demoSpace
  const := demoConstSection
  propSpace := EtaleSpace.refl Bool
  baseSpace := fun _ => EtaleSpace.refl Bool
  space_prop := rfl
  space_base := by
    intro b
    cases b
    rfl
  space_arr := by
    intro τ υ
    rfl

def propHead : demoInterp.CtxTerm [.prop] .prop :=
  TopologicalInterpretation.CtxTerm.var0 demoInterp .prop []

noncomputable def propId : demoInterp.CtxTerm [] (.arr .prop .prop) :=
  TopologicalInterpretation.CtxTerm.lam propHead

noncomputable def truthTerm : demoInterp.CtxTerm [] .prop :=
  EtaleSpace.BasicTopologicalInterpretation.CtxTerm.const
    demoInterp.toBasicTopologicalInterpretation [] DemoConst.truth

example {X : Type*} [TopologicalSpace X]
    {Base : Type*} {Const : Ty Base → Type*}
    {I : TopologicalInterpretation Base Const X}
    {Γ : Ctx Base} {τ υ : Ty Base}
    (t : I.CtxTerm (τ :: Γ) υ)
    (a : I.CtxTerm Γ τ) :
    TopologicalInterpretation.CtxTerm.app (I := I) (TopologicalInterpretation.CtxTerm.lam t) a =
      t.reindex (TopologicalInterpretation.CtxHom.cons a (TopologicalInterpretation.CtxHom.id I Γ)) :=
  TopologicalInterpretation.CtxTerm.app_lam t a

theorem prop_space_is_refl :
    demoInterp.space .prop = EtaleSpace.refl Bool :=
  rfl

theorem atom_space_is_refl :
    demoInterp.space (.base .atom) = EtaleSpace.refl Bool :=
  rfl

theorem arr_space_is_exp :
    demoInterp.space (.arr .prop (.base .atom)) =
      EtaleSpace.exp (EtaleSpace.refl Bool) (EtaleSpace.refl Bool) :=
  rfl

theorem toSimple_agrees_on_atom :
    demoInterp.space (.base .atom) = demoInterp.toSimple.space (.base .atom) :=
  demoInterp.space_eq_simple_space (.base .atom)

theorem propId_app_truth :
    TopologicalInterpretation.CtxTerm.app propId truthTerm = truthTerm := by
  simp [propId, propHead, truthTerm]

end

end AwodeyButzFullTypedRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
