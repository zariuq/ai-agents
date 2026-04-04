import Mathlib.Order.ULift
import Mettapedia.Logic.HOL.ParamWorld
import Mettapedia.Logic.HOL.Semantics.HeytingHenkin

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-!
# Growing-World Semantic Carrier  [MAINLINE]

This file begins the direct semantic packaging for the parameterized root route.
The current layer names the base-type carrier over growing worlds, without yet
committing to the full `HeytingPreModel` structure.

Positive example:
a constant symbol at base type gives a canonical section present at every world.

Negative example:
this file does not yet define the truth theorem or the final
`RootCounterworld -> HeytingHenkinModel` bridge.
-/

namespace GrowingWorld

/-- Universe-lifted truth object for the direct growing-model route.

`HeytingPreModel` expects both the truth object and the base carriers to live in
the same ambient universe `Type (max (u + 1) w)`. The raw growing-world truth
object `GrowingWorld.Ω` is smaller, so the direct route lifts it explicitly at
the semantic packaging layer.

Positive example:
the lifted truth object still carries the same Kripke/Henkin order structure as
the raw upper-set truth values.

Negative example:
this does not yet define the final premodel; it only repairs the universe level
of the truth object used by that future packaging.
-/
abbrev ModelΩ
    (Base : Type u) (Const : Ty Base → Type v) :
    Type (max (u + 1) v) :=
  ULift.{max (u + 1) v, max u v} (GrowingWorld.Ω (Base := Base) (Const := Const))

/-- Embed a raw growing-world truth value into the universe-lifted truth
object. -/
abbrev liftTruth
    (p : GrowingWorld.Ω (Base := Base) (Const := Const)) :
    ModelΩ (Base := Base) (Const := Const) :=
  ULift.up p

@[simp] theorem down_liftTruth
    (p : GrowingWorld.Ω (Base := Base) (Const := Const)) :
    (liftTruth (Base := Base) (Const := Const) p).down = p :=
  rfl

@[simp] theorem liftTruth_down
    (p : ModelΩ (Base := Base) (Const := Const)) :
    liftTruth (Base := Base) (Const := Const) p.down = p := by
  cases p
  rfl

instance : HImp (ModelΩ (Base := Base) (Const := Const)) where
  himp p q := ULift.up (p.down ⇨ q.down)

@[simp] theorem down_himp
    (p q : ModelΩ (Base := Base) (Const := Const)) :
    (p ⇨ q).down = (p.down ⇨ q.down) :=
  rfl

noncomputable instance : Order.Frame (ModelΩ (Base := Base) (Const := Const)) := by
  let _ : Order.Frame (GrowingWorld.Ω (Base := Base) (Const := Const)) := inferInstance
  refine Order.Frame.mk ?_ ?_
  · intro a b c
    change a.down ≤ b.down ⇨ c.down ↔ a.down ⊓ b.down ≤ c.down
    exact (le_himp_iff (a := a.down) (b := b.down) (c := c.down))
  · intro a
    apply ULift.down_injective
    simp

/-- A supported future-local base-type individual for the growing-domain route.

Instead of requiring a single global section defined at every world, a base
section is only required on an upward-closed support of worlds. This is the
right carrier shape for growing domains: a local parameter term born at some
future world should become available above that world without forcing an
artificial root-world value.

Positive example:
an original base constant gives a section supported at all worlds.

Negative example:
this file still does not package the full `HeytingPreModel`; it only repairs
the carrier layer so future local inhabitants are representable.
-/
structure BaseSection
    (Base : Type u) (Const : Ty Base → Type v)
    (b : Base) : Type (max (u + 1) v) where
  support : UpperSet (GrowingWorld Base Const)
  termAt :
    ∀ {W : GrowingWorld Base Const},
      W ∈ support →
        ClosedTerm (ParamConst Const W.ctx) (.base b)

/-- The principal future of a world inside the growing frame. -/
def principalSupport
    (W : GrowingWorld Base Const) :
    UpperSet (GrowingWorld Base Const) :=
  ⟨{V | W ≤ V}, by
    intro U V hUV hWU
    exact le_trans hWU hUV
  ⟩

@[simp] theorem mem_principalSupport
    {U V : GrowingWorld Base Const} :
    V ∈ principalSupport (Base := Base) (Const := Const) U ↔ U ≤ V :=
  Iff.rfl

/-- A local closed base term defines a supported section on its honest future.

Positive example:
the fresh parameter constant at a one-step extension yields a base section
supported exactly above that extension world.

Negative example:
this constructor does not yet prove any recursive coherence theorem beyond the
transport built into `transportClosedTerm`.
-/
noncomputable def localSection
    {b : Base}
    (W : GrowingWorld Base Const)
    (t : ClosedTerm (ParamConst Const W.ctx) (.base b)) :
    BaseSection Base Const b where
  support := principalSupport (Base := Base) (Const := Const) W
  termAt hV := transportClosedTerm (Base := Base) (Const := Const) hV t

/-- The fresh head parameter at a base-typed one-step extension yields a
supported base section.

Positive example:
this is the simplest future-local inhabitant that the old global-section
carrier could not represent at all.

Negative example:
this only handles the distinguished newest parameter, not arbitrary local
closed terms.
-/
noncomputable def freshParamSection
    {Γ : Ctx Base} {b : Base}
    (W : PrimeTheory Const (.base b :: Γ)) :
    BaseSection Base Const b :=
  localSection
    (Base := Base)
    (Const := Const)
    ⟨.base b :: Γ, W⟩
    (.const (ParamConst.param (.vz : Var (.base b :: Γ) (.base b))))

theorem nonempty_baseSection_of_param_world
    {Γ : Ctx Base} {b : Base}
    (W : PrimeTheory Const (.base b :: Γ)) :
    Nonempty (BaseSection Base Const b) :=
  ⟨freshParamSection (Base := Base) (Const := Const) W⟩

/-- Transporting an original base constant across a context equality is trivial.

Positive example:
if `Δ = Γ`, the same original constant denotes the same closed term on both
parameterized signatures.

Negative example:
this does not yet transport arbitrary local parameter constants, whose indices
do depend on the context.
-/
lemma cast_closedTerm_const_base
    {Γ Δ : Ctx Base} {b : Base}
    (h : Δ = Γ) (c : Const (.base b)) :
    cast (by cases h; rfl) (.const (Sum.inl c) : ClosedTerm (ParamConst Const Γ) (.base b)) =
      (.const (ParamConst.base c) : ClosedTerm (ParamConst Const Δ) (.base b)) := by
  cases h
  rfl

/-- The constant section generated by an original base constant.

Positive example:
the denotation of an original individual constant should be world-invariant in
the direct growing model.

Negative example:
this only applies to constants of base type, not arbitrary higher-order
constants.
-/
noncomputable def constSection
    {b : Base}
    (c : Const (.base b)) :
    BaseSection Base Const b where
  support := ⊤
  termAt _ := .const (ParamConst.base c)

@[simp] theorem constSection_termAt
    {b : Base}
    (c : Const (.base b))
    {W : GrowingWorld Base Const}
    (hW : W ∈ (constSection (Base := Base) (Const := Const) c).support) :
    (constSection (Base := Base) (Const := Const) c).termAt hW =
      .const (ParamConst.base c) :=
  rfl

/-- The local equality formula comparing two supported base sections at a world
where both are available. -/
def eqFormulaAt
    {b : Base}
    (x y : BaseSection Base Const b)
    {W : GrowingWorld Base Const}
    (hx : W ∈ x.support)
    (hy : W ∈ y.support) :
    ClosedFormula (ParamConst Const W.ctx) :=
  .eq (x.termAt hx) (y.termAt hy)

@[simp] theorem eqFormulaAt_constSection
    {b : Base}
    (c d : Const (.base b))
    {W : GrowingWorld Base Const}
    (hc : W ∈ (constSection (Base := Base) (Const := Const) c).support)
    (hd : W ∈ (constSection (Base := Base) (Const := Const) d).support) :
    eqFormulaAt (Base := Base) (Const := Const)
        (constSection (Base := Base) (Const := Const) c)
        (constSection (Base := Base) (Const := Const) d)
        hc
        hd =
      .eq (.const (ParamConst.base c)) (.const (ParamConst.base d)) :=
  rfl

end GrowingWorld

end Mettapedia.Logic.HOL
