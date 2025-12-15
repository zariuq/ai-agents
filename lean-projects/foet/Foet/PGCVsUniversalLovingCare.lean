import Foet.EvaluateTheory

set_option autoImplicit false

namespace Foet

namespace UniversalLovingCare

universe u

/-!
ESOWIKI-aligned formalization of (Epistemic) Universal Love.

From the “Ethical Conjectures” page:

UniversalLove:
  UL agent loves universally iff for all agents A, if A desires φ then UL desires the *fulfillment* of φ.

EpistemicUniversalLove:
  as above, but only for desires that UL *knows about*.

The conjecture:
  if UL has EpistemicUniversalLove and knows two agents desire φ and ¬φ, then UL “desires everything”,
  so classical closure principles for desires lead to explosion, motivating paraconsistent reasoning.
-/

abbrev Not {W : Type u} (φ : Formula W) : Formula W :=
  fun w => ¬ φ w

abbrev And {W : Type u} (φ ψ : Formula W) : Formula W :=
  fun w => φ w ∧ ψ w

abbrev Subset {W : Type u} (φ ψ : Formula W) : Prop :=
  ∀ w, φ w → ψ w

structure LoveSig (World : Type u) (Agent : Type u) (Process : Type u) : Type (u + 1) where
  desires : Agent → Formula World → World → Prop
  knows : Agent → (World → Prop) → World → Prop
  realizesFormula : Process → Formula World → World → Prop

def fulfills {World : Type u} {Agent : Type u} {Process : Type u} (sig : LoveSig World Agent Process)
    (φ : Formula World) : Formula World :=
  fun w => ∃ p : Process, sig.realizesFormula p φ w

def UniversalLove {World : Type u} {Agent : Type u} {Process : Type u} (sig : LoveSig World Agent Process)
    (ul : Agent) : Formula World :=
  fun w =>
    ∀ (a : Agent) (φ : Formula World),
      sig.desires a φ w → sig.desires ul (fulfills sig φ) w

def EpistemicUniversalLove {World : Type u} {Agent : Type u} {Process : Type u} (sig : LoveSig World Agent Process)
    (ul : Agent) : Formula World :=
  fun w =>
    ∀ (a : Agent) (φ : Formula World),
      sig.knows ul (fun w' => sig.desires a φ w') w →
        sig.desires ul (fulfills sig φ) w

/-! ## Guidance via evaluator-style output

In the ESOWIKI, “guidance” is the output of `evaluateTheory` at a choice point.
Here we mirror that idea directly from *desires* (no entailment, no temporal logic):

At a world `w`, say:
- Good φ iff the agent desires φ at w
- Bad φ iff the agent desires ¬φ at w
- Otherwise Permissible φ

This is a deliberately simple “practical guidance” extraction.
-/

noncomputable def desireTag {World : Type u} {Agent : Type u} (desires : Agent → Formula World → World → Prop)
    (a : Agent) (w : World) (φ : Formula World) : MoralValueAttribute := by
  classical
  exact
    if desires a φ w then
      .MorallyGood
    else if desires a (Not φ) w then
      .MorallyBad
    else
      .MorallyPermissible

def evaluateByDesire {World : Type u} {Agent : Type u} (desires : Agent → Formula World → World → Prop)
    (a : Agent) (w : World) (cp : ChoicePoint World) : ValueJudgmentTheory World :=
  fun s => ∃ φ, φ ∈ cp ∧ s = valueSentence (desireTag (World := World) (Agent := Agent) desires a w φ) φ

def LabelsGood {World : Type u} (G : ValueJudgmentTheory World) (φ : Formula World) : Prop :=
  morallyGood φ ∈ G

def LabelsBad {World : Type u} (G : ValueJudgmentTheory World) (φ : Formula World) : Prop :=
  morallyBad φ ∈ G

def LabelsPerm {World : Type u} (G : ValueJudgmentTheory World) (φ : Formula World) : Prop :=
  morallyPermissible φ ∈ G

/--
Evaluator-style “provides guidance” (one useful notion):
there exist two options with different *chosen* tags (so the evaluator distinguishes them).

This intentionally does *not* claim that “all-permissible” is bad in general; it only measures discrimination.
-/
def DiscriminatesByTag {World : Type u} {Agent : Type u} (desires : Agent → Formula World → World → Prop)
    (a : Agent) (w : World) (cp : ChoicePoint World) : Prop :=
  ∃ φ ψ, φ ∈ cp ∧ ψ ∈ cp ∧ desireTag (World := World) (Agent := Agent) desires a w φ ≠
    desireTag (World := World) (Agent := Agent) desires a w ψ

/-!
ESOWIKI conjecture (guidance form):

If `ul` has epistemic universal love and knows about a contradictory pair of desires,
then at the conflict choice point `{fulfill φ, fulfill ¬φ}` the derived guidance cannot discriminate:
it recommends both options as good.
-/
theorem epistemic_universal_love_explodes
    {World : Type u} {Agent : Type u} {Process : Type u}
    (sig : LoveSig World Agent Process)
    (ul a1 a2 : Agent) (φ : Formula World) (w : World)
    (hEUL : EpistemicUniversalLove sig ul w)
    (hKnow1 : sig.knows ul (fun w' => sig.desires a1 φ w') w)
    (hKnow2 : sig.knows ul (fun w' => sig.desires a2 (Not φ) w') w) :
    ¬ DiscriminatesByTag (World := World) (Agent := Agent) sig.desires ul w
        (Set.insert (fulfills sig φ) (Set.singleton (fulfills sig (Not φ)))) := by
  intro hDisc
  rcases hDisc with ⟨x, y, hx, hy, hNe⟩
  -- In this conflict choice point, epistemic universal love implies both options are desired,
  -- so the desire-based tagger labels them both `MorallyGood`, hence cannot discriminate.
  have hGoodFulfill : sig.desires ul (fulfills sig φ) w :=
    hEUL a1 φ hKnow1
  have hGoodFulfillNot : sig.desires ul (fulfills sig (Not φ)) w :=
    hEUL a2 (Not φ) hKnow2
  have hTagX : desireTag (World := World) (Agent := Agent) sig.desires ul w x = .MorallyGood := by
    -- `x` is one of the two options; either way the corresponding desire holds.
    rcases hx with rfl | hx'
    · simp [desireTag, hGoodFulfill]
    · cases hx'
      simp [desireTag, hGoodFulfillNot]
  have hTagY : desireTag (World := World) (Agent := Agent) sig.desires ul w y = .MorallyGood := by
    rcases hy with rfl | hy'
    · simp [desireTag, hGoodFulfill]
    · cases hy'
      simp [desireTag, hGoodFulfillNot]
  exact hNe (by simpa [hTagX, hTagY])

end UniversalLovingCare

end Foet
