import Foet.UtilitarianToValue
import Foet.VirtueToValue

set_option autoImplicit false

namespace Foet

universe u

/-
“Moral paradigm equivalence” (ESOWIKI) as a type-checked translation loop.

This file intentionally stays at the *minimal sentence level* (tag + formula),
so we can sanity-check the inter-paradigm plumbing in Lean before importing any
large ontology fragments.
-/

/-- Convenience: deontic sentence → utility-assignment sentence (via value judgments). -/
def DeonticSentence.toUtilityAssignment {World : Type u} (s : DeonticSentence World) :
    UtilityAssignmentSentence World :=
  s.toValue.toUtilityAssignment

/-- Convenience: utility-assignment sentence → deontic sentence (via value judgments). -/
def UtilityAssignmentSentence.toDeontic {World : Type u} (s : UtilityAssignmentSentence World) :
    DeonticSentence World :=
  s.toValue.toDeontic

/-- Utility-assignment sentence → virtue-desire sentence (via value judgments). -/
def UtilityAssignmentSentence.toVirtueDesire {World : Type u} (s : UtilityAssignmentSentence World) :
    VirtueDesireSentence World :=
  (s.toValue.toVirtueTarget).toDesire

/-- Virtue-desire sentence → value-judgment sentence (via virtue-target). -/
def VirtueDesireSentence.toValue {World : Type u} (s : VirtueDesireSentence World) :
    ValueJudgmentSentence World :=
  s.toTarget.toValue

/--
The “paradigm loop” suggested by the wiki page:

`Value → Deontic → Util → VirtueDesire → Target → Value`

In our minimal Lean MVP, each hop is a definitional/tag-level translation, so the loop is
literally the identity.
-/
def ValueJudgmentSentence.paradigmLoop {World : Type u} (s : ValueJudgmentSentence World) :
    ValueJudgmentSentence World :=
  ((((s.toDeontic).toUtilityAssignment).toVirtueDesire).toTarget).toValue

theorem ValueJudgmentSentence.paradigmLoop_id {World : Type u} (s : ValueJudgmentSentence World) :
    s.paradigmLoop = s := by
  cases s with
  | mk tag formula =>
    cases tag <;> rfl

end Foet
