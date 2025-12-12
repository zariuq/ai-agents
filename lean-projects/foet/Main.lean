import Foet

set_option autoImplicit false

namespace Foet

-- Tiny sanity check: this should elaborate without any axioms/sorries.
inductive World : Type
  | w

def sem : ValueSemantics World :=
  ⟨fun _ φ => φ⟩

def semD : DeonticSemantics World :=
  ⟨fun _ φ => φ⟩

def align : ∀ a φ w, semD.deontic a φ w ↔ sem.morally (deonticToMoralValue a) φ w := by
  intro a φ w
  rfl

def exampleSentence : ValueJudgmentSentence World :=
  { tag := .MorallyGood, formula := fun _ => True }

example : Entails (valueJudgmentSemantics World sem) (Set.singleton exampleSentence) exampleSentence := by
  intro w hw
  exact hw exampleSentence (by
    show exampleSentence ∈ Set.singleton exampleSentence
    rfl)

def exampleDeontic : DeonticSentence World :=
  { tag := .Obligation, formula := fun _ => True }

def exampleDeonticTheory : DeontologicalImperativeTheory World :=
  Set.singleton exampleDeontic

def exampleAsValue : ValueJudgmentTheory World :=
  exampleDeonticTheory.toValueJudgmentTheory

example : exampleDeontic.toValue ∈ exampleAsValue :=
  Theory.mem_map_of_mem (T := exampleDeonticTheory) (f := DeonticSentence.toValue) (a := exampleDeontic) rfl

example : Entails (deonticSemantics World semD) exampleDeonticTheory exampleDeontic := by
  intro w hw
  exact hw exampleDeontic rfl

example : Entails (valueJudgmentSemantics World sem) exampleAsValue exampleDeontic.toValue := by
  have h :=
    (entails_deontic_iff_entails_value (semD := semD) (semV := sem) align exampleDeonticTheory exampleDeontic).1
  exact h (by
    intro w hw
    exact hw exampleDeontic rfl)

def utilSem : UtilityAssignmentSemantics World :=
  ⟨fun _ _ => 1⟩

def utilSentence : UtilityAssignmentSentence World :=
  { tag := 5, formula := fun _ => True }

def utilTheory : UtilityAssignmentTheory World :=
  Set.singleton utilSentence

def utilAsValue : ValueJudgmentTheory World :=
  utilTheory.toValueJudgmentTheory

example : Entails (utilityAssignmentSemantics World utilSem) utilTheory utilSentence := by
  intro w hw
  exact hw utilSentence rfl

example :
    Entails
      (valueJudgmentSemantics World (valueSemanticsOfUtility World utilSem))
      utilAsValue utilSentence.toValue := by
  have h :=
    (entails_utilitarian_iff_entails_value (World := World) (semU := utilSem) utilTheory utilSentence).1
  exact h (by
    intro w hw
    exact hw utilSentence rfl)

def virtSem : VirtueTargetSemantics World :=
  ⟨fun _ φ => φ⟩

def virtAlign : ∀ a φ w, virtSem.targets a φ w ↔ sem.morally (virtueAspectToMoralValue a) φ w := by
  intro a φ w
  rfl

def virtSentence : VirtueTargetSentence World :=
  { aspect := .Virtuous, formula := fun _ => True }

def virtTheory : VirtueTargetTheory World :=
  Set.singleton virtSentence

def virtAsValue : ValueJudgmentTheory World :=
  virtTheory.toValueJudgmentTheory

example : Entails (virtueTargetSemantics World virtSem) virtTheory virtSentence := by
  intro w hw
  exact hw virtSentence rfl

example : Entails (valueJudgmentSemantics World sem) virtAsValue virtSentence.toValue := by
  have h :=
    (entails_virtueTarget_iff_entails_value (semT := virtSem) (semV := sem) virtAlign virtTheory virtSentence).1
  exact h (by
    intro w hw
    exact hw virtSentence rfl)

example : exampleSentence.paradigmLoop = exampleSentence :=
  ValueJudgmentSentence.paradigmLoop_id exampleSentence

end Foet
