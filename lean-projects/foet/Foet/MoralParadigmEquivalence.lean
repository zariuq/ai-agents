import Foet.EvaluateTheoryParadigms
import Foet.Translation

set_option autoImplicit false

namespace Foet

universe u v w

/-!
Moral paradigm equivalence (ESOWIKI): two Lean formulations.

1. **Practical / choice-point equivalence**: paradigms are equivalent if, after a
   translation on theories, they yield the same `ValueJudgmentTheory` when evaluated
   at every context + choice point.

2. **Semantic / entailment equivalence**: paradigms are equivalent if the translation
   preserves models/entailment via `Theory.map` (deterministic) or `Theory.relMap`
   (existential-introducing), using `RelSound`/`RelComplete`.
-/

/-! ## 1) Choice-point evaluator formulation -/

abbrev EvaluatorUnder (World : Type u) (TheoryP : Type v) : Type (max (max u v) 1) :=
  TheoryP → Formula World → ChoicePoint World → ValueJudgmentTheory World

def SimulatesByEvaluation {World : Type u} {TheoryA : Type v} {TheoryB : Type w}
    (evalA : EvaluatorUnder World TheoryA) (evalB : EvaluatorUnder World TheoryB) : Prop :=
  ∃ translate : TheoryB → TheoryA, ∀ T ctx cp, evalA (translate T) ctx cp = evalB T ctx cp

def EquivalentByEvaluation {World : Type u} {TheoryA : Type v} {TheoryB : Type w}
    (evalA : EvaluatorUnder World TheoryA) (evalB : EvaluatorUnder World TheoryB) : Prop :=
  SimulatesByEvaluation (World := World) evalA evalB ∧ SimulatesByEvaluation (World := World) evalB evalA

/-! ### Small “round-trip” lemmas for theory maps -/

theorem value_toDeontic_toValueTheory_eq {World : Type u} (T : ValueJudgmentTheory World) :
    (T.toDeontologicalImperativeTheory).toValueJudgmentTheory = T := by
  funext s
  apply propext
  constructor
  · intro hs
    rcases hs with ⟨d, hd, hdEq⟩
    rcases hd with ⟨v, hv, hvEq⟩
    cases hvEq
    -- `v.toDeontic.toValue` is definitionally `DeonticSentence.toValue v.toDeontic`.
    have hsEq : s = v := by
      exact Eq.trans hdEq.symm (ValueJudgmentSentence.toDeontic_toValue (World := World) v)
    cases hsEq
    exact hv
  · intro hs
    refine ⟨s.toDeontic, ?_, ?_⟩
    · exact Theory.mem_map_of_mem (T := T) (f := ValueJudgmentSentence.toDeontic) (a := s) hs
    · simpa using (ValueJudgmentSentence.toDeontic_toValue (World := World) s)

theorem value_toUtility_toValueTheory_eq {World : Type u} (T : ValueJudgmentTheory World) :
    (T.toUtilityAssignmentTheory).toValueJudgmentTheory = T := by
  funext s
  apply propext
  constructor
  · intro hs
    rcases hs with ⟨u, hu, huEq⟩
    rcases hu with ⟨v, hv, hvEq⟩
    cases hvEq
    have hsEq : s = v := by
      exact Eq.trans huEq.symm (ValueJudgmentSentence.toUtilityAssignment_toValue (World := World) v)
    cases hsEq
    exact hv
  · intro hs
    refine ⟨s.toUtilityAssignment, ?_, ?_⟩
    · exact Theory.mem_map_of_mem (T := T) (f := ValueJudgmentSentence.toUtilityAssignment) (a := s) hs
    · simpa using (ValueJudgmentSentence.toUtilityAssignment_toValue (World := World) s)

theorem value_toVirtueTarget_toValueTheory_eq {World : Type u} (T : ValueJudgmentTheory World) :
    (T.toVirtueTargetTheory).toValueJudgmentTheory = T := by
  funext s
  apply propext
  constructor
  · intro hs
    rcases hs with ⟨t, ht, htEq⟩
    rcases ht with ⟨v, hv, hvEq⟩
    cases hvEq
    have hsEq : s = v := by
      exact Eq.trans htEq.symm (ValueJudgmentSentence.toVirtueTarget_toValue (World := World) v)
    cases hsEq
    exact hv
  · intro hs
    refine ⟨s.toVirtueTarget, ?_, ?_⟩
    · exact Theory.mem_map_of_mem (T := T) (f := ValueJudgmentSentence.toVirtueTarget) (a := s) hs
    · simpa using (ValueJudgmentSentence.toVirtueTarget_toValue (World := World) s)

/-! ### MVP instances: Value ↔ {Deontic, Utilitarian, VirtueTarget} -/

theorem value_simulates_deontic_by_evaluation {World : Type u}
    (semD : DeonticSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semD.deontic a φ w ↔ semV.morally (deonticToMoralValue a) φ w) :
    SimulatesByEvaluation (World := World)
      (evalA := evaluateTheoryUnder (World := World) semV)
      (evalB := evaluateDeonticTheoryUnder (World := World) semD) := by
  refine ⟨fun T => T.toValueJudgmentTheory, ?_⟩
  intro T ctx cp
  symm
  simpa using
    (evaluateDeonticTheoryUnder_eq_evaluateTheoryUnder_toValue (World := World)
      (semD := semD) (semV := semV) h_align (T := T) (ctx := ctx) (cp := cp))

theorem deontic_simulates_value_by_evaluation {World : Type u}
    (semD : DeonticSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semD.deontic a φ w ↔ semV.morally (deonticToMoralValue a) φ w) :
    SimulatesByEvaluation (World := World)
      (evalA := evaluateDeonticTheoryUnder (World := World) semD)
      (evalB := evaluateTheoryUnder (World := World) semV) := by
  refine ⟨fun T => T.toDeontologicalImperativeTheory, ?_⟩
  intro T ctx cp
  have h :=
    (evaluateDeonticTheoryUnder_eq_evaluateTheoryUnder_toValue (World := World)
      (semD := semD) (semV := semV) h_align (T := T.toDeontologicalImperativeTheory) (ctx := ctx) (cp := cp))
  -- rewrite the translated theory back to `T`.
  simpa [value_toDeontic_toValueTheory_eq (World := World) (T := T)] using h

theorem value_simulates_utilitarian_by_evaluation {World : Type u}
    (semU : UtilityAssignmentSemantics World) :
    SimulatesByEvaluation (World := World)
      (evalA := evaluateTheoryUnder (World := World) (valueSemanticsOfUtility World semU))
      (evalB := evaluateUtilitarianTheoryUnder (World := World) semU) := by
  refine ⟨fun T => T.toValueJudgmentTheory, ?_⟩
  intro T ctx cp
  symm
  simpa using
    (evaluateUtilitarianTheoryUnder_eq_evaluateTheoryUnder_toValue (World := World)
      (semU := semU) (T := T) (ctx := ctx) (cp := cp))

theorem utilitarian_simulates_value_by_evaluation {World : Type u}
    (semU : UtilityAssignmentSemantics World) :
    SimulatesByEvaluation (World := World)
      (evalA := evaluateUtilitarianTheoryUnder (World := World) semU)
      (evalB := evaluateTheoryUnder (World := World) (valueSemanticsOfUtility World semU)) := by
  refine ⟨fun T => T.toUtilityAssignmentTheory, ?_⟩
  intro T ctx cp
  have h :=
    (evaluateUtilitarianTheoryUnder_eq_evaluateTheoryUnder_toValue (World := World)
      (semU := semU) (T := T.toUtilityAssignmentTheory) (ctx := ctx) (cp := cp))
  simpa [value_toUtility_toValueTheory_eq (World := World) (T := T)] using h

theorem value_simulates_virtueTarget_by_evaluation {World : Type u}
    (semT : VirtueTargetSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semT.targets a φ w ↔ semV.morally (virtueAspectToMoralValue a) φ w) :
    SimulatesByEvaluation (World := World)
      (evalA := evaluateTheoryUnder (World := World) semV)
      (evalB := evaluateVirtueTargetTheoryUnder (World := World) semT) := by
  refine ⟨fun T => T.toValueJudgmentTheory, ?_⟩
  intro T ctx cp
  symm
  simpa using
    (evaluateVirtueTargetTheoryUnder_eq_evaluateTheoryUnder_toValue (World := World)
      (semT := semT) (semV := semV) h_align (T := T) (ctx := ctx) (cp := cp))

theorem virtueTarget_simulates_value_by_evaluation {World : Type u}
    (semT : VirtueTargetSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semT.targets a φ w ↔ semV.morally (virtueAspectToMoralValue a) φ w) :
    SimulatesByEvaluation (World := World)
      (evalA := evaluateVirtueTargetTheoryUnder (World := World) semT)
      (evalB := evaluateTheoryUnder (World := World) semV) := by
  refine ⟨fun T => T.toVirtueTargetTheory, ?_⟩
  intro T ctx cp
  have h :=
    (evaluateVirtueTargetTheoryUnder_eq_evaluateTheoryUnder_toValue (World := World)
      (semT := semT) (semV := semV) h_align (T := T.toVirtueTargetTheory) (ctx := ctx) (cp := cp))
  simpa [value_toVirtueTarget_toValueTheory_eq (World := World) (T := T)] using h

/-! ## 2) Semantic formulation via `Theory.map` / `Theory.relMap` -/

def ModelsEquivalentAcross {S₁ : Type u} {S₂ : Type v} {M : Type w}
    (sem₁ : Semantics S₁ M) (sem₂ : Semantics S₂ M) (T₁ : Theory S₁) (T₂ : Theory S₂) : Prop :=
  ∀ m, Models sem₁ m T₁ ↔ Models sem₂ m T₂

structure RelationalTranslation {S₁ : Type u} {S₂ : Type v} {M : Type w}
    (sem₁ : Semantics S₁ M) (sem₂ : Semantics S₂ M) : Type (max u v w) where
  R : TranslationRel S₁ S₂
  sound : RelSound sem₁ sem₂ R
  complete : RelComplete sem₁ sem₂ R

def RelationalTranslation.push {S₁ : Type u} {S₂ : Type v} {M : Type w}
    {sem₁ : Semantics S₁ M} {sem₂ : Semantics S₂ M}
    (tr : RelationalTranslation (sem₁ := sem₁) (sem₂ := sem₂)) (T : Theory S₁) : Theory S₂ :=
  Theory.relMap tr.R T

theorem models_iff_models_relMap_of_witnessTotal {S₁ : Type u} {S₂ : Type v} {M : Type w}
    {sem₁ : Semantics S₁ M} {sem₂ : Semantics S₂ M}
    (R : TranslationRel S₁ S₂)
    (hSound : RelSound sem₁ sem₂ R) (hComplete : RelComplete sem₁ sem₂ R)
    {T : Theory S₁} (hTotal : Theory.WitnessTotalOn R T) (m : M) :
    Models sem₁ m T ↔ Models sem₂ m (Theory.relMap R T) := by
  constructor
  · exact models_relMap_of_models (sem₁ := sem₁) (sem₂ := sem₂) (R := R) (m := m) (T := T) hSound
  · exact models_of_models_relMap_of_witnessTotal (sem₁ := sem₁) (sem₂ := sem₂) (R := R) (m := m) (T := T)
      hComplete hTotal

end Foet
