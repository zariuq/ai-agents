import Foet.SumoEthicsSig
import Foet.EvaluateTheoryParadigms

set_option autoImplicit false

namespace Foet

universe u

/-!
ESOWIKI “Deontology ← Utilitarianism” schemata, Lean-first.

We:
- encode the KIF-shaped “hold philosophy” and “best action by utility in situation” rules as
  type-correct `Formula World` terms over `SumoEthicsSig`;
- give a tiny *best-action* utilitarian fragment whose theories can be translated into
  deontic theories, with evaluator/entailment commutation theorems (under an explicit
  semantic alignment hypothesis).
-/

namespace UtilitarianInDeontology

def allAgentsObligatedToHoldPhilosophy {World : Type u} (sig : SumoEthicsSig World)
    (p : sig.EthicalPhilosophy) : Formula World :=
  fun w => ∀ a : sig.Agent, sig.holdsObligation (sig.holdsEthicalPhilosophy a p) a w

def bestActionByUtilityBody {World : Type u} (sig : SumoEthicsSig World)
    (a : sig.Agent) (uf : sig.UtilityFormulaFn) : Formula World :=
  fun w =>
    ∀ (s : sig.Situation) (c : sig.ProcessClass),
      sig.bestActionByUtilityInSituation c uf s w →
        (sig.agentDoesProcessOfClassInSituation a c s) w

def obligatedToBestActionsByUtility {World : Type u} (sig : SumoEthicsSig World)
    (a : sig.Agent) (uf : sig.UtilityFormulaFn) : Formula World :=
  sig.holdsObligation (bestActionByUtilityBody (World := World) sig a uf) a

/-! ## A best-action utilitarian fragment (literals) -/

inductive BestActionLit {World : Type u} (sig : SumoEthicsSig World)
    (uf : sig.UtilityFormulaFn) (situation : sig.Situation) : Type u where
  | best : sig.ProcessClass → BestActionLit sig uf situation
  | notBest : sig.ProcessClass → BestActionLit sig uf situation

def bestActionLitSemantics {World : Type u} (sig : SumoEthicsSig World)
    (uf : sig.UtilityFormulaFn) (situation : sig.Situation) :
    Semantics (BestActionLit sig uf situation) World :=
  ⟨fun w lit =>
    match lit with
    | .best c => (sig.bestActionByUtilityInSituation c uf situation) w
    | .notBest c => ¬ (sig.bestActionByUtilityInSituation c uf situation) w⟩

def BestActionLit.toDeonticSentence {World : Type u} {sig : SumoEthicsSig World}
    {uf : sig.UtilityFormulaFn} {situation : sig.Situation} (a : sig.Agent) :
    BestActionLit sig uf situation → DeonticSentence World
  | .best c =>
      { tag := .Obligation, formula := sig.agentDoesProcessOfClassInSituation a c situation }
  | .notBest c =>
      { tag := .Prohibition, formula := sig.agentDoesProcessOfClassInSituation a c situation }

abbrev BestActionTheory {World : Type u} (sig : SumoEthicsSig World)
    (uf : sig.UtilityFormulaFn) (situation : sig.Situation) : Type u :=
  Theory (BestActionLit sig uf situation)

def BestActionTheory.toDeonticTheory {World : Type u} {sig : SumoEthicsSig World}
    {uf : sig.UtilityFormulaFn} {situation : sig.Situation} (a : sig.Agent)
    (T : BestActionTheory sig uf situation) :
    DeontologicalImperativeTheory World :=
  Theory.map (BestActionLit.toDeonticSentence (sig := sig) (uf := uf) (situation := situation) a) T

def choicePointOfProcessClasses {World : Type u} (sig : SumoEthicsSig World) (a : sig.Agent) (s : sig.Situation)
    (cp : Set sig.ProcessClass) : ChoicePoint World :=
  fun φ => ∃ c : sig.ProcessClass, c ∈ cp ∧ sig.agentDoesProcessOfClassInSituation a c s = φ

def evaluateBestActionTheoryUnder {World : Type u} (sig : SumoEthicsSig World)
    (uf : sig.UtilityFormulaFn) (situation : sig.Situation) (a : sig.Agent)
    (T : BestActionTheory sig uf situation)
    (ctx : Formula World) (cp : Set sig.ProcessClass) : ValueJudgmentTheory World :=
  fun s =>
    ∃ c : sig.ProcessClass,
      c ∈ cp ∧
        ( (s = morallyGood (sig.agentDoesProcessOfClassInSituation a c situation) ∧
            EntailsUnder (bestActionLitSemantics sig uf situation) T ctx (.best c)) ∨
          (s = morallyBad (sig.agentDoesProcessOfClassInSituation a c situation) ∧
            ¬ EntailsUnder (bestActionLitSemantics sig uf situation) T ctx (.best c) ∧
            EntailsUnder (bestActionLitSemantics sig uf situation) T ctx (.notBest c)) ∨
          (s = morallyPermissible (sig.agentDoesProcessOfClassInSituation a c situation) ∧
            ¬ EntailsUnder (bestActionLitSemantics sig uf situation) T ctx (.best c) ∧
            ¬ EntailsUnder (bestActionLitSemantics sig uf situation) T ctx (.notBest c)) )

/-! ## Entailment + evaluator commutation into deontology -/

theorem entailsUnder_bestActionLit_iff_entailsUnder_deontic_map {World : Type u} {sig : SumoEthicsSig World}
    {uf : sig.UtilityFormulaFn} {situation : sig.Situation} {a : sig.Agent}
    (semD : DeonticSemantics World)
    (h_align :
      ∀ w lit,
        (bestActionLitSemantics sig uf situation).Sat w lit ↔
          (deonticSemantics World semD).Sat w (BestActionLit.toDeonticSentence (sig := sig) (uf := uf) (situation := situation) a lit))
    (T : BestActionTheory sig uf situation)
    (ctx : Formula World) (lit : BestActionLit sig uf situation) :
    EntailsUnder (bestActionLitSemantics sig uf situation) T ctx lit ↔
      EntailsUnder (deonticSemantics World semD)
        (Theory.map (BestActionLit.toDeonticSentence (sig := sig) (uf := uf) (situation := situation) a) T)
        ctx
        (BestActionLit.toDeonticSentence (sig := sig) (uf := uf) (situation := situation) a lit) := by
  simpa using
    (entails_map_iff_under
      (sem₁ := bestActionLitSemantics sig uf situation)
      (sem₂ := deonticSemantics World semD)
      (f := BestActionLit.toDeonticSentence (sig := sig) (uf := uf) (situation := situation) a)
      (h_sat := h_align)
      (T := T) (C := ctx) (s := lit))

theorem entails_bestActionLit_iff_entails_deontic_map {World : Type u} {sig : SumoEthicsSig World}
    {uf : sig.UtilityFormulaFn} {situation : sig.Situation} {a : sig.Agent}
    (semD : DeonticSemantics World)
    (h_align :
      ∀ w lit,
        (bestActionLitSemantics sig uf situation).Sat w lit ↔
          (deonticSemantics World semD).Sat w (BestActionLit.toDeonticSentence (sig := sig) (uf := uf) (situation := situation) a lit))
    (T : BestActionTheory sig uf situation)
    (lit : BestActionLit sig uf situation) :
    Entails (bestActionLitSemantics sig uf situation) T lit ↔
      Entails (deonticSemantics World semD)
        (Theory.map (BestActionLit.toDeonticSentence (sig := sig) (uf := uf) (situation := situation) a) T)
        (BestActionLit.toDeonticSentence (sig := sig) (uf := uf) (situation := situation) a lit) := by
  simpa using
    (entails_map_iff
      (sem₁ := bestActionLitSemantics sig uf situation)
      (sem₂ := deonticSemantics World semD)
      (f := BestActionLit.toDeonticSentence (sig := sig) (uf := uf) (situation := situation) a)
      (h_sat := h_align)
      (T := T) (s := lit))

theorem evaluateBestActionTheoryUnder_eq_evaluateDeonticTheoryUnder_of_align {World : Type u} (sig : SumoEthicsSig World)
    (uf : sig.UtilityFormulaFn) (situation : sig.Situation) (a : sig.Agent)
    (semD : DeonticSemantics World)
    (h_align :
      ∀ w lit,
        (bestActionLitSemantics sig uf situation).Sat w lit ↔
          (deonticSemantics World semD).Sat w (BestActionLit.toDeonticSentence (sig := sig) (uf := uf) (situation := situation) a lit))
    (T : BestActionTheory sig uf situation)
    (ctx : Formula World) (cp : Set sig.ProcessClass) :
    evaluateBestActionTheoryUnder (sig := sig) uf situation a T ctx cp =
      evaluateDeonticTheoryUnder (World := World) semD
        (BestActionTheory.toDeonticTheory (sig := sig) (uf := uf) (situation := situation) a T)
        ctx (choicePointOfProcessClasses (World := World) sig a situation cp) := by
  funext s
  apply propext
  constructor <;> intro hs
  · rcases hs with ⟨c, hc, hCases⟩
    refine ⟨sig.agentDoesProcessOfClassInSituation a c situation, ?_, ?_⟩
    · exact ⟨c, hc, rfl⟩
    have hBest :
        EntailsUnder (bestActionLitSemantics sig uf situation) T ctx (.best c) ↔
          EntailsUnder (deonticSemantics World semD)
            (BestActionTheory.toDeonticTheory (sig := sig) (uf := uf) (situation := situation) a T) ctx
            ({ tag := .Obligation, formula := sig.agentDoesProcessOfClassInSituation a c situation } : DeonticSentence World) := by
      simpa [BestActionTheory.toDeonticTheory, BestActionLit.toDeonticSentence] using
        (entailsUnder_bestActionLit_iff_entailsUnder_deontic_map
          (semD := semD) (sig := sig) (uf := uf) (situation := situation) (a := a) h_align T ctx (.best c))
    have hNotBest :
        EntailsUnder (bestActionLitSemantics sig uf situation) T ctx (.notBest c) ↔
          EntailsUnder (deonticSemantics World semD)
            (BestActionTheory.toDeonticTheory (sig := sig) (uf := uf) (situation := situation) a T) ctx
            ({ tag := .Prohibition, formula := sig.agentDoesProcessOfClassInSituation a c situation } : DeonticSentence World) := by
      simpa [BestActionTheory.toDeonticTheory, BestActionLit.toDeonticSentence] using
        (entailsUnder_bestActionLit_iff_entailsUnder_deontic_map
          (semD := semD) (sig := sig) (uf := uf) (situation := situation) (a := a) h_align T ctx (.notBest c))
    rcases hCases with hGood | hBad | hPerm
    · rcases hGood with ⟨hsEq, hEnt⟩
      exact Or.inl ⟨hsEq, (hBest).1 hEnt⟩
    · rcases hBad with ⟨hsEq, hNotGood, hEntBad⟩
      refine Or.inr (Or.inl ?_)
      refine ⟨hsEq, ?_, (hNotBest).1 hEntBad⟩
      intro hEntGood
      exact hNotGood ((hBest).2 hEntGood)
    · rcases hPerm with ⟨hsEq, hNotGood, hNotBad⟩
      refine Or.inr (Or.inr ?_)
      refine ⟨hsEq, ?_, ?_⟩
      · intro hEntGood
        exact hNotGood ((hBest).2 hEntGood)
      · intro hEntBad
        exact hNotBad ((hNotBest).2 hEntBad)
  · rcases hs with ⟨φ, hφ, hCases⟩
    rcases hφ with ⟨c, hc, hEq⟩
    cases hEq
    refine ⟨c, hc, ?_⟩
    have hBest :
        EntailsUnder (bestActionLitSemantics sig uf situation) T ctx (.best c) ↔
          EntailsUnder (deonticSemantics World semD)
            (BestActionTheory.toDeonticTheory (sig := sig) (uf := uf) (situation := situation) a T) ctx
            ({ tag := .Obligation, formula := sig.agentDoesProcessOfClassInSituation a c situation } : DeonticSentence World) := by
      simpa [BestActionTheory.toDeonticTheory, BestActionLit.toDeonticSentence] using
        (entailsUnder_bestActionLit_iff_entailsUnder_deontic_map
          (semD := semD) (sig := sig) (uf := uf) (situation := situation) (a := a) h_align T ctx (.best c))
    have hNotBest :
        EntailsUnder (bestActionLitSemantics sig uf situation) T ctx (.notBest c) ↔
          EntailsUnder (deonticSemantics World semD)
            (BestActionTheory.toDeonticTheory (sig := sig) (uf := uf) (situation := situation) a T) ctx
            ({ tag := .Prohibition, formula := sig.agentDoesProcessOfClassInSituation a c situation } : DeonticSentence World) := by
      simpa [BestActionTheory.toDeonticTheory, BestActionLit.toDeonticSentence] using
        (entailsUnder_bestActionLit_iff_entailsUnder_deontic_map
          (semD := semD) (sig := sig) (uf := uf) (situation := situation) (a := a) h_align T ctx (.notBest c))
    rcases hCases with hGood | hBad | hPerm
    · rcases hGood with ⟨hsEq, hEnt⟩
      exact Or.inl ⟨hsEq, (hBest).2 hEnt⟩
    · rcases hBad with ⟨hsEq, hNotGood, hEntBad⟩
      refine Or.inr (Or.inl ?_)
      refine ⟨hsEq, ?_, (hNotBest).2 hEntBad⟩
      intro hEntGood
      exact hNotGood ((hBest).1 hEntGood)
    · rcases hPerm with ⟨hsEq, hNotGood, hNotBad⟩
      refine Or.inr (Or.inr ?_)
      refine ⟨hsEq, ?_, ?_⟩
      · intro hEntGood
        exact hNotGood ((hBest).1 hEntGood)
      · intro hEntBad
        exact hNotBad ((hNotBest).1 hEntBad)

end UtilitarianInDeontology

end Foet
