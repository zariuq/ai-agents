import Foet.ChoicePoint

set_option autoImplicit false

namespace Foet

universe u

def valueSentence {World : Type u} (tag : MoralValueAttribute) (φ : Formula World) : ValueJudgmentSentence World :=
  { tag := tag, formula := φ }

def morallyGood {World : Type u} (φ : Formula World) : ValueJudgmentSentence World :=
  valueSentence .MorallyGood φ

def morallyBad {World : Type u} (φ : Formula World) : ValueJudgmentSentence World :=
  valueSentence .MorallyBad φ

def morallyPermissible {World : Type u} (φ : Formula World) : ValueJudgmentSentence World :=
  valueSentence .MorallyPermissible φ

/-
`evaluateTheory` (ESOWIKI / FOET KIF) in the Lean MVP.

Given:
  - a value-judgment semantics `semV`
  - a value-judgment theory `T` (set of sentences)
  - a choice point `cp` (set of alternative action formulas)

Return a theory that assigns each option in `cp` a simple moral tag:
  1) If `T ⊨ Good φ`, output `Good φ`
  2) Else if `T ⊨ Bad φ`, output `Bad φ`
  3) Else output `Permissible φ`

We encode this as a *set of sentences* (a predicate) to avoid requiring decidability of entailment.
-/

def evaluateTheory {World : Type u} (semV : ValueSemantics World) (T : ValueJudgmentTheory World) (cp : ChoicePoint World) :
    ValueJudgmentTheory World :=
  fun s =>
    ∃ φ, φ ∈ cp ∧
      ( (s = morallyGood φ ∧ Entails (valueJudgmentSemantics World semV) T (morallyGood φ)) ∨
        (s = morallyBad φ ∧ ¬ Entails (valueJudgmentSemantics World semV) T (morallyGood φ) ∧
          Entails (valueJudgmentSemantics World semV) T (morallyBad φ)) ∨
        (s = morallyPermissible φ ∧ ¬ Entails (valueJudgmentSemantics World semV) T (morallyGood φ) ∧
          ¬ Entails (valueJudgmentSemantics World semV) T (morallyBad φ)) )

/-! ## Contextual (situational) evaluation -/

/--
`evaluateTheory` with an extra “situation description” premise `ctx`.

This matches the FOET KIF idea:
  `entails (and (ListAndFn (SetToListFn T)) ctx) sentence`

except that we encode `ctx` as a model-side restriction (`World → Prop`) rather than as an
additional object-language sentence.
-/
def evaluateTheoryUnder {World : Type u} (semV : ValueSemantics World) (T : ValueJudgmentTheory World)
    (ctx : Formula World) (cp : ChoicePoint World) : ValueJudgmentTheory World :=
  fun s =>
    ∃ φ, φ ∈ cp ∧
      ( (s = morallyGood φ ∧ EntailsUnder (valueJudgmentSemantics World semV) T ctx (morallyGood φ)) ∨
        (s = morallyBad φ ∧ ¬ EntailsUnder (valueJudgmentSemantics World semV) T ctx (morallyGood φ) ∧
          EntailsUnder (valueJudgmentSemantics World semV) T ctx (morallyBad φ)) ∨
        (s = morallyPermissible φ ∧ ¬ EntailsUnder (valueJudgmentSemantics World semV) T ctx (morallyGood φ) ∧
          ¬ EntailsUnder (valueJudgmentSemantics World semV) T ctx (morallyBad φ)) )

theorem morallyGood_mem_evaluateTheoryUnder {World : Type u} {semV : ValueSemantics World} {T : ValueJudgmentTheory World}
    {ctx : Formula World} {cp : ChoicePoint World} {φ : Formula World}
    (hφ : φ ∈ cp) (hEnt : EntailsUnder (valueJudgmentSemantics World semV) T ctx (morallyGood φ)) :
    morallyGood φ ∈ evaluateTheoryUnder (World := World) semV T ctx cp :=
  ⟨φ, hφ, Or.inl ⟨rfl, hEnt⟩⟩

theorem morallyBad_mem_evaluateTheoryUnder {World : Type u} {semV : ValueSemantics World} {T : ValueJudgmentTheory World}
    {ctx : Formula World} {cp : ChoicePoint World} {φ : Formula World}
    (hφ : φ ∈ cp)
    (hNotGood : ¬ EntailsUnder (valueJudgmentSemantics World semV) T ctx (morallyGood φ))
    (hBad : EntailsUnder (valueJudgmentSemantics World semV) T ctx (morallyBad φ)) :
    morallyBad φ ∈ evaluateTheoryUnder (World := World) semV T ctx cp :=
  ⟨φ, hφ, Or.inr (Or.inl ⟨rfl, hNotGood, hBad⟩)⟩

theorem morallyPermissible_mem_evaluateTheoryUnder {World : Type u} {semV : ValueSemantics World} {T : ValueJudgmentTheory World}
    {ctx : Formula World} {cp : ChoicePoint World} {φ : Formula World}
    (hφ : φ ∈ cp)
    (hNotGood : ¬ EntailsUnder (valueJudgmentSemantics World semV) T ctx (morallyGood φ))
    (hNotBad : ¬ EntailsUnder (valueJudgmentSemantics World semV) T ctx (morallyBad φ)) :
    morallyPermissible φ ∈ evaluateTheoryUnder (World := World) semV T ctx cp :=
  ⟨φ, hφ, Or.inr (Or.inr ⟨rfl, hNotGood, hNotBad⟩)⟩

structure SituatedChoicePoint (World : Type u) : Type u where
  options : ChoicePoint World
  context : Formula World

def evaluateSituated {World : Type u} (semV : ValueSemantics World) (T : ValueJudgmentTheory World)
    (scp : SituatedChoicePoint World) : ValueJudgmentTheory World :=
  evaluateTheoryUnder (World := World) semV T scp.context scp.options

theorem formula_mem_of_mem_evaluateTheory {World : Type u} {semV : ValueSemantics World} {T : ValueJudgmentTheory World}
    {cp : ChoicePoint World} {s : ValueJudgmentSentence World}
    (hs : s ∈ evaluateTheory (World := World) semV T cp) :
    s.formula ∈ cp := by
  rcases hs with ⟨φ, hφ, hCases⟩
  rcases hCases with hGood | hBad | hPerm
  · rcases hGood with ⟨hsEq, _⟩
    simpa [morallyGood, valueSentence, hsEq] using hφ
  · rcases hBad with ⟨hsEq, _, _⟩
    simpa [morallyBad, valueSentence, hsEq] using hφ
  · rcases hPerm with ⟨hsEq, _, _⟩
    simpa [morallyPermissible, valueSentence, hsEq] using hφ

theorem morallyGood_mem_evaluateTheory {World : Type u} {semV : ValueSemantics World} {T : ValueJudgmentTheory World}
    {cp : ChoicePoint World} {φ : Formula World}
    (hφ : φ ∈ cp) (hEnt : Entails (valueJudgmentSemantics World semV) T (morallyGood φ)) :
    morallyGood φ ∈ evaluateTheory (World := World) semV T cp :=
  ⟨φ, hφ, Or.inl ⟨rfl, hEnt⟩⟩

theorem morallyBad_mem_evaluateTheory {World : Type u} {semV : ValueSemantics World} {T : ValueJudgmentTheory World}
    {cp : ChoicePoint World} {φ : Formula World}
    (hφ : φ ∈ cp)
    (hNotGood : ¬ Entails (valueJudgmentSemantics World semV) T (morallyGood φ))
    (hBad : Entails (valueJudgmentSemantics World semV) T (morallyBad φ)) :
    morallyBad φ ∈ evaluateTheory (World := World) semV T cp :=
  ⟨φ, hφ, Or.inr (Or.inl ⟨rfl, hNotGood, hBad⟩)⟩

theorem morallyPermissible_mem_evaluateTheory {World : Type u} {semV : ValueSemantics World} {T : ValueJudgmentTheory World}
    {cp : ChoicePoint World} {φ : Formula World}
    (hφ : φ ∈ cp)
    (hNotGood : ¬ Entails (valueJudgmentSemantics World semV) T (morallyGood φ))
    (hNotBad : ¬ Entails (valueJudgmentSemantics World semV) T (morallyBad φ)) :
    morallyPermissible φ ∈ evaluateTheory (World := World) semV T cp :=
  ⟨φ, hφ, Or.inr (Or.inr ⟨rfl, hNotGood, hNotBad⟩)⟩

theorem evaluateTheory_eq_of_equivalent {World : Type u} (semV : ValueSemantics World)
    {T₁ T₂ : ValueJudgmentTheory World}
    (hEq : Equivalent (valueJudgmentSemantics World semV) T₁ T₂)
    (cp : ChoicePoint World) :
    evaluateTheory (World := World) semV T₁ cp = evaluateTheory (World := World) semV T₂ cp := by
  funext s
  apply propext
  constructor
  · intro hs
    rcases hs with ⟨φ, hφ, hCases⟩
    refine ⟨φ, hφ, ?_⟩
    rcases hCases with hGood | hBad | hPerm
    · rcases hGood with ⟨hs, hEnt⟩
      exact Or.inl ⟨hs, (hEq (morallyGood φ)).1 hEnt⟩
    · rcases hBad with ⟨hs, hNotGood, hEntBad⟩
      refine Or.inr (Or.inl ?_)
      refine ⟨hs, ?_, (hEq (morallyBad φ)).1 hEntBad⟩
      intro hEntGood
      exact hNotGood ((hEq (morallyGood φ)).2 hEntGood)
    · rcases hPerm with ⟨hs, hNotGood, hNotBad⟩
      refine Or.inr (Or.inr ?_)
      refine ⟨hs, ?_, ?_⟩
      · intro hEntGood
        exact hNotGood ((hEq (morallyGood φ)).2 hEntGood)
      · intro hEntBad
        exact hNotBad ((hEq (morallyBad φ)).2 hEntBad)
  · intro hs
    rcases hs with ⟨φ, hφ, hCases⟩
    refine ⟨φ, hφ, ?_⟩
    rcases hCases with hGood | hBad | hPerm
    · rcases hGood with ⟨hs, hEnt⟩
      exact Or.inl ⟨hs, (hEq (morallyGood φ)).2 hEnt⟩
    · rcases hBad with ⟨hs, hNotGood, hEntBad⟩
      refine Or.inr (Or.inl ?_)
      refine ⟨hs, ?_, (hEq (morallyBad φ)).2 hEntBad⟩
      intro hEntGood
      exact hNotGood ((hEq (morallyGood φ)).1 hEntGood)
    · rcases hPerm with ⟨hs, hNotGood, hNotBad⟩
      refine Or.inr (Or.inr ?_)
      refine ⟨hs, ?_, ?_⟩
      · intro hEntGood
        exact hNotGood ((hEq (morallyGood φ)).1 hEntGood)
      · intro hEntBad
        exact hNotBad ((hEq (morallyBad φ)).1 hEntBad)

end Foet
