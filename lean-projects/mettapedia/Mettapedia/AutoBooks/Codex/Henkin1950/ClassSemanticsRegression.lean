import Mettapedia.AutoBooks.Codex.Henkin1950.ClassSemantics

namespace Mettapedia.AutoBooks.Codex.Henkin1950

/-!
# Henkin 1950 Class Semantics Regression

Positive and negative canaries for the paper-faithful class-semantics endpoint.
-/

namespace Regression

open Mettapedia.Logic.HOL

example
    (M : CanonicalClassModel)
    (ν : M.toClassGeneralModel.Assignment Γ)
    (φ : Formula Γ) :
    M.toClassGeneralModel.denoteFormula ν φ ↔ M.denoteFormula ν φ :=
  M.toClassGeneralModel_denoteFormula_iff ν φ

example
    (M : CanonicalClassModel) :
    ¬ M.toClassGeneralModel.models (.bot : Sentence) := by
  intro hBot
  have hCanon :
      M.denoteFormula M.emptyAssignment (.bot : Sentence) :=
    (M.toClassGeneralModel_models_iff (.bot : Sentence)).1 hBot
  exact (M.denoteFormula_bot_iff_false M.emptyAssignment).1 hCanon

example
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T) :
    SatisfiableInClassGeneral T :=
  CanonicalClassModel.theorem1_classGeneral hT hEx hAll

example
    (M : CanonicalClassModel.CanonicalDescriptionModel) :
    DescriptionAxiomClosed M.T :=
  M.descriptionAxiomClosed

example
    (M : CanonicalClassModel.CanonicalDescriptionModel) :
    SatisfiableInClassDescription M.T :=
  M.satisfiableInClassDescription

example
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    (hA11 : DescriptionAxiomClosed T) :
    SatisfiableInClassDescription T :=
  theorem1_classDescription hT hEx hAll hA11

end Regression

end Mettapedia.AutoBooks.Codex.Henkin1950
