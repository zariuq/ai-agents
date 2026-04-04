import Mettapedia.Logic.HOL.PlainIntuitionistic
import Mettapedia.Logic.HOL.OriginalReflectionReduction

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace HenkinConstInfinity

/--
Auxiliary composition theorem at the exact minimal proof-theoretic boundary
actually consumed by the represented-canonical route.

This theorem does not ask for a full source reflection target. It asks only for
the contrapositive lifted-nonprovability payload already expected by the public
canonical completeness theorem.
-/
theorem plain_intuitionistic_completeness_of_witnessedLiftNotProvable_via_canonicalRepresented
    (W : BaseWitnesses Base Const)
    (hLiftNot :
      WitnessedLiftNotProvableGoal (Base := Base) (Const := Const) W)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, v + 1} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact PlainIntuitionistic.plain_intuitionistic_completeness_of_liftBase_notProvable_via_canonicalRepresented
    (Base := Base)
    (Const := Const)
    (hLiftNotProvable := by
      intro Δ φ hNot
      exact hLiftNot hNot)

/--
Auxiliary composition theorem from a witnessed original-reflection target to
the live represented-canonical plain completeness reduction.

This does not change the mainline entrypoint in `PlainIntuitionistic`. It only
shows that once the auxiliary proof-theoretic reflection target is available,
the already-green represented-canonical countermodel route discharges plain
intuitionistic completeness immediately.
-/
theorem plain_intuitionistic_completeness_of_witnessedOriginalReflectionTarget_via_canonicalRepresented
    (R : WitnessedOriginalReflectionTarget (Base := Base) (Const := Const))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, v + 1} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact plain_intuitionistic_completeness_of_witnessedLiftNotProvable_via_canonicalRepresented
    (Base := Base)
    (Const := Const)
    R.witnesses
    (hLiftNot :=
      witnessedLiftNotProvableGoal_of_witnessedOriginalReflectionTarget
        (Base := Base)
        (Const := Const)
        R)

/--
Concrete auxiliary composition corollary from recursive witnessed
conservativity.

Once the witnessed conservativity package is proved at every stage, the plain
intuitionistic completeness theorem follows through the represented-canonical
Route 1 bridge with no further semantic work.
-/
theorem plain_intuitionistic_completeness_of_witnessedTheoryConservativity_via_canonicalRepresented
    (W : BaseWitnesses Base Const)
    (hCons :
      ∀ n : Nat,
        WitnessedTheoryConservativityGoal
          (Base := Base)
          (Const := HenkinConstStage Base Const n)
          (baseWitnessesOf (Base := Base) (Const := Const) W n))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, v + 1} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact plain_intuitionistic_completeness_of_witnessedLiftNotProvable_via_canonicalRepresented
    (Base := Base)
    (Const := Const)
    W
    (hLiftNot := witnessedLiftNotProvableGoal_of_witnessedTheoryConservativity
      (Base := Base)
      (Const := Const)
      W
      hCons)

/--
Concrete auxiliary composition theorem reducing the witnessed-reflection detour
to a single remaining stage-language theorem.

The finite-stage reduction side is already proved in
`OriginalReflectionReduction`; only the concrete one-step stage reflection
theorem remains.
-/
theorem plain_intuitionistic_completeness_of_stageLanguageOneStepReflection_via_canonicalRepresented
    (W : BaseWitnesses Base Const)
    (hStep : StageLanguageOneStepReflectionGoal (Base := Base) (Const := Const))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, v + 1} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact plain_intuitionistic_completeness_of_witnessedOriginalReflectionTarget_via_canonicalRepresented
    (Base := Base)
    (Const := Const)
    (R := stageLanguageWitnessedOriginalReflectionTarget
      (Base := Base)
      (Const := Const)
      W
      (stageLanguageFiniteReduction_of_supportedOriginalLift
        (Base := Base)
        (Const := Const)
        (supportedOriginalLiftConstructionGoal_proved
          (Base := Base)
          (Const := Const)))
      hStep)

/--
Cleaner auxiliary composition theorem at the recursive-stage boundary.

This packages the same reflected route as the stage-language theorem above, but
at the better abstraction layer already preferred internally by
`OriginalReflectionReduction`.
-/
theorem plain_intuitionistic_completeness_of_recursiveStageOneStepReflection_via_canonicalRepresented
    (W : BaseWitnesses Base Const)
    (hStep : RecursiveStageOneStepReflectionGoal (Base := Base) (Const := Const))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, v + 1} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact plain_intuitionistic_completeness_of_witnessedOriginalReflectionTarget_via_canonicalRepresented
    (Base := Base)
    (Const := Const)
    (R := (recursiveStageWitnessedStageReductionPackage
      (Base := Base)
      (Const := Const)
      W).toWitnessedOriginalReflectionTarget hStep)

/--
Cleaner auxiliary completeness theorem at the exact-step boundary.

The recursive-stage one-step theorem is now reduced to the local exact-step
reflection theorem in `OriginalReflectionReduction`, so this is the sharper
remaining proof-theoretic surface for the auxiliary route.
-/
theorem plain_intuitionistic_completeness_of_exactStepReflection_via_canonicalRepresented
    (W : BaseWitnesses Base Const)
    (hExact : ExactStepReflectionGoal (Base := Base) (Const := Const))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, v + 1} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact plain_intuitionistic_completeness_of_recursiveStageOneStepReflection_via_canonicalRepresented
    (Base := Base)
    (Const := Const)
    W
    (hStep := recursiveStageOneStepReflection_of_exactStepReflection
      (Base := Base)
      (Const := Const)
      hExact)

end HenkinConstInfinity

end Mettapedia.Logic.HOL
