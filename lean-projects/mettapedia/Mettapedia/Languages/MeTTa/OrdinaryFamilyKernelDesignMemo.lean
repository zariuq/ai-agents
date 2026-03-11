import Mettapedia.Languages.MeTTa.InductiveKernelExtension
import Mettapedia.Languages.MeTTa.PureCheckingExtensions

/-!
# General Ordinary-Family Kernel Design Memo

This file is a design memo for the next real `PureKernel` implementation step.
It is intentionally **not** imported by the trusted umbrella path.

The purpose is to make one thing explicit before implementation resumes:

- ordinary families must enter `PureKernel` through a **general mechanism**,
- `Unit`, `Bool`, and `Nat` must arise as instances of that mechanism,
- and `Unit` is the first proving ground for the implementation.

The memo is code-adjacent on purpose: it names the objects, obligations, and
phase order in Lean terms, but it does not pretend the mechanism is already
implemented.
-/

namespace Mettapedia.Languages.MeTTa

/-- What route the next kernel extension is allowed to take. -/
inductive OrdinaryFamilyKernelRoute where
  | declarationEnvWithSymbolicRefs
  | familySpecificBuiltinsRejected
deriving DecidableEq, Repr

/-- The design choice for the next implementation pass. -/
def chosenOrdinaryFamilyKernelRoute : OrdinaryFamilyKernelRoute :=
  .declarationEnvWithSymbolicRefs

/-- Generic references into the future ordinary-family declaration environment.

The key idea is that the kernel should not gain `NatRec`, `BoolRec`, etc.
Instead, the term language should refer to declarations through generic
symbols whose meaning is supplied by the ordinary-family environment.
-/
structure OrdinaryFamilyRefs where
  familyName : String
  ctorName : Option String := none
  recursorName : Option String := none
deriving DecidableEq, Repr

/-- The minimal new term-form classes the general mechanism should provide.

This is deliberately generic. It describes the *kind* of syntax extension
required, not family-specific constructors.
-/
inductive OrdinaryFamilyTermForm where
  | familyConst
  | ctorConst
  | recursorConst
  | motiveApp
  | ctorApp
  | recursorApp
deriving DecidableEq, Repr

/-- The declaration environment shape needed by the next implementation pass. -/
structure OrdinaryFamilyDeclarationEnv where
  declarations : List OrdinaryFamilyDeclaration
  familyNamesDistinct : declarations.Pairwise (fun a b => a.familyName ≠ b.familyName)
deriving Repr

/-- The kernel needs one explicit naming discipline for declared family items.

The immediate goal is not to settle parser syntax. It is to say what kind of
references the trusted term language may carry once ordinary families are
admitted through a declaration environment.
-/
inductive OrdinaryFamilyRefForm where
  | familyRefByName
  | ctorRefByQualifiedName
  | recursorRefByQualifiedName
deriving DecidableEq, Repr

/-- The current design choice for kernel references into the declaration
environment.

We choose symbolic names first because:

- the surrounding spec/interface layers already speak in names,
- `Unit` as the pilot does not need de Bruijn-style declaration indices to test
  the mechanism,
- and bridge/paper/debugging work stays legible while the mechanism is being
  stabilized.

If we later want a compiled/indexed internal form, it should come after the
symbolic route is correct, not instead of it.
-/
def chosenOrdinaryFamilyRefForm : OrdinaryFamilyRefForm :=
  .familyRefByName

/-- Generic references carried by the future trusted kernel terms.

These references are generic on purpose:
- no `Nat.rec`,
- no `Bool.true`,
- no `Unit.unit` baked into the AST shape.

Instead, one term form will carry one of these references, and typing/reduction
will consult the declaration environment to interpret it.
-/
inductive KernelOrdinaryFamilyRef where
  | family (familyName : String)
  | ctor (familyName ctorName : String)
  | recursor (familyName recursorName : String)
deriving DecidableEq, Repr

/-- Generic declaration-driven forms the trusted kernel will need once ordinary
families are live.

These are still design objects, not a change to `PureTm` yet.

- `declConst` is the closed symbolic head for a family/constructor/recursor.
- `declElim` is the elimination form whose computation rules depend on the
  declaration environment.

The important point is that `Unit`, `Bool`, and `Nat` must all reuse these
same forms.
-/
inductive PlannedOrdinaryFamilyKernelForm where
  | declConst (ref : KernelOrdinaryFamilyRef)
  | declElim (recursorRef : KernelOrdinaryFamilyRef)
deriving DecidableEq, Repr

/-- Files that must move in lockstep once the general mechanism starts landing.

This is the anti-drift checklist for the real kernel extension. -/
def ordinaryFamilyKernelTouchSet : List String :=
  [ "Mettapedia/Languages/MeTTa/PureKernel/Syntax.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/Renaming.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/Substitution.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/Typing.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/Reduction.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/AlgorithmicTyping.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/Parallel.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/Confluence.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/SubjectReduction.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/PatternBridge.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/CoreEmbedding.lean"
  , "Mettapedia/Languages/MeTTa/PureCertificateFragment.lean"
  , "Mettapedia/Languages/MeTTa/PureCheckingService.lean"
  , "Mettapedia/Languages/MeTTa/PureNormalizationService.lean"
  , "Mettapedia/Languages/MeTTa/PureCanonicalEvaluation.lean" ]

/-- The minimal live-kernel files that must change for the `Unit` pilot itself.

This is the implementation checklist we want to satisfy before broadening to
`Bool` or `Nat`.
-/
def unitPilotKernelTouchSet : List String :=
  [ "Mettapedia/Languages/MeTTa/PureKernel/Syntax.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/Renaming.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/Substitution.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/Typing.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/Reduction.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/AlgorithmicTyping.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/SubjectReduction.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/PatternBridge.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/CoreEmbedding.lean"
  , "Mettapedia/Languages/MeTTa/PureCertificateFragment.lean" ]

/-- The first implementation proving ground.

`Unit` is the pilot because it has:
- zero parameters,
- zero indices,
- one nullary constructor,
- the smallest nontrivial recursor story.
-/
def ordinaryFamilyPilot : OrdinaryFamilyDeclaration :=
  unitKernelExtension.declaration

/-- The order in which the first concrete instances should land. -/
def ordinaryFamilyPilotOrder : List OrdinaryFamilyDeclaration :=
  [ unitKernelExtension.declaration
  , boolKernelExtension.declaration
  , natKernelExtension.declaration ]

/-- The declaration environment responsibilities that typing/reduction must
share.

This is the central representation checkpoint before implementation:
- syntax may mention only generic declaration references,
- typing must validate those references against the environment,
- reduction must consult the same environment for recursor computation.
-/
structure OrdinaryFamilyKernelEnvironmentContract where
  declarationEnv : OrdinaryFamilyDeclarationEnv
  referenceForm : OrdinaryFamilyRefForm
  termForms : List PlannedOrdinaryFamilyKernelForm
  typingConsultsEnv : Bool
  reductionConsultsEnv : Bool
  generatedRecursorsComeFromDeclarations : Bool
deriving Repr

/-- The implementation-ready environment contract for the next pass. -/
def ordinaryFamilyKernelEnvironmentContract : OrdinaryFamilyKernelEnvironmentContract :=
  { declarationEnv :=
      { declarations := ordinaryFamilyPilotOrder
        familyNamesDistinct := by
          native_decide }
    referenceForm := chosenOrdinaryFamilyRefForm
    termForms :=
      [ .declConst (.family "Unit")
      , .declConst (.ctor "Unit" "unit")
      , .declConst (.recursor "Unit" "Unit.rec")
      , .declElim (.recursor "Unit" "Unit.rec") ]
    typingConsultsEnv := true
    reductionConsultsEnv := true
    generatedRecursorsComeFromDeclarations := true }

/-- The exact kind of success criterion we want from the first pass. -/
structure OrdinaryFamilyPilotSuccess where
  route : OrdinaryFamilyKernelRoute
  pilotFamily : String
  noFamilySpecificAstGrowth : Bool
  generatedRecursorComesFromDeclaration : Bool
  checkingBoundaryStillAuthoritative : Bool
  subjectReductionReestablished : Bool
  canonicalizationUpdated : Bool
  bridgeQuotingUpdated : Bool
deriving Repr

/-- File-by-file obligations for the first `Unit` pilot.

This is meant to prevent the common “we implemented the constructor but forgot
the bridge/theory side” failure mode.
-/
structure UnitPilotTouchPoint where
  file : String
  obligation : String
deriving DecidableEq, Repr

def unitPilotTouchPoints : List UnitPilotTouchPoint :=
  [ { file := "Mettapedia/Languages/MeTTa/PureKernel/Syntax.lean"
      obligation := "add generic declaration-driven family/constructor/recursor term forms; do not add family-specific Unit constructors" }
  , { file := "Mettapedia/Languages/MeTTa/PureKernel/Renaming.lean"
      obligation := "thread renaming through the new generic declaration-driven forms" }
  , { file := "Mettapedia/Languages/MeTTa/PureKernel/Substitution.lean"
      obligation := "thread substitution through the new generic declaration-driven forms" }
  , { file := "Mettapedia/Languages/MeTTa/PureKernel/Typing.lean"
      obligation := "typecheck Unit family references, Unit constructor references, and Unit.rec by consulting the declaration environment" }
  , { file := "Mettapedia/Languages/MeTTa/PureKernel/Reduction.lean"
      obligation := "add only the declaration-driven Unit.rec computation equation for the Unit constructor" }
  , { file := "Mettapedia/Languages/MeTTa/PureKernel/AlgorithmicTyping.lean"
      obligation := "teach the checker how to recognize declaration-driven Unit family/constructor/recursor heads without family-specific shortcuts" }
  , { file := "Mettapedia/Languages/MeTTa/PureKernel/SubjectReduction.lean"
      obligation := "re-establish subject reduction for the declaration-driven Unit recursor computation rule" }
  , { file := "Mettapedia/Languages/MeTTa/PureKernel/PatternBridge.lean"
      obligation := "quote declaration-driven Unit family/constructor/recursor forms honestly into shared artifacts" }
  , { file := "Mettapedia/Languages/MeTTa/PureKernel/CoreEmbedding.lean"
      obligation := "re-establish the Pure-to-profile bridge facts for the declaration-driven Unit recursor computation rule" }
  , { file := "Mettapedia/Languages/MeTTa/PureCertificateFragment.lean"
      obligation := "extend the restricted certificate lane only if the new generic Unit-backed kernel terms are already live and quote correctly" } ]

/-- The target success profile for the first `Unit` implementation pass. -/
def unitPilotSuccessTarget : OrdinaryFamilyPilotSuccess :=
  { route := chosenOrdinaryFamilyKernelRoute
    pilotFamily := "Unit"
    noFamilySpecificAstGrowth := true
    generatedRecursorComesFromDeclaration := true
    checkingBoundaryStillAuthoritative := true
    subjectReductionReestablished := true
    canonicalizationUpdated := true
    bridgeQuotingUpdated := true }

/-- The implementation phase order that keeps the project at the right layer. -/
def ordinaryFamilyPhaseOrder : List String :=
  [ "freeze the current Pure checking/canonicalization waist"
  , "add the general ordinary-family declaration environment"
  , "extend PureKernel syntax with generic declaration-driven family/ctor/recursor references"
  , "thread renaming and substitution through the generic forms"
  , "add declarative typing for declaration-driven ordinary families"
  , "add recursor computation rules from the declaration environment"
  , "re-establish algorithmic typing, confluence, and subject reduction"
  , "re-establish quotation, profile, and certificate bridges"
  , "land Unit as the first instance"
  , "land Bool, then Nat"
  , "only then stage structural fixpoints above the family mechanism" ]

theorem chosenOrdinaryFamilyKernelRoute_is_general :
    chosenOrdinaryFamilyKernelRoute = .declarationEnvWithSymbolicRefs := rfl

theorem chosenOrdinaryFamilyRefForm_is_symbolic :
    chosenOrdinaryFamilyRefForm = .familyRefByName := rfl

theorem ordinaryFamilyKernelEnvironmentContract_typingConsultsEnv :
    ordinaryFamilyKernelEnvironmentContract.typingConsultsEnv = true := rfl

theorem ordinaryFamilyKernelEnvironmentContract_reductionConsultsEnv :
    ordinaryFamilyKernelEnvironmentContract.reductionConsultsEnv = true := rfl

theorem ordinaryFamilyKernelEnvironmentContract_generatesRecursorsFromDeclarations :
    ordinaryFamilyKernelEnvironmentContract.generatedRecursorsComeFromDeclarations = true := rfl

theorem ordinaryFamilyPilot_is_unit :
    ordinaryFamilyPilot.familyName = "Unit" := by
  rfl

theorem ordinaryFamilyPilotOrder_head_is_unit :
    ordinaryFamilyPilotOrder.head? = some ordinaryFamilyPilot := by
  rfl

theorem unitPilotSuccessTarget_rejects_familySpecificAstGrowth :
    unitPilotSuccessTarget.noFamilySpecificAstGrowth = true := rfl

theorem unitPilotSuccessTarget_requires_generatedRecursorFromDeclaration :
    unitPilotSuccessTarget.generatedRecursorComesFromDeclaration = true := rfl

theorem unitPilotKernelTouchSet_head_is_syntax :
    unitPilotKernelTouchSet.head? =
      some "Mettapedia/Languages/MeTTa/PureKernel/Syntax.lean" := by
  rfl

theorem unitPilotTouchPoints_head_is_syntax :
    unitPilotTouchPoints.head?.map UnitPilotTouchPoint.file =
      some "Mettapedia/Languages/MeTTa/PureKernel/Syntax.lean" := by
  rfl

theorem ordinaryFamilyPhaseOrder_starts_with_waist_freeze :
    ordinaryFamilyPhaseOrder.head? = some "freeze the current Pure checking/canonicalization waist" := by
  rfl

end Mettapedia.Languages.MeTTa
