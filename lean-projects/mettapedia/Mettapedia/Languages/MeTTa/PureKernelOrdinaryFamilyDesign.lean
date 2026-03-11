import Mettapedia.Languages.MeTTa.InductiveRecursorContract
import Mettapedia.Languages.MeTTa.OrdinaryFamilyImplementationSeed

/-!
# PureKernel Ordinary-Family Builtin Design

Code-facing design data for the next honest PureKernel extension.

This file does not claim that ordinary families are already implemented in the
kernel. It pins down the built-in starter scope we intend to add next so the
implementation work can follow one explicit contract.
-/

namespace Mettapedia.Languages.MeTTa

/-- The first built-in ordinary families planned for direct PureKernel support. -/
inductive PlannedBuiltinFamily where
  | unit
  | bool
  | nat
deriving DecidableEq, Repr

def PlannedBuiltinFamily.name : PlannedBuiltinFamily → String
  | .unit => "Unit"
  | .bool => "Bool"
  | .nat => "Nat"

/-- The built-in Pure term forms required for the first ordinary-family step. -/
inductive PlannedBuiltinTermForm where
  | unitTy
  | unitMk
  | boolTy
  | boolFalse
  | boolTrue
  | natTy
  | natZero
  | natSucc
  | unitRec
  | boolRec
  | natRec
deriving DecidableEq, Repr

def PlannedBuiltinTermForm.name : PlannedBuiltinTermForm → String
  | .unitTy => "Unit"
  | .unitMk => "unit"
  | .boolTy => "Bool"
  | .boolFalse => "false"
  | .boolTrue => "true"
  | .natTy => "Nat"
  | .natZero => "zero"
  | .natSucc => "succ"
  | .unitRec => "Unit.rec"
  | .boolRec => "Bool.rec"
  | .natRec => "Nat.rec"

structure PlannedBuiltinTermSignature where
  form : PlannedBuiltinTermForm
  family : PlannedBuiltinFamily
  directArgumentCount : Nat
  binderArgumentCount : Nat
  note : String
deriving Repr

structure PlannedRecursorTypingShape where
  recursor : PlannedBuiltinTermForm
  motiveType : String
  minorPremiseTypes : List String
  majorPremiseType : String
  resultType : String
deriving Repr

def plannedBuiltinSignatures : List PlannedBuiltinTermSignature :=
  [ { form := .unitTy
      family := .unit
      directArgumentCount := 0
      binderArgumentCount := 0
      note := "the Unit family as a built-in closed type former" }
  , { form := .unitMk
      family := .unit
      directArgumentCount := 0
      binderArgumentCount := 0
      note := "the unique Unit constructor" }
  , { form := .boolTy
      family := .bool
      directArgumentCount := 0
      binderArgumentCount := 0
      note := "the Bool family as a built-in closed type former" }
  , { form := .boolFalse
      family := .bool
      directArgumentCount := 0
      binderArgumentCount := 0
      note := "the false constructor" }
  , { form := .boolTrue
      family := .bool
      directArgumentCount := 0
      binderArgumentCount := 0
      note := "the true constructor" }
  , { form := .natTy
      family := .nat
      directArgumentCount := 0
      binderArgumentCount := 0
      note := "the Nat family as a built-in closed type former" }
  , { form := .natZero
      family := .nat
      directArgumentCount := 0
      binderArgumentCount := 0
      note := "the zero constructor" }
  , { form := .natSucc
      family := .nat
      directArgumentCount := 1
      binderArgumentCount := 0
      note := "the successor constructor" }
  , { form := .unitRec
      family := .unit
      directArgumentCount := 3
      binderArgumentCount := 0
      note := "dependent eliminator over Unit: motive, unit case, scrutinee" }
  , { form := .boolRec
      family := .bool
      directArgumentCount := 4
      binderArgumentCount := 0
      note := "dependent eliminator over Bool: motive, false case, true case, scrutinee" }
  , { form := .natRec
      family := .nat
      directArgumentCount := 4
      binderArgumentCount := 0
      note := "dependent eliminator over Nat: motive, zero case, succ step, scrutinee" } ]

def plannedRecursorTypingShapes : List PlannedRecursorTypingShape :=
  [ { recursor := .unitRec
      motiveType := "Pi Unit (fun _ => Type1)"
      minorPremiseTypes := ["motive unit"]
      majorPremiseType := "Unit"
      resultType := "motive scrutinee" }
  , { recursor := .boolRec
      motiveType := "Pi Bool (fun _ => Type1)"
      minorPremiseTypes := ["motive false", "motive true"]
      majorPremiseType := "Bool"
      resultType := "motive scrutinee" }
  , { recursor := .natRec
      motiveType := "Pi Nat (fun _ => Type1)"
      minorPremiseTypes :=
        [ "motive zero"
        , "Pi n : Nat, Pi ih : motive n, motive (succ n)" ]
      majorPremiseType := "Nat"
      resultType := "motive scrutinee" } ]

structure PlannedOrdinaryFamilyKernelStep where
  families : List PlannedBuiltinFamily
  signatures : List PlannedBuiltinTermSignature
  recursorShapes : List PlannedRecursorTypingShape
  replacesSeedLayer : Bool
  keepsStructuralFixpointsDeferred : Bool
  firstExecutableMilestone : String
deriving Repr

def plannedOrdinaryFamilyKernelStep : PlannedOrdinaryFamilyKernelStep :=
  { families := [.unit, .bool, .nat]
    signatures := plannedBuiltinSignatures
    recursorShapes := plannedRecursorTypingShapes
    replacesSeedLayer := true
    keepsStructuralFixpointsDeferred := true
    firstExecutableMilestone := "kernel-backed Nat.rec with a checked Nat.isZero demo" }

theorem plannedOrdinaryFamilyKernelStep_familyCount :
    plannedOrdinaryFamilyKernelStep.families.length = 3 := rfl

theorem plannedOrdinaryFamilyKernelStep_replacesSeedLayer :
    plannedOrdinaryFamilyKernelStep.replacesSeedLayer = true := rfl

theorem plannedOrdinaryFamilyKernelStep_keepsStructuralFixpointsDeferred :
    plannedOrdinaryFamilyKernelStep.keepsStructuralFixpointsDeferred = true := rfl

theorem plannedOrdinaryFamilyKernelStep_firstMilestone :
    plannedOrdinaryFamilyKernelStep.firstExecutableMilestone =
      "kernel-backed Nat.rec with a checked Nat.isZero demo" := rfl

theorem plannedOrdinaryFamilyKernelStep_aligns_with_unitContract :
    unitRecursorContract.recursorName = PlannedBuiltinTermForm.name .unitRec := by
  rfl

theorem plannedOrdinaryFamilyKernelStep_aligns_with_boolContract :
    boolRecursorContract.recursorName = PlannedBuiltinTermForm.name .boolRec := by
  rfl

theorem plannedOrdinaryFamilyKernelStep_aligns_with_natContract :
    natRecursorContract.recursorName = PlannedBuiltinTermForm.name .natRec := by
  rfl

theorem plannedOrdinaryFamilyKernelStep_refines_currentSeedNames :
    checkedUnitFamily.extension.declaration.familyName = PlannedBuiltinFamily.name .unit ∧
      checkedBoolFamily.extension.declaration.familyName = PlannedBuiltinFamily.name .bool ∧
      checkedNatFamily.extension.declaration.familyName = PlannedBuiltinFamily.name .nat := by
  constructor
  · exact checkedUnitFamily_familyName
  constructor
  · exact checkedBoolFamily_familyName
  · exact checkedNatFamily_familyName

end Mettapedia.Languages.MeTTa
