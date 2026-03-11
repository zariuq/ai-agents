import Mettapedia.Languages.MeTTa.PureNormalizationService
import Mettapedia.Languages.MeTTa.PurePrototypeEval

/-!
# Pure Semantic Waist

Central service-level API for the current closed MeTTa-Pure waist.

This module treats canonical development as the reference conversion anchor and
packages executable evaluator agreement with that anchor via an explicit common
reduct, rather than by pretending that complete development is the evaluator's
final normal form.
-/

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.PureKernel
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Confluence
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PurePrototypeEval

/-- A stronger agreement package between the executable fuel evaluator and the
canonical-development service than bare convertibility: both sides reduce to an
explicit common reduct. -/
structure ExecutableCanonicalAgreement where
  input : PureTm 0
  fuel : Nat
  executableResult : PureTm 0
  canonical : CanonicalClosedPureTerm
  canonicalInput_eq : canonical.input = input
  inputToExecutable : RedStar input executableResult
  commonReduct : PureTm 0
  executableToCommonReduct : RedStar executableResult commonReduct
  canonicalToCommonReduct : RedStar canonical.canonicalDevelopment commonReduct

namespace ExecutableCanonicalAgreement

def executableArtifact (agreement : ExecutableCanonicalAgreement) : SharedArtifact :=
  ⟨quoteClosedTm agreement.executableResult⟩

theorem executableQuoteAgreement
    (agreement : ExecutableCanonicalAgreement) :
    agreement.executableArtifact.pattern =
      quoteClosedTm agreement.executableResult := rfl

def executableWitness
    (agreement : ExecutableCanonicalAgreement) :
    ConversionWitness agreement.executableResult agreement.canonical.canonicalDevelopment :=
  { commonReduct := agreement.commonReduct
    leftReduces := agreement.executableToCommonReduct
    rightReduces := agreement.canonicalToCommonReduct }

theorem executableConvCanonical
    (agreement : ExecutableCanonicalAgreement) :
    Conv agreement.executableResult agreement.canonical.canonicalDevelopment :=
  agreement.executableWitness.toConv

theorem inputToCanonical
    (agreement : ExecutableCanonicalAgreement) :
    RedStar agreement.input agreement.canonical.canonicalDevelopment :=
  by
    simpa [agreement.canonicalInput_eq] using agreement.canonical.reductionToCanonicalDevelopment

theorem inputToCommonReduct
    (agreement : ExecutableCanonicalAgreement) :
    RedStar agreement.input agreement.commonReduct :=
  RedStar.trans agreement.inputToExecutable agreement.executableToCommonReduct

def canonicalArtifact (agreement : ExecutableCanonicalAgreement) : SharedArtifact :=
  agreement.canonical.artifact

theorem canonicalQuoteAgreement
    (agreement : ExecutableCanonicalAgreement) :
    agreement.canonicalArtifact.pattern =
      quoteClosedTm agreement.canonical.canonicalDevelopment :=
  agreement.canonical.quoteAgreement

def commonReductArtifact (agreement : ExecutableCanonicalAgreement) : SharedArtifact :=
  ⟨quoteClosedTm agreement.commonReduct⟩

theorem commonReductQuoteAgreement
    (agreement : ExecutableCanonicalAgreement) :
    agreement.commonReductArtifact.pattern =
      quoteClosedTm agreement.commonReduct := rfl

end ExecutableCanonicalAgreement

noncomputable def PureCheckingBoundary.compareExecutableToCanonical
    (svc : PureCheckingBoundary)
    (fuel : Nat)
    (term : PureTm 0) :
    ExecutableCanonicalAgreement :=
  let canonical := svc.canonicalizeClosed term
  let executableResult := evalPureFuel fuel term
  let inputToExecutable := evalPureFuel_redStar fuel term
  let joined := redStar_confluence inputToExecutable canonical.reductionToCanonicalDevelopment
  let commonReduct := Classical.choose joined
  let executableToCommonReduct := (Classical.choose_spec joined).1
  let canonicalToCommonReduct := (Classical.choose_spec joined).2
  { input := term
    fuel := fuel
    executableResult := executableResult
    canonical := canonical
    canonicalInput_eq := svc.canonicalizeClosed_term term
    inputToExecutable := inputToExecutable
    commonReduct := commonReduct
    executableToCommonReduct := executableToCommonReduct
    canonicalToCommonReduct := canonicalToCommonReduct }

theorem PureCheckingBoundary.compareExecutableToCanonical_input
    (svc : PureCheckingBoundary)
    (fuel : Nat)
    (term : PureTm 0) :
    (svc.compareExecutableToCanonical fuel term).input = term := by
  simp [PureCheckingBoundary.compareExecutableToCanonical]

theorem PureCheckingBoundary.compareExecutableToCanonical_executableResult
    (svc : PureCheckingBoundary)
    (fuel : Nat)
    (term : PureTm 0) :
    (svc.compareExecutableToCanonical fuel term).executableResult =
      evalPureFuel fuel term := by
  simp [PureCheckingBoundary.compareExecutableToCanonical]

theorem PureCheckingBoundary.compareExecutableToCanonical_canonicalDevelopment
    (svc : PureCheckingBoundary)
    (fuel : Nat)
    (term : PureTm 0) :
    (svc.compareExecutableToCanonical fuel term).canonical.canonicalDevelopment =
      cdev term := by
  simp [PureCheckingBoundary.compareExecutableToCanonical,
    PureCheckingBoundary.canonicalizeClosed, canonicalizeClosedPureTerm]

structure BoundedCommonReductWitness (left right : PureTm 0) where
  leftSteps : Nat
  rightSteps : Nat
  commonReduct : PureTm 0
  leftReduction : RedStar left commonReduct
  rightReduction : RedStar right commonReduct

structure BoundedExecutableCanonicalAgreement where
  input : PureTm 0
  fuel : Nat
  executableResult : PureTm 0
  canonical : CanonicalClosedPureTerm
  canonicalInput_eq : canonical.input = input
  inputToExecutable : RedStar input executableResult
  commonReduct : PureTm 0
  executableJoinSteps : Nat
  canonicalJoinSteps : Nat
  executableToCommonReduct : RedStar executableResult commonReduct
  canonicalToCommonReduct : RedStar canonical.canonicalDevelopment commonReduct

namespace BoundedExecutableCanonicalAgreement

def executableArtifact (agreement : BoundedExecutableCanonicalAgreement) : SharedArtifact :=
  ⟨quoteClosedTm agreement.executableResult⟩

def canonicalArtifact (agreement : BoundedExecutableCanonicalAgreement) : SharedArtifact :=
  agreement.canonical.artifact

def commonReductArtifact (agreement : BoundedExecutableCanonicalAgreement) : SharedArtifact :=
  ⟨quoteClosedTm agreement.commonReduct⟩

theorem executableQuoteAgreement
    (agreement : BoundedExecutableCanonicalAgreement) :
    agreement.executableArtifact.pattern =
      quoteClosedTm agreement.executableResult := rfl

theorem canonicalQuoteAgreement
    (agreement : BoundedExecutableCanonicalAgreement) :
    agreement.canonicalArtifact.pattern =
      quoteClosedTm agreement.canonical.canonicalDevelopment :=
  agreement.canonical.quoteAgreement

theorem commonReductQuoteAgreement
    (agreement : BoundedExecutableCanonicalAgreement) :
    agreement.commonReductArtifact.pattern =
      quoteClosedTm agreement.commonReduct := rfl

def executableWitness
    (agreement : BoundedExecutableCanonicalAgreement) :
    ConversionWitness agreement.executableResult agreement.canonical.canonicalDevelopment :=
  { commonReduct := agreement.commonReduct
    leftReduces := agreement.executableToCommonReduct
    rightReduces := agreement.canonicalToCommonReduct }

theorem executableConvCanonical
    (agreement : BoundedExecutableCanonicalAgreement) :
    Conv agreement.executableResult agreement.canonical.canonicalDevelopment :=
  agreement.executableWitness.toConv

theorem inputToCanonical
    (agreement : BoundedExecutableCanonicalAgreement) :
    RedStar agreement.input agreement.canonical.canonicalDevelopment := by
  simpa [agreement.canonicalInput_eq] using agreement.canonical.reductionToCanonicalDevelopment

theorem inputToCommonReduct
    (agreement : BoundedExecutableCanonicalAgreement) :
    RedStar agreement.input agreement.commonReduct :=
  RedStar.trans agreement.inputToExecutable agreement.executableToCommonReduct

end BoundedExecutableCanonicalAgreement

def mkBoundedCommonReductWitness?
    (left right : PureTm 0)
    (leftSteps rightSteps : Nat) :
    Option (BoundedCommonReductWitness left right) :=
  let leftResult := evalPureFuel leftSteps left
  let rightResult := evalPureFuel rightSteps right
  if h : leftResult = rightResult then
    some
      { leftSteps := leftSteps
        rightSteps := rightSteps
        commonReduct := leftResult
        leftReduction := evalPureFuel_redStar leftSteps left
        rightReduction := by
          simpa [h] using evalPureFuel_redStar rightSteps right }
  else
    none

private def searchCommonReductRightFuel
    (left right : PureTm 0)
    (leftSteps : Nat) :
    Nat -> Option (BoundedCommonReductWitness left right)
  | 0 => mkBoundedCommonReductWitness? left right leftSteps 0
  | rightSteps + 1 =>
      match searchCommonReductRightFuel left right leftSteps rightSteps with
      | some witness => some witness
      | none => mkBoundedCommonReductWitness? left right leftSteps (rightSteps + 1)

def findCommonReductWithinFuel?
    (budget : Nat)
    (left right : PureTm 0) :
    Option (BoundedCommonReductWitness left right) :=
  let rec go : Nat -> Option (BoundedCommonReductWitness left right)
    | 0 => searchCommonReductRightFuel left right 0 budget
    | leftSteps + 1 =>
        match go leftSteps with
        | some witness => some witness
        | none => searchCommonReductRightFuel left right (leftSteps + 1) budget
  go budget

def PureCheckingBoundary.compareExecutableToCanonicalWithinFuel?
    (svc : PureCheckingBoundary)
    (fuel : Nat)
    (term : PureTm 0) :
    Option BoundedExecutableCanonicalAgreement :=
  let canonical := svc.canonicalizeClosed term
  let executableResult := evalPureFuel fuel term
  let inputToExecutable := evalPureFuel_redStar fuel term
  match findCommonReductWithinFuel? fuel executableResult canonical.canonicalDevelopment with
  | none => none
  | some witness =>
      some
        { input := term
          fuel := fuel
          executableResult := executableResult
          canonical := canonical
          canonicalInput_eq := svc.canonicalizeClosed_term term
          inputToExecutable := inputToExecutable
          commonReduct := witness.commonReduct
          executableJoinSteps := witness.leftSteps
          canonicalJoinSteps := witness.rightSteps
          executableToCommonReduct := witness.leftReduction
          canonicalToCommonReduct := witness.rightReduction }

private def formatArtifactPattern (artifact : SharedArtifact) : String :=
  s!"{repr artifact.pattern}"

private def formatAgreementSummary : List String :=
  [ "proof: executable-to-common-reduct=ok"
  , "proof: canonical-to-common-reduct=ok"
  , "proof: executable-canonical-agreement=ok"
  ]

def runPureAgreeFile
    (path : System.FilePath)
    (fuel : Nat := Mettapedia.Languages.MeTTa.PurePrototypeEval.defaultFuel) :
    IO UInt32 := do
  let input <- IO.FS.readFile path
  match Mettapedia.Languages.MeTTa.PurePrototypeEval.parseClosedPrettyPureInput input with
  | .error err =>
      IO.eprintln s!"pure-agree parse error in {path}: {err}"
      pure 1
  | .ok parsed =>
      let term := parsed.term.toPureTm
      let canonical := pureCheckingBoundary.canonicalizeClosed term
      IO.println s!"input: {Mettapedia.Languages.MeTTa.PurePrototypeEval.prettyClosed parsed.term.toPureTm}"
      match parsed.expectedType? with
      | some expectedType =>
          IO.println s!"annotation: {Mettapedia.Languages.MeTTa.PurePrototypeEval.prettyClosed expectedType.toPureTm}"
      | none =>
          pure ()
      match pureCheckingBoundary.compareExecutableToCanonicalWithinFuel? fuel term with
      | none =>
          IO.eprintln s!"pure-agree witness search exhausted fuel {fuel} without finding a common reduct"
          pure 1
      | some agreement =>
          IO.println s!"executable-result: {Mettapedia.Languages.MeTTa.PurePrototypeEval.prettyClosed agreement.executableResult}"
          IO.println s!"canonical-development: {Mettapedia.Languages.MeTTa.PurePrototypeEval.prettyClosed canonical.canonicalDevelopment}"
          IO.println s!"common-reduct: {Mettapedia.Languages.MeTTa.PurePrototypeEval.prettyClosed agreement.commonReduct}"
          IO.println s!"executable-join-steps: {agreement.executableJoinSteps}"
          IO.println s!"canonical-join-steps: {agreement.canonicalJoinSteps}"
          IO.println s!"executable-artifact: {formatArtifactPattern agreement.executableArtifact}"
          IO.println s!"canonical-artifact: {formatArtifactPattern agreement.canonicalArtifact}"
          IO.println s!"common-reduct-artifact: {formatArtifactPattern agreement.commonReductArtifact}"
          for line in formatAgreementSummary do
            IO.println line
          pure 0

end Mettapedia.Languages.MeTTa.ElaboratedCore
