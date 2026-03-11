import Mettapedia.Languages.MeTTa.PureBidirectionalChecking
import Mettapedia.Languages.MeTTa.PureNormalizationService
import Mettapedia.Languages.MeTTa.PurePrototypeEval
import Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction

namespace Mettapedia.Languages.MeTTa.PureCheckedEval

open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.PureKernel
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction
open Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory

theorem subjectReductionRedStar {Γ : Ctx n} {t u A : PureTm n}
    (ht : HasType Γ t A) (h : RedStar t u) :
    HasType Γ u A := by
  induction h generalizing A with
  | refl =>
      simpa using ht
  | tail htu huv ih =>
      exact subject_reduction (ih ht) huv

def checkParsedPureInput
    (input : Mettapedia.Languages.MeTTa.PurePrototypeEval.ParsedPureInput) :
    Except String PureCheckSuccess :=
  checkSurfacePureWithOptionalType input.term input.expectedType?

structure CheckedPureEvaluation where
  checkedInput : PureCheckSuccess
  canonical : CanonicalClosedPureTerm
  input_eq : canonical.input = checkedInput.term.toPureTm
  outputTyping : HasType .nil canonical.canonicalDevelopment checkedInput.claimedType

def CheckedPureEvaluation.inputCertificate
    (result : CheckedPureEvaluation) : CheckedPureCertificate :=
  result.checkedInput.certificate

def CheckedPureEvaluation.outputCertificate
    (result : CheckedPureEvaluation) : CheckedPureCertificate :=
  pureCheckingBoundary.checkClosedTerm
    result.canonical.canonicalDevelopment
    result.checkedInput.claimedType
    result.outputTyping

theorem CheckedPureEvaluation.outputQuoteAgreement
    (result : CheckedPureEvaluation) :
    result.outputCertificate.artifact.pattern =
      quoteClosedTm result.outputCertificate.term := by
  exact result.outputCertificate.quoteAgreement

theorem CheckedPureEvaluation.profileBridge
    (result : CheckedPureEvaluation) :
    PureProfileTheoryStepStar
      (quoteClosedTm result.checkedInput.term.toPureTm)
      (quoteClosedTm result.canonical.canonicalDevelopment) := by
  have hred : RedStar result.checkedInput.term.toPureTm result.canonical.canonicalDevelopment := by
    simpa [result.input_eq] using result.canonical.reductionToCanonicalDevelopment
  exact pureTheoryStepStar_sound_pureProfileTheoryStepStar_quoteClosed hred

def evalCheckedSurfacePure
    (checked : PureCheckSuccess) :
    CheckedPureEvaluation :=
  let canonical := pureCheckingBoundary.canonicalizeClosed checked.term.toPureTm
  let outputTyping := subjectReductionRedStar checked.typing canonical.reductionToCanonicalDevelopment
  { checkedInput := checked
    canonical := canonical
    input_eq := pureCheckingBoundary.canonicalizeClosed_term checked.term.toPureTm
    outputTyping := outputTyping }

def Mettapedia.Languages.MeTTa.ElaboratedCore.PureCheckingBoundary.checkAndEvalSurface
    (svc : PureCheckingBoundary)
    (surface : SurfacePureTm 0)
    (claimedType? : Option (SurfacePureTm 0)) :
    Except String CheckedPureEvaluation := do
  let checked <- checkSurfacePureWithOptionalType surface claimedType?
  let canonical := svc.canonicalizeClosed checked.term.toPureTm
  let outputTyping := subjectReductionRedStar checked.typing canonical.reductionToCanonicalDevelopment
  pure
    { checkedInput := checked
      canonical := canonical
      input_eq := svc.canonicalizeClosed_term checked.term.toPureTm
      outputTyping := outputTyping }

def checkAndEvalParsedPureInput
    (input : Mettapedia.Languages.MeTTa.PurePrototypeEval.ParsedPureInput) :
    Except String CheckedPureEvaluation := do
  Mettapedia.Languages.MeTTa.ElaboratedCore.PureCheckingBoundary.checkAndEvalSurface
    pureCheckingBoundary
    input.term
    input.expectedType?

private def formatArtifactPattern (artifact : SharedArtifact) : String :=
  s!"{repr artifact.pattern}"

private def formatCheckSummary : List String :=
  [ "proof: closed-typing=ok"
  , "proof: quoted-artifact-agreement=ok"
  ]

private def formatCheckedEvalSummary : List String :=
  [ "proof: closed-typing=ok"
  , "proof: eval-preserves-type=ok"
  , "proof: canonical-quoted-artifact-agreement=ok"
  , "proof: profile-bridge=ok"
  ]

def runPureCheckFile (path : System.FilePath) : IO UInt32 := do
  let input <- IO.FS.readFile path
  match Mettapedia.Languages.MeTTa.PurePrototypeEval.parseClosedPrettyPureInput input with
  | .error err =>
      IO.eprintln s!"pure-check parse error in {path}: {err}"
      pure 1
  | .ok parsed =>
      match checkParsedPureInput parsed with
      | .error err =>
          IO.eprintln s!"pure-check type error in {path}: {err}"
          pure 1
      | .ok result =>
          let cert := result.certificate
          IO.println s!"input: {Mettapedia.Languages.MeTTa.PurePrototypeEval.prettyClosed result.term.toPureTm}"
          IO.println s!"type: {Mettapedia.Languages.MeTTa.PurePrototypeEval.prettyClosed result.claimedType}"
          IO.println s!"artifact: {formatArtifactPattern cert.artifact}"
          for line in formatCheckSummary do
            IO.println line
          pure 0

def runPureCheckEvalFile (path : System.FilePath) : IO UInt32 := do
  let input <- IO.FS.readFile path
  match Mettapedia.Languages.MeTTa.PurePrototypeEval.parseClosedPrettyPureInput input with
  | .error err =>
      IO.eprintln s!"pure-check-eval parse error in {path}: {err}"
      pure 1
  | .ok parsed =>
      match checkAndEvalParsedPureInput parsed with
      | .error err =>
          IO.eprintln s!"pure-check-eval type error in {path}: {err}"
          pure 1
      | .ok result =>
          IO.println s!"input: {Mettapedia.Languages.MeTTa.PurePrototypeEval.prettyClosed result.checkedInput.term.toPureTm}"
          IO.println s!"type: {Mettapedia.Languages.MeTTa.PurePrototypeEval.prettyClosed result.checkedInput.claimedType}"
          IO.println s!"canonical-development: {Mettapedia.Languages.MeTTa.PurePrototypeEval.prettyClosed result.canonical.canonicalDevelopment}"
          IO.println s!"input-artifact: {formatArtifactPattern result.inputCertificate.artifact}"
          IO.println s!"canonical-artifact: {formatArtifactPattern result.outputCertificate.artifact}"
          for line in formatCheckedEvalSummary do
            IO.println line
          pure 0

end Mettapedia.Languages.MeTTa.PureCheckedEval
