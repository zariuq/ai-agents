import Mettapedia.Languages.MeTTa.PureCheckedEval
import Mettapedia.Languages.MeTTa.PureSemanticWaist

/-!
# Pure Waist Service

Structured service-level views over the current closed Pure semantic waist.

This file keeps the CLI thin by exposing a shared family of result records for:

- closed-term canonical inspection,
- checked closed terms,
- checked evaluation,
- executable/canonical agreement within a finite fuel budget.
-/

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.PureKernel
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PurePrototypeEval
open Mettapedia.Languages.MeTTa.PureCheckedEval

structure PureClosedWaistView where
  surface : SurfacePureTm 0
  canonical : CanonicalClosedPureTerm
  canonicalInput_eq : canonical.input = surface.toPureTm

namespace PureClosedWaistView

def input (view : PureClosedWaistView) : PureTm 0 :=
  view.surface.toPureTm

def inputArtifact (view : PureClosedWaistView) : SharedArtifact :=
  ⟨quoteClosedTm view.input⟩

def canonicalArtifact (view : PureClosedWaistView) : SharedArtifact :=
  view.canonical.artifact

theorem inputArtifact_eq_quote
    (view : PureClosedWaistView) :
    view.inputArtifact.pattern = quoteClosedTm view.input := rfl

theorem canonicalArtifact_eq_quote
    (view : PureClosedWaistView) :
    view.canonicalArtifact.pattern = quoteClosedTm view.canonical.canonicalDevelopment :=
  view.canonical.quoteAgreement

end PureClosedWaistView

def PureCheckingBoundary.inspectClosedSurface
    (svc : PureCheckingBoundary)
    (surface : SurfacePureTm 0) :
    PureClosedWaistView :=
  let canonical := svc.canonicalizeClosed surface.toPureTm
  { surface := surface
    canonical := canonical
    canonicalInput_eq := svc.canonicalizeClosed_term surface.toPureTm }

structure PureClosedCheckView extends PureClosedWaistView where
  check : PureCheckSuccess

namespace PureClosedCheckView

def claimedType (view : PureClosedCheckView) : PureTm 0 :=
  view.check.claimedType

def certificate (view : PureClosedCheckView) : CheckedPureCertificate :=
  view.check.certificate

theorem certificateQuoteAgreement
    (view : PureClosedCheckView) :
    view.certificate.artifact.pattern = quoteClosedTm view.certificate.term :=
  view.check.quoteAgreement

end PureClosedCheckView

def PureCheckingBoundary.inspectCheckedSurface
    (svc : PureCheckingBoundary)
    (surface : SurfacePureTm 0)
    (claimedType? : Option (SurfacePureTm 0)) :
    Except String PureClosedCheckView := do
  let check <- checkSurfacePureWithOptionalType surface claimedType?
  pure
    { toPureClosedWaistView := svc.inspectClosedSurface surface
      check := check }

structure PureClosedCheckedEvalView extends PureClosedCheckView where
  evaluation : CheckedPureEvaluation

namespace PureClosedCheckedEvalView

def outputCertificate (view : PureClosedCheckedEvalView) : CheckedPureCertificate :=
  view.evaluation.outputCertificate

theorem outputCertificateQuoteAgreement
    (view : PureClosedCheckedEvalView) :
    view.outputCertificate.artifact.pattern = quoteClosedTm view.outputCertificate.term :=
  view.evaluation.outputQuoteAgreement

end PureClosedCheckedEvalView

def PureCheckingBoundary.inspectCheckedEvalSurface
    (svc : PureCheckingBoundary)
    (surface : SurfacePureTm 0)
    (claimedType? : Option (SurfacePureTm 0)) :
    Except String PureClosedCheckedEvalView := do
  let checkView <- svc.inspectCheckedSurface surface claimedType?
  let evaluation := evalCheckedSurfacePure checkView.check
  pure
    { toPureClosedCheckView := checkView
      evaluation := evaluation }

structure PureClosedAgreementView extends PureClosedWaistView where
  fuel : Nat
  agreement : BoundedExecutableCanonicalAgreement

namespace PureClosedAgreementView

def executableArtifact (view : PureClosedAgreementView) : SharedArtifact :=
  view.agreement.executableArtifact

def commonReductArtifact (view : PureClosedAgreementView) : SharedArtifact :=
  view.agreement.commonReductArtifact

end PureClosedAgreementView

def PureCheckingBoundary.inspectAgreementSurfaceWithinFuel?
    (svc : PureCheckingBoundary)
    (fuel : Nat)
    (surface : SurfacePureTm 0) :
    Option PureClosedAgreementView :=
  match svc.compareExecutableToCanonicalWithinFuel? fuel surface.toPureTm with
  | none => none
  | some agreement =>
      some
        { toPureClosedWaistView := svc.inspectClosedSurface surface
          fuel := fuel
          agreement := agreement }

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

private def formatAgreementSummary : List String :=
  [ "proof: executable-to-common-reduct=ok"
  , "proof: canonical-to-common-reduct=ok"
  , "proof: executable-canonical-agreement=ok"
  ]

def runPureCheckFile (path : System.FilePath) : IO UInt32 := do
  let input <- IO.FS.readFile path
  match parseClosedPrettyPureInput input with
  | .error err =>
      IO.eprintln s!"pure-check parse error in {path}: {err}"
      pure 1
  | .ok parsed =>
      match pureCheckingBoundary.inspectCheckedSurface parsed.term parsed.expectedType? with
      | .error err =>
          IO.eprintln s!"pure-check type error in {path}: {err}"
          pure 1
      | .ok view =>
          IO.println s!"input: {prettyClosed view.input}"
          IO.println s!"type: {prettyClosed view.claimedType}"
          IO.println s!"artifact: {formatArtifactPattern view.certificate.artifact}"
          for line in formatCheckSummary do
            IO.println line
          pure 0

def runPureCheckEvalFile (path : System.FilePath) : IO UInt32 := do
  let input <- IO.FS.readFile path
  match parseClosedPrettyPureInput input with
  | .error err =>
      IO.eprintln s!"pure-check-eval parse error in {path}: {err}"
      pure 1
  | .ok parsed =>
      match pureCheckingBoundary.inspectCheckedEvalSurface parsed.term parsed.expectedType? with
      | .error err =>
          IO.eprintln s!"pure-check-eval type error in {path}: {err}"
          pure 1
      | .ok view =>
          IO.println s!"input: {prettyClosed view.input}"
          IO.println s!"type: {prettyClosed view.claimedType}"
          IO.println s!"canonical-development: {prettyClosed view.canonical.canonicalDevelopment}"
          IO.println s!"input-artifact: {formatArtifactPattern view.certificate.artifact}"
          IO.println s!"canonical-artifact: {formatArtifactPattern view.outputCertificate.artifact}"
          for line in formatCheckedEvalSummary do
            IO.println line
          pure 0

def runPureAgreeServiceFile
    (path : System.FilePath)
    (fuel : Nat := defaultFuel) :
    IO UInt32 := do
  let input <- IO.FS.readFile path
  match parseClosedPrettyPureInput input with
  | .error err =>
      IO.eprintln s!"pure-agree parse error in {path}: {err}"
      pure 1
  | .ok parsed =>
      IO.println s!"input: {prettyClosed parsed.term.toPureTm}"
      match parsed.expectedType? with
      | some expectedType =>
          IO.println s!"annotation: {prettyClosed expectedType.toPureTm}"
      | none =>
          pure ()
      match pureCheckingBoundary.inspectAgreementSurfaceWithinFuel? fuel parsed.term with
      | none =>
          IO.eprintln s!"pure-agree witness search exhausted fuel {fuel} without finding a common reduct"
          pure 1
      | some view =>
          IO.println s!"executable-result: {prettyClosed view.agreement.executableResult}"
          IO.println s!"canonical-development: {prettyClosed view.canonical.canonicalDevelopment}"
          IO.println s!"common-reduct: {prettyClosed view.agreement.commonReduct}"
          IO.println s!"executable-join-steps: {view.agreement.executableJoinSteps}"
          IO.println s!"canonical-join-steps: {view.agreement.canonicalJoinSteps}"
          IO.println s!"executable-artifact: {formatArtifactPattern view.executableArtifact}"
          IO.println s!"canonical-artifact: {formatArtifactPattern view.canonicalArtifact}"
          IO.println s!"common-reduct-artifact: {formatArtifactPattern view.commonReductArtifact}"
          for line in formatAgreementSummary do
            IO.println line
          pure 0

end Mettapedia.Languages.MeTTa.ElaboratedCore
