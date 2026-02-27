import Mettapedia.OSLF.MeTTaIL.Export
import Mettapedia.OSLF.Framework.PyashCoreInstance

open Mettapedia.OSLF.MeTTaIL.Export
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.PyashCoreInstance

/-- Constructor-grounded exported PyashCore cases (single source of truth = Lean `Pattern` states). -/
def pyashCoreCaseBundlePatterns : List (String × Pattern × Pattern) :=
  [ ("plus_do", pyashStateDeriveSignature, pyashStateDoneOk)
  , ("read_do", pyashStateReadDerive, pyashStateReadDoneOk)
  , ("ret_read", pyashStateRetReadDerive, pyashStateRetReadDoneOk)
  , ("mind_do", pyashStateMindDerive, pyashStateMindDoneOk)
  , ("ceremony_do", pyashStateCeremonyDerive, pyashStateCeremonyDoneOk)
  , ("chip_do", pyashStateChipDerive, pyashStateChipDoneOk)
  , ("chip_do_series", pyashStateChipSeriesDerive, pyashStateChipSeriesDoneOk)
  , ("chip_do_bounded", pyashStateChipBoundedDerive, pyashStateChipBoundedDoneOk)
  , ("hear_do", pyashStateHearDerive, pyashStateHearDoneOk)
  , ("hear_do_mic", pyashStateHearMicRecordDerive, pyashStateHearMicRecordDoneOk)
  , ("hear_do_srt", pyashStateHearFileSrtDerive, pyashStateHearFileSrtDoneOk)
  , ("configure_do", pyashStateConfigureDerive, pyashStateConfigureDoneOk)
  , ("configure_def", pyashStateConfigureDefDerive, pyashStateConfigureDefDoneOk)
  , ("world_do", pyashStateWorldDerive, pyashStateWorldDoneOk)
  , ("pipeline_do", pyashStatePipelineDerive, pyashStatePipelineDoneOk)
  , ("compile_do", pyashStateCompileDerive, pyashStateCompileDoneOk)
  , ("import_do", pyashStateImportDerive, pyashStateImportDoneOk)
  , ("download_do", pyashStateDownloadDerive, pyashStateDownloadDoneOk)
  , ("translation_do", pyashStateTranslationDerive, pyashStateTranslationDoneOk)
  , ("dispatch_error_then", pyashStateDispatchErrorInstr, pyashStateDoneDispatchErr)
  , ("malformed_signature_shape", pyashStateMalformedSignatureShape, pyashStateDoneMalformedSignatureErr)
  , ("signature_mismatch", pyashStateMismatch, pyashStateDoneSignatureErr)
  ]

/-- Sparse constructor mix used for generated edge-case bundles. -/
def pyashSparseEdgeRoleTypes : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Vyah" [], .apply "TBool" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "FromIndex" [], .apply "TDate" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "AtIndex" [], .apply "TVec" []],
        .apply "RTCons" [
          .apply "RoleType" [.apply "ToIndex" [], .apply "TFilename" []],
          .apply "RTNil" []
        ]
      ]
    ]
  ]

/-- Alternate sparse constructor mix emphasizing `by`/`during` text and numeric shapes. -/
def pyashSparseEdgeRoleTypesAlt : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "By" [], .apply "TText" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "During" [], .apply "TNum" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "ToText" [], .apply "TText" []],
        .apply "RTNil" []
      ]
    ]
  ]

/-- Alternate sparse constructor mix emphasizing bounded/state transition shapes. -/
def pyashSparseEdgeRoleTypesBounded : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "AtLeast" [], .apply "TNum" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "AtMost" [], .apply "TNum" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "FromState" [], .apply "TWo" []],
        .apply "RTCons" [
          .apply "RoleType" [.apply "Become" [], .apply "TWo" []],
          .apply "RTNil" []
        ]
      ]
    ]
  ]

/-- Generated edge-case bundle for sparse constructors and explicit negative paths. -/
def pyashCoreEdgeCaseBundlePatterns : List (String × Pattern × Pattern) :=
  let mkDefaultDerive (rts : Pattern) : Pattern :=
    .apply "State" [
      .apply "DeriveSignature" [],
      .apply "SentenceCore" [.apply "MYa" [], .apply "VDefault" [], rts],
      .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
      .apply "Ok" []
    ]
  let mkDefaultDone (rts : Pattern) : Pattern :=
    .apply "State" [
      .apply "Done" [],
      .apply "SentenceCore" [.apply "MYa" [], .apply "VDefault" [], rts],
      .apply "Signature" [.apply "VDefault" [], rts],
      .apply "Ok" []
    ]
  let mkDefaultMismatch (rts : Pattern) : Pattern :=
    .apply "State" [
      .apply "Dispatch" [],
      .apply "SentenceCore" [.apply "MYa" [], .apply "VDefault" [], rts],
      .apply "SigMismatch" [
        .apply "Signature" [.apply "VDefault" [], rts],
        .apply "Signature" [.apply "VRead" [], .apply "RTNil" []]
      ],
      .apply "Ok" []
    ]
  let mkDefaultDispatchErrInstr (rts : Pattern) : Pattern :=
    .apply "State" [
      .apply "DispatchError" [],
      .apply "SentenceCore" [.apply "MRet" [], .apply "VDefault" [], rts],
      .apply "Signature" [.apply "VDefault" [], rts],
      .apply "Ok" []
    ]
  let mkDefaultSigErrDone (rts : Pattern) : Pattern :=
    .apply "State" [
      .apply "Done" [],
      .apply "SentenceCore" [.apply "MYa" [], .apply "VError" [], rts],
      .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
      .apply "ErrSignature" []
    ]
  let mkDefaultDispatchErrDone (rts : Pattern) : Pattern :=
    .apply "State" [
      .apply "Done" [],
      .apply "SentenceCore" [.apply "MYa" [], .apply "VError" [], rts],
      .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
      .apply "ErrDispatch" []
    ]
  [ ("edge_ret_read_terminal", pyashStateRetReadDerive, pyashStateRetReadDoneOk)
  , ("edge_sparse_default_positive", mkDefaultDerive pyashSparseEdgeRoleTypes, mkDefaultDone pyashSparseEdgeRoleTypes)
  , ("edge_sparse_signature_mismatch_negative", mkDefaultMismatch pyashSparseEdgeRoleTypes, mkDefaultSigErrDone pyashSparseEdgeRoleTypes)
  , ("edge_sparse_dispatch_error_negative", mkDefaultDispatchErrInstr pyashSparseEdgeRoleTypes, mkDefaultDispatchErrDone pyashSparseEdgeRoleTypes)
  , ("edge_sparse_alt_default_positive", mkDefaultDerive pyashSparseEdgeRoleTypesAlt, mkDefaultDone pyashSparseEdgeRoleTypesAlt)
  , ("edge_sparse_alt_signature_mismatch_negative", mkDefaultMismatch pyashSparseEdgeRoleTypesAlt, mkDefaultSigErrDone pyashSparseEdgeRoleTypesAlt)
  , ("edge_sparse_alt_dispatch_error_negative", mkDefaultDispatchErrInstr pyashSparseEdgeRoleTypesAlt, mkDefaultDispatchErrDone pyashSparseEdgeRoleTypesAlt)
  , ("edge_sparse_bounded_default_positive", mkDefaultDerive pyashSparseEdgeRoleTypesBounded, mkDefaultDone pyashSparseEdgeRoleTypesBounded)
  , ("edge_sparse_bounded_signature_mismatch_negative", mkDefaultMismatch pyashSparseEdgeRoleTypesBounded, mkDefaultSigErrDone pyashSparseEdgeRoleTypesBounded)
  , ("edge_sparse_bounded_dispatch_error_negative", mkDefaultDispatchErrInstr pyashSparseEdgeRoleTypesBounded, mkDefaultDispatchErrDone pyashSparseEdgeRoleTypesBounded)
  , ("edge_malformed_signature_shape_negative", pyashStateMalformedSignatureShape, pyashStateDoneMalformedSignatureErr)
  ]

/-- Exported case bundle after rendering state patterns into Rust runtime `C_...` syntax. -/
def pyashCoreCaseBundle : List (String × String × String) :=
  pyashCoreCaseBundlePatterns.map (fun caseTriple =>
    let label := caseTriple.1
    let input := caseTriple.2.1
    let expected := caseTriple.2.2
    (label, renderPyashCtorPattern input, renderPyashCtorPattern expected))

/-- Exported edge-case bundle after rendering patterns into runtime `C_...` syntax. -/
def pyashCoreEdgeCaseBundle : List (String × String × String) :=
  pyashCoreEdgeCaseBundlePatterns.map (fun caseTriple =>
    let label := caseTriple.1
    let input := caseTriple.2.1
    let expected := caseTriple.2.2
    (label, renderPyashCtorPattern input, renderPyashCtorPattern expected))

/-- Representative input term for the Pyash core Lean->Rust roundtrip check. -/
def pyashCoreInput : String :=
  renderPyashCtorPattern pyashStateDeriveSignature

/-- Expected normal-form term after running Pyash core reductions. -/
def pyashCoreExpected : String :=
  renderPyashCtorPattern pyashStateDoneOk

def renderPyashCoreCaseBundle : String :=
  String.intercalate "\n" <|
    pyashCoreCaseBundle.map (fun caseTriple =>
      let label := caseTriple.1
      let input := caseTriple.2.1
      let expected := caseTriple.2.2
      label ++ "|||" ++ input ++ "|||" ++ expected)

def renderPyashCoreEdgeCaseBundle : String :=
  String.intercalate "\n" <|
    pyashCoreEdgeCaseBundle.map (fun caseTriple =>
      let label := caseTriple.1
      let input := caseTriple.2.1
      let expected := caseTriple.2.2
      label ++ "|||" ++ input ++ "|||" ++ expected)

private def usage : String :=
  String.intercalate "\n"
    [ "Usage:"
    , "  lake env lean --run Mettapedia/OSLF/Tools/ExportPyashCoreToMettail.lean"
    , "  lake env lean --run Mettapedia/OSLF/Tools/ExportPyashCoreToMettail.lean <lang_out> <input_out> <expected_out>"
    , "  lake env lean --run Mettapedia/OSLF/Tools/ExportPyashCoreToMettail.lean <lang_out> <input_out> <expected_out> <cases_out>"
    , "  lake env lean --run Mettapedia/OSLF/Tools/ExportPyashCoreToMettail.lean <lang_out> <input_out> <expected_out> <cases_out> <edge_cases_out>"
    ]

/--
Emit Lean-exported artifacts for the isolated Pyash core pathway.

- No args: print all artifacts to stdout.
- 3 args: write language macro text, input term, expected output term to files.
- 4 args: same as 3 args, plus write case bundle file.
- 5 args: same as 4 args, plus write generated edge-case bundle file.
-/
def main (args : List String) : IO UInt32 := do
  let rendered := renderLanguage pyashCore
  match args with
  | [] =>
      IO.println "=== LANGUAGE ==="
      IO.println rendered
      IO.println "=== INPUT ==="
      IO.println pyashCoreInput
      IO.println "=== EXPECTED ==="
      IO.println pyashCoreExpected
      IO.println "=== CASES ==="
      IO.println renderPyashCoreCaseBundle
      IO.println "=== EDGE_CASES ==="
      IO.println renderPyashCoreEdgeCaseBundle
      pure 0
  | [langOut, inputOut, expectedOut] =>
      IO.FS.writeFile langOut (rendered ++ "\n")
      IO.FS.writeFile inputOut (pyashCoreInput ++ "\n")
      IO.FS.writeFile expectedOut (pyashCoreExpected ++ "\n")
      pure 0
  | [langOut, inputOut, expectedOut, casesOut] =>
      IO.FS.writeFile langOut (rendered ++ "\n")
      IO.FS.writeFile inputOut (pyashCoreInput ++ "\n")
      IO.FS.writeFile expectedOut (pyashCoreExpected ++ "\n")
      IO.FS.writeFile casesOut (renderPyashCoreCaseBundle ++ "\n")
      pure 0
  | [langOut, inputOut, expectedOut, casesOut, edgeCasesOut] =>
      IO.FS.writeFile langOut (rendered ++ "\n")
      IO.FS.writeFile inputOut (pyashCoreInput ++ "\n")
      IO.FS.writeFile expectedOut (pyashCoreExpected ++ "\n")
      IO.FS.writeFile casesOut (renderPyashCoreCaseBundle ++ "\n")
      IO.FS.writeFile edgeCasesOut (renderPyashCoreEdgeCaseBundle ++ "\n")
      pure 0
  | _ =>
      IO.eprintln usage
      pure 1
