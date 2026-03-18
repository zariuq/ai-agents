/-
# Main README GF Pilot

This file demonstrates the intended architecture:

- Canonical source = language-independent semantic tree (`RepoClaim`)
- English output = generated through GF English morphology/syntax
  (`linPredVP`, `complV2`, `linUseCl`, agreement/tense handling)

This is intentionally a small pilot over sentences from `~/claude/README.md`.
The wording is semantically close, not byte-identical.
-/

import Mettapedia.Languages.GF.HandCrafted.English.Examples

namespace Mettapedia.Languages.GF.Examples.MainReadmeGFPilot

open Mettapedia.Languages.GF.HandCrafted.English
open Mettapedia.Languages.GF.HandCrafted.English.Nouns
open Mettapedia.Languages.GF.HandCrafted.English.Verbs
open Mettapedia.Languages.GF.HandCrafted.English.Syntax

/-! ## Domain-Semantic Tree (language-independent) -/

inductive RepoClaim where
  | workspaceIncludesTooling
  | mettapediaHostsInferenceProofs
  | mmLean4ProvesVerifier
  | pverifyExercisesInteroperability
  | tptpConvertersSupportInteroperability
  | statusChecksUseRgSorry
  deriving Repr

/-! ## Lexical Helpers -/

def literalNP (txt : String) (agr : Agr := .AgP3Sg .Neutr) : EnglishNP :=
  { s := fun
      | .NCase .Nom => txt
      | .NCase .Gen => txt ++ "'s"
      | .NPAcc => txt
      | .NPNomPoss => txt ++ "'s"
    agr := agr
  }

private def mkPresClause (subj : EnglishNP) (vp : EnglishVP) : String :=
  linUseCl .Pres .Simul .CPos (linPredVP subj vp)

private def regV2 (base : String) : EnglishV2 :=
  mkV2 (regV base)

/-! ## English Linearization from Semantic Tree -/

def renderEnglish : RepoClaim → String
  | .workspaceIncludesTooling =>
      mkPresClause
        (literalNP "this workspace")
        (complV2 (regV2 "include")
          (literalNP "Lean, Metamath, and ATP tooling"))
  | .mettapediaHostsInferenceProofs =>
      mkPresClause
        (literalNP "Mettapedia")
        (complV2 (regV2 "host")
          (literalNP "foundations of inference proofs"))
  | .mmLean4ProvesVerifier =>
      mkPresClause
        (literalNP "mm-lean4")
        (complV2 (regV2 "prove")
          (literalNP "a Metamath verifier in Lean"))
  | .pverifyExercisesInteroperability =>
      mkPresClause
        (literalNP "pverify")
        (complV2 (regV2 "exercise")
          (literalNP "cross-language verification interoperability"))
  | .tptpConvertersSupportInteroperability =>
      mkPresClause
        (literalNP "tools/tptp-metta converters" .AgP3Pl)
        (complV2 (regV2 "support")
          (literalNP "TPTP and MeTTa interoperability"))
  | .statusChecksUseRgSorry =>
      mkPresClause
        (literalNP "status checks" .AgP3Pl)
        (complV2 (regV2 "use")
          (literalNP "`rg \"sorry\"` in relevant code folders"))

/-! ## Sample README Paragraph (generated) -/

def mainReadmePilotParagraph : List String :=
  [ .workspaceIncludesTooling
  , .mettapediaHostsInferenceProofs
  , .mmLean4ProvesVerifier
  , .pverifyExercisesInteroperability
  , .tptpConvertersSupportInteroperability
  , .statusChecksUseRgSorry
  ] |>.map renderEnglish

#eval mainReadmePilotParagraph

/-! ## Checks: morphology and agreement are actually exercised -/

theorem workspace_sentence :
    renderEnglish .workspaceIncludesTooling =
      "this workspace includes Lean, Metamath, and ATP tooling" := by
  decide

theorem mettapedia_sentence :
    renderEnglish .mettapediaHostsInferenceProofs =
      "Mettapedia hosts foundations of inference proofs" := by
  decide

theorem plural_agreement_sentence :
    renderEnglish .tptpConvertersSupportInteroperability =
      "tools/tptp-metta converters support TPTP and MeTTa interoperability" := by
  decide

theorem status_sentence :
    renderEnglish .statusChecksUseRgSorry =
      "status checks use `rg \"sorry\"` in relevant code folders" := by
  decide

end Mettapedia.Languages.GF.Examples.MainReadmeGFPilot
