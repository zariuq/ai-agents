import Mettapedia.Languages.GF.Abstract

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.Abstract

private def gfRglCzechRoot : System.FilePath :=
  "/home/zar/claude/gf-rgl/src/czech"

private def leanCzechRoot : System.FilePath :=
  "/home/zar/claude/lean-projects/mettapedia/Mettapedia/Languages/GF/Czech"

private def actualGFCzechModules : List (String × String) :=
  [ ("core.adjective", "AdjectiveCze.gf")
  , ("core.conjunction", "ConjunctionCze.gf")
  , ("core.noun", "NounCze.gf")
  , ("core.phrase", "PhraseCze.gf")
  , ("core.question", "QuestionCze.gf")
  , ("core.relative", "RelativeCze.gf")
  , ("core.sentence", "SentenceCze.gf")
  , ("core.verb", "VerbCze.gf")
  , ("adverb", "AdverbCze.gf")
  , ("tense", "TenseCze.gf")
  , ("text", "TextCze.gf")
  , ("idiom", "IdiomCze.gf")
  , ("numeral", "NumeralCze.gf")
  , ("structural", "StructuralCze.gf")
  , ("symbol", "SymbolCze.gf")
  ]

private def leanCzechModules : List (String × String) :=
  [ ("resource.morphology", "Morphology.lean")
  , ("resource.declensions", "Declensions.lean")
  , ("resource.adjectives", "Adjectives.lean")
  , ("resource.verbs", "Verbs.lean")
  , ("resource.pronouns", "Pronouns.lean")
  , ("resource.numerals", "Numerals.lean")
  , ("resource.agreement", "Agreement.lean")
  , ("linearization", "Linearization.lean")
  , ("corpus", "RoundTripCorpus.lean")
  , ("tests", "Tests.lean")
  , ("examples", "Examples.lean")
  , ("missing.sentence", "Sentence.lean")
  , ("missing.question", "Question.lean")
  , ("missing.relative", "Relative.lean")
  , ("missing.phrase", "Phrase.lean")
  , ("missing.structural", "Structural.lean")
  , ("missing.text", "Text.lean")
  , ("missing.tense", "Tense.lean")
  , ("missing.idiom", "Idiom.lean")
  , ("missing.adverb", "Adverb.lean")
  , ("missing.symbol", "Symbol.lean")
  ]

private def countExisting (root : System.FilePath) (mods : List (String × String)) :
    IO Nat := do
  let mut acc := 0
  for (_, rel) in mods do
    if ← (root / rel).pathExists then
      acc := acc + 1
  pure acc

  private def emitExistenceTable (tag : String) (root : System.FilePath)
    (mods : List (String × String)) : IO Unit := do
  for (label, rel) in mods do
    let present := if ← (root / rel).pathExists then "true" else "false"
    IO.println s!"{tag}.{label}.exists={present}"

def main : IO Unit := do
  let actualCount ← countExisting gfRglCzechRoot actualGFCzechModules
  let leanCount ← countExisting leanCzechRoot leanCzechModules
  IO.println s!"gf_czech_actual.project_core_family_modules.total={actualGFCzechModules.length - 1}"
  IO.println s!"gf_czech_actual.project_core_plus_symbol_family_modules.total={actualGFCzechModules.length}"
  IO.println s!"gf_czech_actual.family_modules.present={actualCount}/{actualGFCzechModules.length}"
  IO.println s!"gf_czech_lean.module_markers.present={leanCount}/{leanCzechModules.length}"
  IO.println s!"gf_czech_lean.project_core_functions.target={FunctionSig.projectCoreFunctions.length}"
  IO.println s!"gf_czech_lean.project_core_plus_symbol_functions.target={FunctionSig.projectCorePlusSymbolFunctions.length}"
  emitExistenceTable "gf_czech_actual.family" gfRglCzechRoot actualGFCzechModules
  emitExistenceTable "gf_czech_lean" leanCzechRoot leanCzechModules
