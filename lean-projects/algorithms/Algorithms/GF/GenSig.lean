/-
# Generate GrammarSig from PGF JSON export

Usage: lake exe gfGenSig <pgf_json_path> <output_lean_path> <namespace>

Example:
  lake exe gfGenSig gf_fragments/json_export/PaperAmbiguity.json \
    Algorithms/GF/Generated/PaperAmbiguitySig.lean \
    Algorithms.GF.Generated.PaperAmbiguitySig
-/

import GFCore
import GFCore.SigGen

open GFCore

def main (args : List String) : IO UInt32 := do
  match args with
  | [jsonPath, outPath, ns] =>
    IO.println s!"Reading PGF JSON from: {jsonPath}"
    let sig ← sigFromPGFJsonFile jsonPath
    IO.println s!"Grammar: {sig.grammar}"
    IO.println s!"Start cats: {sig.startCats}"
    IO.println s!"Functions: {sig.funs.size}"
    let leanSrc := generateSigLean sig ns
    IO.FS.writeFile outPath leanSrc
    IO.println s!"Wrote: {outPath}"
    return 0
  | _ =>
    IO.eprintln "Usage: gfGenSig <pgf_json_path> <output_lean_path> <namespace>"
    return 1
