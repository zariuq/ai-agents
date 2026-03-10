import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.English.Linearization.Coverage

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.Abstract.FunctionSig
open Mettapedia.Languages.GF.English.Linearization

private def explicitCount (fns : List FunctionSig) : Nat :=
  (fns.filter (fun f => explicitlyHandledFunctionNames.contains f.name)).length

private def uncoveredPreview (fns : List FunctionSig) (k : Nat) : String :=
  String.intercalate "," <|
    ((fns.map (·.name)).filter (fun nm => !(explicitlyHandledFunctionNames.contains nm))).take k

def main : IO Unit := do
  let projectCoreFns := (FunctionSig.projectCoreFunctions)
  let projectCorePlusSymbolFns := (FunctionSig.projectCorePlusSymbolFunctions)
  let projectCoreExplicit := explicitCount projectCoreFns
  let projectCorePlusSymbolExplicit := explicitCount projectCorePlusSymbolFns
  let projectCoreUncovered := projectCoreFns.length - projectCoreExplicit
  let projectCorePlusSymbolUncovered := projectCorePlusSymbolFns.length - projectCorePlusSymbolExplicit
  IO.println s!"gf_en_linearization.project_core.total={projectCoreFns.length}"
  IO.println s!"gf_en_linearization.project_core.explicit={projectCoreExplicit}"
  IO.println s!"gf_en_linearization.project_core.uncovered={projectCoreUncovered}"
  IO.println s!"gf_en_linearization.project_core.preview_uncovered_csv={uncoveredPreview projectCoreFns 80}"
  IO.println s!"gf_en_linearization.project_core_plus_symbol.total={projectCorePlusSymbolFns.length}"
  IO.println s!"gf_en_linearization.project_core_plus_symbol.explicit={projectCorePlusSymbolExplicit}"
  IO.println s!"gf_en_linearization.project_core_plus_symbol.uncovered={projectCorePlusSymbolUncovered}"
  IO.println s!"gf_en_linearization.project_core_plus_symbol.preview_uncovered_csv={uncoveredPreview projectCorePlusSymbolFns 80}"
  if projectCoreExplicit + projectCoreUncovered != projectCoreFns.length then
    throw <| IO.userError "project core accounting mismatch"
  if projectCorePlusSymbolExplicit + projectCorePlusSymbolUncovered != projectCorePlusSymbolFns.length then
    throw <| IO.userError "project core plus symbol accounting mismatch"
