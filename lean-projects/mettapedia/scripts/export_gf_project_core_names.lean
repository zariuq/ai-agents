import Mettapedia.Languages.GF.HandCrafted.Abstract

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.HandCrafted.Abstract
open Mettapedia.Languages.GF.HandCrafted.Abstract.FunctionSig

private def emitNames (tag : String) (names : List String) : IO Unit := do
  IO.println s!"{tag}.count={names.length}"
  for nm in names do
    IO.println s!"{tag}.name={nm}"

def main : IO Unit := do
  emitNames "gf_scope.project_core" projectCoreFunctionNames
  emitNames "gf_scope.project_core_gf_native" projectCoreGFNativeFunctionNames
  emitNames "gf_scope.project_core_plus_symbol" projectCorePlusSymbolFunctionNames
