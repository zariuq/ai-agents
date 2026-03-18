import Mettapedia.Languages.GF.HandCrafted.Abstract

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.HandCrafted.Abstract
open Mettapedia.Languages.GF.HandCrafted.Abstract.FunctionSig

private def scopeFamilies : List (String × List FunctionSig) :=
  [ ("core", allCoreFunctions)
  , ("adverb", adverbFunctions)
  , ("tense", tenseFunctions)
  , ("text", textFunctions)
  , ("idiom", idiomFunctions)
  , ("numeral", numeralFunctions)
  , ("structural", structuralFunctions)
  , ("symbol", symbolFunctions)
  , ("extend", extendFunctions)
  , ("construction", constructionFunctions)
  ]

def main : IO Unit := do
  let projectCoreCount := (FunctionSig.projectCoreFunctions).length
  let projectCoreGFNativeCount := (FunctionSig.projectCoreGFNativeFunctions).length
  let projectCorePlusSymbolCount := (FunctionSig.projectCorePlusSymbolFunctions).length
  IO.println s!"gf_scope.project_core.total={projectCoreCount}"
  IO.println s!"gf_scope.project_core_gf_native.total={projectCoreGFNativeCount}"
  IO.println s!"gf_scope.project_core_plus_symbol.total={projectCorePlusSymbolCount}"
  for (family, fns) in scopeFamilies do
    IO.println s!"gf_scope.family.{family}.total={fns.length}"
