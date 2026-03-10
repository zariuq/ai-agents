import Algorithms.MeTTa.LookupPlans
import Algorithms.MeTTa.Simple.Relations
import Mettapedia.Languages.MeTTa.ExecutionContract
import Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment
import Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment

/-!
# PeTTa Execution Contract

First concrete execution-contract instance for the shared MeTTa certificate
surface.

This file intentionally exports the first honest query and space-effect entries:
- `match &self` as the `spaceMatch` lookup family
- `get-atoms &self` as the `selfFacts` lookup family
- `add-atom &self` as a MORK sink-backed space effect
- `remove-atom &self` as a MORK sink-backed space effect
- the first pure intrinsic builtin slice inherited through `coreIntrinsicBuiltins`

Positive example:
- `match &self` and `get-atoms &self` are read-only queries, MORK/MM2-backed,
  query-compilable, and admit outcome-set memoization.
- `spaceMatch` relation premises expose explicit argument roles and the fresh
  result-variable invariant needed by the MM2 compiler.
- `add-atom` and `remove-atom` are stateful space effects, MORK/MM2-backed, and
  space-effect-compilable.
- `add-atom` / `remove-atom` fact payloads expose explicit payload/sink lanes
  instead of forcing Rust to infer them from surface syntax.
- `add-atom` / `remove-atom` rewrite-rule payloads expose explicit
  `source_rule_payload` lanes instead of forcing Rust to infer dynamic rule
  updates from raw syntax.
- `+`, `-`, `*`, `/`, `%`, `abs-math`, `and`, `or`, `not`, `xor`, `if`, and
  structural `=` are the current pure intrinsic builtins, MORK/MM2-backed, and
  admit scalar/outcome-set memoization.

Negative example:
- this file still does not certify premise-bearing rewrite execution or arbitrary
  grounded/FFI builtin catalogs.
- this file intentionally does not export the full shared intrinsic catalog yet:
  uncertified PeTTa MM2 lowerings must fail closed rather than overclaim support.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract

open Mettapedia.Languages.MeTTa.ExecutionContract
open Mettapedia.Languages.MeTTa.RuntimeKernel
open MeTTailCore.MeTTaIL.EffectSafety

/-- First PeTTa execution-contract entry: `match &self` via `spaceMatch`. -/
def spaceMatchLookupContract : LookupQueryContract where
  head := "match"
  surfaceHead := some "match"
  arity := 3
  lookupFamily := Algorithms.MeTTa.LookupPlans.pettaSpaceMatchFamily
  owner := .artifactBackend
  kernelClass := .query
  effectClass := queryFragment.effectClass
  resourceClass := queryFragment.resourceClass
  backendName := queryFragment.backendName
  supportedMemoShapes := [.scalar, .outcomeSet]
  sourceRuleCompilable := false
  queryCompilable := true
  spaceEffectCompilable := false
  builtinDemand := none
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.query_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_scalar"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.anyFactMatch_mem_spaceMatch"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.anyFactMatch_toComputableSourceQuery"
    ]

def spaceMatchEntry : ExecutionContractEntry :=
  .lookupQuery spaceMatchLookupContract

def getAtomsLookupContract : LookupQueryContract where
  head := "get-atoms"
  surfaceHead := some "get-atoms"
  arity := 1
  lookupFamily := Algorithms.MeTTa.LookupPlans.pettaGetAtomsFamily
  owner := .artifactBackend
  kernelClass := .query
  effectClass := queryFragment.effectClass
  resourceClass := queryFragment.resourceClass
  backendName := queryFragment.backendName
  supportedMemoShapes := [.outcomeSet]
  sourceRuleCompilable := false
  queryCompilable := true
  spaceEffectCompilable := false
  builtinDemand := none
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.query_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.getAtoms_toComputableSourceQuery"
    ]

def getAtomsEntry : ExecutionContractEntry :=
  .lookupQuery getAtomsLookupContract

def addAtomSpaceEffectContract : SpaceEffectContract where
  head := "add-atom"
  arity := 2
  owner := .artifactBackend
  kernelClass := .spaceEffect
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  sourceRuleCompilable := false
  queryCompilable := false
  spaceEffectCompilable := true
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_resource"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_backend"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_not_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.addAtom_fireSourceRule_mem"
    ]

def addAtomEntry : ExecutionContractEntry :=
  .spaceEffect addAtomSpaceEffectContract

def removeAtomSpaceEffectContract : SpaceEffectContract where
  head := "remove-atom"
  arity := 2
  owner := .artifactBackend
  kernelClass := .spaceEffect
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  sourceRuleCompilable := false
  queryCompilable := false
  spaceEffectCompilable := true
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_resource"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_backend"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_not_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.removeAtom_fireSourceRule_mem"
    ]

def removeAtomEntry : ExecutionContractEntry :=
  .spaceEffect removeAtomSpaceEffectContract

def spaceMatchRelationPremiseContract : RelationPremiseContract where
  relation := "spaceMatch"
  arity := 3
  lookupFamily := Algorithms.MeTTa.LookupPlans.pettaSpaceMatchFamily
  argRoles := [.pattern, .template, .resultVar]
  resultBindingPolicy := some .mustBeFreshVar
  loweringKind := .factMatchEmitPayload
  owner := .artifactBackend
  kernelClass := .query
  effectClass := queryFragment.effectClass
  resourceClass := queryFragment.resourceClass
  backendName := queryFragment.backendName
  supportedMemoShapes := [.scalar, .outcomeSet]
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.query_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_scalar"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.query_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.anyFactMatch_mem_spaceMatch"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceCoreFragment.anyFactMatch_toComputableSourceQuery"
    ]

def spaceMatchRelationPremiseEntry : ExecutionContractEntry :=
  .relationPremise spaceMatchRelationPremiseContract

def addAtomFactPayloadContract : SpaceEffectPayloadContract where
  head := "add-atom"
  arity := 2
  spaceArgPosition := 0
  payloadArgPosition := 1
  payloadKind := .factPayload
  payloadShape := .nonRewritePattern
  sinkKind := .insertFact
  owner := .artifactBackend
  kernelClass := .spaceEffect
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  sourceRuleCompilable := false
  queryCompilable := false
  spaceEffectCompilable := true
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_resource"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_backend"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_not_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.addAtom_fireSourceRule_mem"
    ]

def addAtomFactPayloadEntry : ExecutionContractEntry :=
  .spaceEffectPayload addAtomFactPayloadContract

def addAtomRulePayloadContract : SpaceEffectPayloadContract where
  head := "add-atom"
  arity := 2
  spaceArgPosition := 0
  payloadArgPosition := 1
  payloadKind := .sourceRulePayload
  payloadShape := .rewriteEqRule
  sinkKind := .insertRule
  owner := .artifactBackend
  kernelClass := .spaceEffect
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  sourceRuleCompilable := false
  queryCompilable := false
  spaceEffectCompilable := true
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_resource"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_backend"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_not_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.addAtom_fireSourceRule_mem"
    ]

def addAtomRulePayloadEntry : ExecutionContractEntry :=
  .spaceEffectPayload addAtomRulePayloadContract

def removeAtomFactPayloadContract : SpaceEffectPayloadContract where
  head := "remove-atom"
  arity := 2
  spaceArgPosition := 0
  payloadArgPosition := 1
  payloadKind := .factPayload
  payloadShape := .nonRewritePattern
  sinkKind := .removeFact
  owner := .artifactBackend
  kernelClass := .spaceEffect
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  sourceRuleCompilable := false
  queryCompilable := false
  spaceEffectCompilable := true
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_resource"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_backend"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_not_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.removeAtom_fireSourceRule_mem"
    ]

def removeAtomFactPayloadEntry : ExecutionContractEntry :=
  .spaceEffectPayload removeAtomFactPayloadContract

def removeAtomRulePayloadContract : SpaceEffectPayloadContract where
  head := "remove-atom"
  arity := 2
  spaceArgPosition := 0
  payloadArgPosition := 1
  payloadKind := .sourceRulePayload
  payloadShape := .rewriteEqRule
  sinkKind := .removeRule
  owner := .artifactBackend
  kernelClass := .spaceEffect
  effectClass := spaceEffectFragment.effectClass
  resourceClass := spaceEffectFragment.resourceClass
  backendName := spaceEffectFragment.backendName
  sourceRuleCompilable := false
  queryCompilable := false
  spaceEffectCompilable := true
  theoremRefs :=
    [ "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_effectClass"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_resource"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_backend"
    , "Mettapedia.Languages.MeTTa.RuntimeKernel.spaceEffect_not_memo_outcomeSet"
    , "Mettapedia.Languages.MeTTa.PeTTa.SpaceEffectFragment.removeAtom_fireSourceRule_mem"
    ]

def removeAtomRulePayloadEntry : ExecutionContractEntry :=
  .spaceEffectPayload removeAtomRulePayloadContract

/-- PeTTa-local intrinsic slice that matches the live MM2 lowering in
`mettail-rust`.

This list is intentionally narrow. A head belongs here only when the current
MORK/MM2 backend has a concrete lowering target for it.

Positive example:
- integer numerics (`+`, `-`, `*`, `/`, `%`, `abs-math`)
  These lower to MORK pure ops such as `sum_i32`, `product_i32`, `sub_i32`,
  `div_i32`, `mod_i32`, and `abs_i32`.
- booleans (`and`, `or`, `not`, `xor`)
- `if`
- structural `=`

Negative example:
- numeric comparisons like `<` and `>=`
  These are excluded until there is either a real MORK comparison primitive to
  lower to or an explicit grounded-host contract lane.
- tuple/list operators like `append` and `cons`
- float/transcendental intrinsics
-/
def pettaMm2IntrinsicSpecs : List CoreIntrinsicSpec :=
  [ { head := "=", minArity := 2, maxArity := some 2, demand := .structuralEqArgs }
  , { head := "if", minArity := 2, maxArity := some 3, demand := .boolThenElseArgs }
  , { head := "and", minArity := 0, demand := .boolArgs }
  , { head := "or", minArity := 0, demand := .boolArgs }
  , { head := "not", minArity := 1, maxArity := some 1, demand := .boolArgs }
  , { head := "xor", minArity := 0, demand := .boolArgs }
  , { head := "+", minArity := 2, maxArity := none, demand := .numericArgs }
  , { head := "-", minArity := 1, maxArity := none, demand := .numericArgs }
  , { head := "*", minArity := 2, maxArity := none, demand := .numericArgs }
  , { head := "/", minArity := 2, maxArity := some 2, demand := .numericArgs }
  , { head := "%", minArity := 2, maxArity := some 2, demand := .numericArgs }
  , { head := "abs-math", minArity := 1, maxArity := some 1, demand := .numericArgs }
  ]

def pettaMm2IntrinsicContracts : List IntrinsicBuiltinContract :=
  pettaMm2IntrinsicSpecs.map mkCoreIntrinsicContract

def pettaMm2IntrinsicEntries : List ExecutionContractEntry :=
  pettaMm2IntrinsicContracts.map .intrinsicBuiltin

def pettaExecutionContractArtifact : ExecutionContractArtifact where
  dialect := "petta"
  entries :=
    [ spaceMatchEntry
    , getAtomsEntry
    , addAtomEntry
    , removeAtomEntry
    , spaceMatchRelationPremiseEntry
    , addAtomFactPayloadEntry
    , addAtomRulePayloadEntry
    , removeAtomFactPayloadEntry
    , removeAtomRulePayloadEntry
    ] ++ pettaMm2IntrinsicEntries

theorem spaceMatch_effectClass :
    spaceMatchLookupContract.effectClass = .readOnlyLookup := rfl

theorem spaceMatch_resource :
    spaceMatchLookupContract.resourceClass = .defaultAtomSpace := rfl

theorem spaceMatch_backend :
    spaceMatchLookupContract.backendName = "MORK/MM2" := rfl

theorem spaceMatch_noFalseNegatives :
    spaceMatchLookupContract.noFalseNegatives = true := rfl

theorem spaceMatch_exactResult :
    spaceMatchLookupContract.exactResult = false := rfl

theorem spaceMatch_stratifiedNegationSafe :
    spaceMatchLookupContract.stratifiedNegationSafe = true := rfl

theorem spaceMatch_scalarMemo :
    spaceMatchLookupContract.effectClass.supportsMemoShape .scalar = true := by
  simpa [spaceMatchLookupContract] using query_memo_scalar

theorem spaceMatch_outcomeSetMemo :
    spaceMatchLookupContract.effectClass.supportsMemoShape .outcomeSet = true := by
  simpa [spaceMatchLookupContract] using query_memo_outcomeSet

theorem getAtoms_effectClass :
    getAtomsLookupContract.effectClass = .readOnlyLookup := rfl

theorem getAtoms_resource :
    getAtomsLookupContract.resourceClass = .defaultAtomSpace := rfl

theorem getAtoms_backend :
    getAtomsLookupContract.backendName = "MORK/MM2" := rfl

theorem getAtoms_exactResult :
    getAtomsLookupContract.exactResult = true := rfl

theorem getAtoms_outcomeSetMemo :
    getAtomsLookupContract.effectClass.supportsMemoShape .outcomeSet = true := by
  simpa [getAtomsLookupContract] using query_memo_outcomeSet

theorem addAtom_effectClass :
    addAtomSpaceEffectContract.effectClass = .writesState := rfl

theorem addAtom_spaceEffectCompilable :
    addAtomSpaceEffectContract.spaceEffectCompilable = true := rfl

theorem removeAtom_effectClass :
    removeAtomSpaceEffectContract.effectClass = .writesState := rfl

theorem removeAtom_spaceEffectCompilable :
    removeAtomSpaceEffectContract.spaceEffectCompilable = true := rfl

theorem spaceMatchRelationPremise_freshResult :
    spaceMatchRelationPremiseContract.resultBindingPolicy = some .mustBeFreshVar := rfl

theorem addAtomFactPayload_sink :
    addAtomFactPayloadContract.sinkKind = .insertFact := rfl

theorem removeAtomFactPayload_sink :
    removeAtomFactPayloadContract.sinkKind = .removeFact := rfl

theorem addAtomRulePayload_sink :
    addAtomRulePayloadContract.sinkKind = .insertRule := rfl

theorem removeAtomRulePayload_sink :
    removeAtomRulePayloadContract.sinkKind = .removeRule := rfl

theorem plusIntrinsic_effectClass :
    (mkCoreIntrinsicContract { head := "+", minArity := 2, demand := .numericArgs }).effectClass = .pureStructural := rfl

theorem plusIntrinsic_scalarMemo :
    (mkCoreIntrinsicContract { head := "+", minArity := 2, demand := .numericArgs }).effectClass.supportsMemoShape .scalar = true := by
  simpa [mkCoreIntrinsicContract] using exec_memo_scalar

theorem ifIntrinsic_relation :
    (mkCoreIntrinsicContract { head := "if", minArity := 2, maxArity := some 3, demand := .boolThenElseArgs }).relation =
      Algorithms.MeTTa.Simple.intrinsicRelationName "if" := rfl

def exportPeTTaExecutionContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := pettaExecutionContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"petta execution contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "petta.execution_contract.json"
    let checksumPath := outDir / "petta.execution_contract.checksum"
    IO.FS.createDirAll outDir
    IO.FS.writeFile jsonPath (artifact.renderJson ++ "\n")
    IO.FS.writeFile checksumPath (artifact.checksumString ++ "\n")
    IO.println s!"exported petta execution contract to {outDir}"
    pure 0

def checkPeTTaExecutionContract (outDir : System.FilePath) : IO UInt32 := do
  let artifact := pettaExecutionContractArtifact
  let lintErrs := artifact.lintErrors
  if !lintErrs.isEmpty then
    IO.println s!"petta execution contract lint failed:\n{String.intercalate "\n" lintErrs}"
    pure 2
  else
    let jsonPath := outDir / "petta.execution_contract.json"
    let checksumPath := outDir / "petta.execution_contract.checksum"
    try
      let jsonText ← IO.FS.readFile jsonPath
      let checksumText ← IO.FS.readFile checksumPath
      let jsonOk := jsonText.trimAscii.toString == artifact.renderJson.trimAscii.toString
      let checksumOk := checksumText.trimAscii.toString == artifact.checksumString.trimAscii.toString
      if jsonOk && checksumOk then
        IO.println s!"[ok] petta execution contract matches at {outDir}"
        pure 0
      else
        if !jsonOk then
          IO.println s!"[drift] petta execution contract json mismatch at {jsonPath}"
        if !checksumOk then
          IO.println s!"[drift] petta execution contract checksum mismatch at {checksumPath}"
        pure 3
    catch e =>
      IO.println s!"petta execution contract check failed: {e}"
      pure 2

section Canaries
#check @spaceMatchLookupContract
#check @pettaExecutionContractArtifact
#check @exportPeTTaExecutionContract
#check @checkPeTTaExecutionContract
end Canaries

end Mettapedia.Languages.MeTTa.PeTTa.ExecutionContract
