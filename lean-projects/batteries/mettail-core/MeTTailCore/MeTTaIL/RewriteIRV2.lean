import MeTTailCore.MeTTaIL.Syntax
import MeTTailCore.MeTTaIL.Substitution

namespace MeTTailCore.MeTTaIL.RewriteIRV2

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Substitution

/-!
# Rewrite IR v2 Draft Sidecar

This module does **not** replace the live `RewriteIR` artifact consumed by Rust.
It defines a sidecar draft keyed by the existing `rule_id`s.

Positive example:
- expose per-premise variable flow and root-update hints without breaking
  current `rewrite_ir.json` consumers.

Negative example:
- this is not a second source of rewrite semantics; the live semantics remain
  the existing structured `lhs` / `rhs` / `premises` artifact.
-/

structure PremiseVarFlow where
  premiseIndex : Nat
  premiseVars : List String
  introducedVars : List String
deriving Repr, DecidableEq, BEq

structure RootUpdateHint where
  lhsRootCtor : String
  rhsRootCtor : String
  lhsArity : Nat
  rhsArity : Nat
  preservedArgPositions : List Nat
  changedArgPositions : List Nat
deriving Repr, DecidableEq, BEq

structure RewriteIRV2Rule where
  ruleId : String
  ruleName : String
  sourceInstr : String
  sourceLabel : String
  priority : Nat
  lhsVars : List String
  premiseVarFlow : List PremiseVarFlow := []
  rhsVars : List String
  rhsRequires : List String := []
  rootUpdate : Option RootUpdateHint := none
deriving Repr, DecidableEq, BEq

structure RewriteIRV2Artifact where
  schemaVersion : Nat := 1
  dialect : String
  artifactLabel : String := "rewrite_ir_v2_draft_sidecar"
  baseRewriteIrSchemaVersion : Nat := 2
  rules : List RewriteIRV2Rule
deriving Repr, DecidableEq, BEq

private def orderedUniq (xs : List String) : List String :=
  xs.eraseDups

private def orderedUniqNat (xs : List Nat) : List Nat :=
  xs.eraseDups

private def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

private def premiseVars : Premise → List String
  | .freshness fc =>
      orderedUniq (fc.varName :: freeVars fc.term)
  | .congruence lhs rhs =>
      orderedUniq (freeVars lhs ++ freeVars rhs)
  | .relationQuery _ args =>
      orderedUniq (args.flatMap freeVars)

private def premiseVarFlowAux
    (seen : List String) (idx : Nat) : List Premise → List PremiseVarFlow
  | [] => []
  | prem :: rest =>
      let vars := premiseVars prem
      let introduced := vars.filter (fun x => !(seen.contains x))
      { premiseIndex := idx
        premiseVars := vars
        introducedVars := introduced } ::
        premiseVarFlowAux (seen ++ introduced) (idx + 1) rest

def derivePremiseVarFlow (lhsVars : List String) (premises : List Premise) :
    List PremiseVarFlow :=
  premiseVarFlowAux lhsVars 0 premises

def availableVarsAfterPremises (lhsVars : List String) (premises : List Premise) :
    List String :=
  let flows := derivePremiseVarFlow lhsVars premises
  orderedUniq (lhsVars ++ flows.flatMap (·.introducedVars))

private def rootUpdateHint? : Pattern → Pattern → Option RootUpdateHint
  | .apply lhsCtor lhsArgs, .apply rhsCtor rhsArgs =>
      let shared := Nat.min lhsArgs.length rhsArgs.length
      let positions := List.range shared
      let preserved := positions.filter (fun i => listGet? lhsArgs i = listGet? rhsArgs i)
      let changed := positions.filter (fun i => listGet? lhsArgs i ≠ listGet? rhsArgs i)
      some
        { lhsRootCtor := lhsCtor
          rhsRootCtor := rhsCtor
          lhsArity := lhsArgs.length
          rhsArity := rhsArgs.length
          preservedArgPositions := orderedUniqNat preserved
          changedArgPositions := orderedUniqNat changed }
  | _, _ => none

def RewriteIRV2Rule.ofRewriteRule
    (ruleId ruleName sourceInstr sourceLabel : String)
    (priority : Nat)
    (rw : RewriteRule) : RewriteIRV2Rule :=
  let lhsVars := orderedUniq (freeVars rw.left)
  let flows := derivePremiseVarFlow lhsVars rw.premises
  let available := orderedUniq (lhsVars ++ flows.flatMap (·.introducedVars))
  let rhsVars := orderedUniq (freeVars rw.right)
  let rhsRequires := rhsVars.filter (fun x => !(available.contains x))
  { ruleId := ruleId
    ruleName := ruleName
    sourceInstr := sourceInstr
    sourceLabel := sourceLabel
    priority := priority
    lhsVars := lhsVars
    premiseVarFlow := flows
    rhsVars := rhsVars
    rhsRequires := orderedUniq rhsRequires
    rootUpdate := rootUpdateHint? rw.left rw.right }

private def sortListByKey {α : Type} (xs : List α) (key : α → String) : List α :=
  (xs.toArray.qsort (fun a b => key a < key b)).toList

private def normalizeFlow (f : PremiseVarFlow) : PremiseVarFlow :=
  { f with
    premiseVars := orderedUniq f.premiseVars
    introducedVars := orderedUniq f.introducedVars }

private def normalizeRootUpdate (h : RootUpdateHint) : RootUpdateHint :=
  { h with
    preservedArgPositions := orderedUniqNat h.preservedArgPositions
    changedArgPositions := orderedUniqNat h.changedArgPositions }

private def normalizeRule (r : RewriteIRV2Rule) : RewriteIRV2Rule :=
  { r with
    sourceLabel := if r.sourceLabel.isEmpty then r.sourceInstr else r.sourceLabel
    lhsVars := orderedUniq r.lhsVars
    premiseVarFlow := r.premiseVarFlow.map normalizeFlow
    rhsVars := orderedUniq r.rhsVars
    rhsRequires := orderedUniq r.rhsRequires
    rootUpdate := r.rootUpdate.map normalizeRootUpdate }

private def normalizeArtifact (a : RewriteIRV2Artifact) : RewriteIRV2Artifact :=
  { a with
    rules := sortListByKey (a.rules.map normalizeRule)
      (fun r => s!"{r.sourceInstr}:{r.priority}:{r.ruleId}:{r.ruleName}") }

private def jsonEscape (s : String) : String :=
  s.foldl
    (fun acc c =>
      acc ++
      match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | _ => String.singleton c)
    ""

private def jsonStr (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

private def jsonNat (n : Nat) : String :=
  toString n

private def renderStringList (xs : List String) : String :=
  "[" ++ String.intercalate "," (xs.map jsonStr) ++ "]"

private def renderNatList (xs : List Nat) : String :=
  "[" ++ String.intercalate "," (xs.map jsonNat) ++ "]"

private def renderPremiseVarFlow (f : PremiseVarFlow) : String :=
  "{"
    ++ "\"premise_index\":" ++ jsonNat f.premiseIndex ++ ","
    ++ "\"premise_vars\":" ++ renderStringList f.premiseVars ++ ","
    ++ "\"introduced_vars\":" ++ renderStringList f.introducedVars
  ++ "}"

private def renderRootUpdateHint (h : RootUpdateHint) : String :=
  "{"
    ++ "\"lhs_root_ctor\":" ++ jsonStr h.lhsRootCtor ++ ","
    ++ "\"rhs_root_ctor\":" ++ jsonStr h.rhsRootCtor ++ ","
    ++ "\"lhs_arity\":" ++ jsonNat h.lhsArity ++ ","
    ++ "\"rhs_arity\":" ++ jsonNat h.rhsArity ++ ","
    ++ "\"preserved_arg_positions\":" ++ renderNatList h.preservedArgPositions ++ ","
    ++ "\"changed_arg_positions\":" ++ renderNatList h.changedArgPositions
  ++ "}"

private def renderRule (r : RewriteIRV2Rule) : String :=
  "{"
    ++ "\"rule_id\":" ++ jsonStr r.ruleId ++ ","
    ++ "\"rule_name\":" ++ jsonStr r.ruleName ++ ","
    ++ "\"source_instr\":" ++ jsonStr r.sourceInstr ++ ","
    ++ "\"source_label\":" ++ jsonStr r.sourceLabel ++ ","
    ++ "\"priority\":" ++ jsonNat r.priority ++ ","
    ++ "\"lhs_vars\":" ++ renderStringList r.lhsVars ++ ","
    ++ "\"premise_var_flow\":["
    ++ String.intercalate "," (r.premiseVarFlow.map renderPremiseVarFlow)
    ++ "],"
    ++ "\"rhs_vars\":" ++ renderStringList r.rhsVars ++ ","
    ++ "\"rhs_requires\":" ++ renderStringList r.rhsRequires ++ ","
    ++ "\"root_update\":"
    ++ (match r.rootUpdate with
      | some h => renderRootUpdateHint h
      | none => "null")
  ++ "}"

def RewriteIRV2Artifact.renderJson (a : RewriteIRV2Artifact) : String :=
  let norm := normalizeArtifact a
  "{"
    ++ "\"schema_version\":" ++ jsonNat norm.schemaVersion ++ ","
    ++ "\"dialect\":" ++ jsonStr norm.dialect ++ ","
    ++ "\"artifact_label\":" ++ jsonStr norm.artifactLabel ++ ","
    ++ "\"base_rewrite_ir_schema_version\":" ++ jsonNat norm.baseRewriteIrSchemaVersion ++ ","
    ++ "\"rules\":[" ++ String.intercalate "," (norm.rules.map renderRule) ++ "]"
  ++ "}"

private def isRuleId (rule : String) : Bool :=
  if !rule.startsWith "R" then
    false
  else
    let tail := (rule.drop 1).toString
    !tail.isEmpty && tail.toList.all Char.isDigit

private def lintRule (r : RewriteIRV2Rule) : List String :=
  let idErrs :=
    if isRuleId r.ruleId then [] else [s!"invalid rule_id '{r.ruleId}'"]
  let nameErrs :=
    if r.ruleName.isEmpty then [s!"{r.ruleId}: rule_name must be non-empty"] else []
  let sourceErrs :=
    if r.sourceInstr.isEmpty then
      [s!"{r.ruleId}: source_instr must be non-empty"]
    else if !r.sourceInstr.startsWith "C_" then
      [s!"{r.ruleId}: source_instr must start with C_, got '{r.sourceInstr}'"]
    else
      []
  let flowErrs :=
    r.premiseVarFlow.filterMap fun f =>
      if f.introducedVars.all (fun x => f.premiseVars.contains x) then
        none
      else
        some s!"{r.ruleId}: premise flow {f.premiseIndex} introduces vars not present in premise_vars"
  idErrs ++ nameErrs ++ sourceErrs ++ flowErrs

def RewriteIRV2Artifact.lintErrors (a : RewriteIRV2Artifact) : List String :=
  let norm := normalizeArtifact a
  let schemaErrs :=
    if norm.schemaVersion < 1 then
      [s!"schema_version must be >= 1, got {norm.schemaVersion}"]
    else
      []
  let dialectErrs :=
    if norm.dialect.isEmpty then ["dialect must be non-empty"] else []
  let labelErrs :=
    if norm.artifactLabel.isEmpty then ["artifact_label must be non-empty"] else []
  let ruleErrs :=
    if norm.rules.isEmpty then ["rules cannot be empty"] else []
  let dupRuleIds :=
    let ids := norm.rules.map (·.ruleId)
    if ids.length == ids.eraseDups.length then [] else ["rule_id values must be unique"]
  schemaErrs ++ dialectErrs ++ labelErrs ++ ruleErrs ++ dupRuleIds
    ++ (norm.rules.map lintRule).foldl (· ++ ·) []

def RewriteIRV2Artifact.isLintClean (a : RewriteIRV2Artifact) : Bool :=
  a.lintErrors.isEmpty

private def fnv64Offset : UInt64 := 14695981039346656037
private def fnv64Prime : UInt64 := 1099511628211

def checksumText (text : String) : UInt64 :=
  text.toList.foldl
    (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * fnv64Prime)
    fnv64Offset

def RewriteIRV2Artifact.checksum (a : RewriteIRV2Artifact) : UInt64 :=
  checksumText a.renderJson

def RewriteIRV2Artifact.checksumString (a : RewriteIRV2Artifact) : String :=
  toString a.checksum

end MeTTailCore.MeTTaIL.RewriteIRV2
