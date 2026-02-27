/-
# Shared Structured Parse + Audit Helpers for README Trees

Utilities shared across compositional README modules:
- typed line extraction/parsing for headings and typed technical bullet families
- claim-bullet parsing helper
- hard-audit block predicate for prose-bearing bypass detection
-/

import Mettapedia.DocText.ReadmeTree

namespace Mettapedia.DocText.ReadmeStructuredParse

open Mettapedia.DocText.ReadmeTree

inductive ParsedTechnicalLine where
  | heading (level : Nat) (text : String)
  | pathItem (path : String)
  | syntaxItem (label : String) (pattern : String)
  | apiPath (path : String)
  | apiMember (member : String)
  | fileRefPath (path : String)
  | fileRefDesc (desc : String)
  deriving Repr, DecidableEq

private def ensurePeriod (s : String) : String :=
  if s.endsWith "." then s else s ++ "."

def stripBulletPrefix (line : String) : String :=
  if line.startsWith "- " then
    (line.drop 2).toString
  else if line.startsWith "  - " then
    (line.drop 4).toString
  else
    line

def headingEntries (blocks : List ReadmeBlock) : List (Nat × String) :=
  blocks.foldr
    (fun b acc =>
      match b with
      | .heading lvl txt => (lvl, txt) :: acc
      | _ => acc)
    []

def headingLine (h : Nat × String) : String :=
  let (lvl, txt) := h
  String.ofList (List.replicate lvl '#') ++ " " ++ txt

def pathEntries (blocks : List ReadmeBlock) : List PathItem :=
  blocks.foldr
    (fun b acc =>
      match b with
      | .pathItems items => items ++ acc
      | _ => acc)
    []

def syntaxEntries (blocks : List ReadmeBlock) : List SyntaxItem :=
  blocks.foldr
    (fun b acc =>
      match b with
      | .syntaxItems items => items ++ acc
      | _ => acc)
    []

def apiEntries (blocks : List ReadmeBlock) : List ApiItem :=
  blocks.foldr
    (fun b acc =>
      match b with
      | .apiItems items => items ++ acc
      | _ => acc)
    []

def fileRefEntries (blocks : List ReadmeBlock) : List (String × String) :=
  blocks.foldr
    (fun b acc =>
      match b with
      | .fileRef p d => (p, d) :: acc
      | _ => acc)
    []

def claimBulletLines (blocks : List ReadmeBlock) : List String :=
  blocks.foldr
    (fun b acc =>
      match b with
      | .claimBullets items =>
          (items.map (fun i => "- " ++ ensurePeriod i.text)) ++ acc
      | _ => acc)
    []

def technicalLines (blocks : List ReadmeBlock) : List String :=
  let headingLines := (headingEntries blocks).map headingLine
  let pathLines := (pathEntries blocks).map (fun i => "- `" ++ i.path ++ "`")
  let syntaxLines := (syntaxEntries blocks).map (fun i => "- " ++ i.label ++ ": `" ++ i.pattern ++ "`")
  let apiPathLines := (apiEntries blocks).map (fun i => "- `" ++ i.path ++ "`")
  let apiMemberLines :=
    (apiEntries blocks).foldr
      (fun i acc => (i.members.map (fun m => "  - `" ++ m ++ "`")) ++ acc)
      []
  let fileRefPathLines := (fileRefEntries blocks).map (fun (p, _) => "- `" ++ p ++ "`")
  let fileRefDescLines :=
    (fileRefEntries blocks).foldr
      (fun (_, d) acc => if d = "" then acc else ("  - " ++ d) :: acc)
      []
  headingLines ++ pathLines ++ syntaxLines ++ apiPathLines ++ apiMemberLines ++ fileRefPathLines ++ fileRefDescLines

def parseTechnicalLine? (blocks : List ReadmeBlock) (line : String) : Option ParsedTechnicalLine :=
  match (headingEntries blocks).find? (fun h => headingLine h = line) with
  | some (lvl, txt) => some (.heading lvl txt)
  | none =>
      match (pathEntries blocks).find? (fun p => "- `" ++ p.path ++ "`" = line) with
      | some p => some (.pathItem p.path)
      | none =>
          match (syntaxEntries blocks).find? (fun s => "- " ++ s.label ++ ": `" ++ s.pattern ++ "`" = line) with
          | some s => some (.syntaxItem s.label s.pattern)
          | none =>
              match (apiEntries blocks).find? (fun i => "- `" ++ i.path ++ "`" = line) with
              | some i => some (.apiPath i.path)
              | none =>
                  match (apiEntries blocks).findSome? (fun i =>
                    i.members.find? (fun m => "  - `" ++ m ++ "`" = line)) with
                  | some m => some (.apiMember m)
                  | none =>
                      match (fileRefEntries blocks).find? (fun (p, _) => "- `" ++ p ++ "`" = line) with
                      | some (p, _) => some (.fileRefPath p)
                      | none =>
                          match (fileRefEntries blocks).findSome? (fun (_, d) =>
                            if d = "" then none else
                            if "  - " ++ d = line then some d else none) with
                          | some d => some (.fileRefDesc d)
                          | none => none

def parseClaimBulletLine? {α : Type} (parseClaimLine? : String → Option α) (line : String) : Option α :=
  parseClaimLine? (stripBulletPrefix line)

def blockPassesHardAudit {α : Type} (parseClaimLine? : String → Option α) : ReadmeBlock → Bool
  | .heading _ _ => true
  | .paragraph sents => sents.all (fun s => (parseClaimLine? s).isSome)
  | .claimBullets items => items.all (fun i => (parseClaimLine? i.text).isSome)
  | .apiItems _ => true
  | .syntaxItems _ => true
  | .pathItems _ => true
  | .codeBlock _ _ => true
  | .fileRef _ d => d = "" || (parseClaimLine? d).isSome
  | .apiList _ => true
  | .bulletList _ => false
  | .bulletItem _ => false

end Mettapedia.DocText.ReadmeStructuredParse
