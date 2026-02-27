/-
# Shared Document Tree for GF-Generated READMEs

Pure structural tree + Markdown renderer.
No GF dependency — GF sentences arrive as pre-rendered strings.
-/

namespace Mettapedia.DocText.ReadmeTree

/-- Typed API item for documentation lists. -/
structure ApiItem where
  path : String
  members : List String := []
  note : Option String := none
  deriving Repr, BEq, DecidableEq

/-- Typed syntax-pattern item for documentation lists. -/
structure SyntaxItem where
  label : String
  pattern : String
  deriving Repr, BEq, DecidableEq

/-- Typed path item for path-only bullet lists. -/
structure PathItem where
  path : String
  deriving Repr, BEq, DecidableEq

/-- Claim-backed bullet item (text must come from claim renderer upstream). -/
structure ClaimBullet where
  text : String
  deriving Repr, BEq, DecidableEq

/-- A block in a README document tree. -/
inductive ReadmeBlock where
  | heading (level : Nat) (text : String)
  | paragraph (sentences : List String)
  | bulletList (items : List ReadmeBlock)
  | claimBullets (items : List ClaimBullet)
  | apiItems (items : List ApiItem)
  | syntaxItems (items : List SyntaxItem)
  | pathItems (items : List PathItem)
  | bulletItem (text : String)
  | codeBlock (lang : String) (code : String)
  | fileRef (path : String) (desc : String)
  | apiList (items : List (String × String))
  deriving Repr

private def headingPrefix (level : Nat) : String :=
  String.ofList (List.replicate level '#') ++ " "

private def ensurePeriod (s : String) : String :=
  if s.endsWith "." then s else s ++ "."

private def renderApiItem (item : ApiItem) : String :=
  let header := "- `" ++ item.path ++ "`"
  let memberLines := item.members.map (fun m => "  - `" ++ m ++ "`")
  let noteLines := match item.note with
    | some n => ["  - " ++ n]
    | none => []
  String.intercalate "\n" ([header] ++ memberLines ++ noteLines)

private def renderSyntaxItem (item : SyntaxItem) : String :=
  "- " ++ item.label ++ ": `" ++ item.pattern ++ "`"

private def renderPathItem (item : PathItem) : String :=
  "- `" ++ item.path ++ "`"

mutual
  partial def renderBlock : ReadmeBlock → String
    | .heading level text => headingPrefix level ++ text
    | .paragraph sents =>
        String.intercalate "\n" (sents.map ensurePeriod)
    | .bulletList items =>
        String.intercalate "\n" (items.map renderBulletChild)
    | .claimBullets items =>
        String.intercalate "\n" (items.map fun i => "- " ++ ensurePeriod i.text)
    | .apiItems items =>
        String.intercalate "\n" (items.map renderApiItem)
    | .syntaxItems items =>
        String.intercalate "\n" (items.map renderSyntaxItem)
    | .pathItems items =>
        String.intercalate "\n" (items.map renderPathItem)
    | .bulletItem text => "- " ++ text
    | .codeBlock lang code =>
        "```" ++ lang ++ "\n" ++ code ++ "\n```"
    | .fileRef path desc => "- `" ++ path ++ "`\n  - " ++ desc
    | .apiList items =>
        String.intercalate "\n" (items.map fun (name, desc) =>
          "  - `" ++ name ++ "` — " ++ desc)

  partial def renderBulletChild : ReadmeBlock → String
    | .bulletItem text => "- " ++ text
    | .fileRef path desc => "- `" ++ path ++ "`\n  - " ++ desc
    | .claimBullets items =>
        String.intercalate "\n" (items.map fun i => "  - " ++ ensurePeriod i.text)
    | .pathItems items =>
        String.intercalate "\n" (items.map fun i => "  - `" ++ i.path ++ "`")
    | other => renderBlock other
end

def renderDoc (blocks : List ReadmeBlock) : String :=
  String.intercalate "\n\n" (blocks.map renderBlock) ++ "\n"

end Mettapedia.DocText.ReadmeTree
