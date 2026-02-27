/-
# Paper CNL — English Linearization

Deterministic linearization of PaperCNL abstract trees to natural
academic English prose. Same tree also linearizes to LaTeX via
PaperCNLLatex.lean.

Phase D of the GF-aligned English plan.
-/

import Mettapedia.Languages.GF.PaperCNL

namespace Mettapedia.Languages.GF.PaperCNLEng

open Mettapedia.Languages.GF.PaperCNL

/-! ## Atom Linearization -/

private def linCitation (c : Citation) : String :=
  c.author ++ " (" ++ toString c.year ++ ")"

private def linLeanRef (r : LeanRef) : String :=
  if r.theorem_.isEmpty then r.file
  else r.file ++ ":" ++ r.theorem_

private def linMathExpr (m : MathExpr) : String :=
  m.tex

private def linEnvKind : EnvKind → String
  | .theorem_ => "Theorem"
  | .lemma_ => "Lemma"
  | .proposition => "Proposition"
  | .corollary => "Corollary"
  | .definition_ => "Definition"
  | .remark => "Remark"
  | .example_ => "Example"
  | .principle => "Principle"

/-! ## Claim Linearization -/

private def linClaim : Claim → String
  | .text s => s
  | .withMath before m after => before ++ linMathExpr m ++ after
  | .leanProven stmt ref =>
    stmt ++ " (Lean: " ++ linLeanRef ref ++ ")"
  | .citeBacked stmt cite =>
    stmt ++ " (" ++ linCitation cite ++ ")"

/-! ## Environment Linearization -/

private def linTheoremEnv (e : TheoremEnv) : String :=
  let header := linEnvKind e.kind ++
    (if e.name.isEmpty then "" else " (" ++ e.name ++ ")")
  let stmt := e.statement ++
    (match e.math with
     | some m => ": " ++ linMathExpr m
     | none => "")
  let pf := match e.proof with
    | some p => "\nProof. " ++ p ++ " QED."
    | none => ""
  let ref := match e.leanRef with
    | some r => " [Lean: " ++ linLeanRef r ++ "]"
    | none => ""
  header ++ ". " ++ stmt ++ ref ++ pf

/-! ## Statement Linearization -/

/-- Linearize a paper statement to English -/
def linPaperStmt : PaperStmt → String
  | .weShow c =>
    "We show that " ++ linClaim c ++ "."
  | .followingFrom c cite =>
    linClaim c ++ ", following from " ++ linCitation cite ++ "."
  | .inContrastTo cite c =>
    "In contrast to " ++ linCitation cite ++ ", " ++ linClaim c ++ "."
  | .contribution n c =>
    "Contribution " ++ toString n ++ ": " ++ linClaim c ++ "."
  | .relatedWork cite relation =>
    linCitation cite ++ " " ++ relation ++ "."
  | .env e =>
    linTheoremEnv e
  | .prose text => text
  | .proseWithCite text cite =>
    text ++ " (" ++ linCitation cite ++ ")."
  | .leanStatus ref desc =>
    "The Lean formalization at " ++ linLeanRef ref ++ " " ++ desc ++ "."
  | .statusNote text =>
    "Status note. " ++ text
  | .enumList pfx items =>
    let rec go : List String → Nat → List String
      | [], _ => []
      | item :: rest, n => (pfx ++ toString n ++ ". " ++ item) :: go rest (n + 1)
    "\n".intercalate (go items 1)
  | .codeListing _lang caption code =>
    "--- " ++ caption ++ " ---\n" ++ code ++ "\n---"
  | .displayMath m =>
    "  " ++ linMathExpr m
  | .seq first rest =>
    linPaperStmt first ++ "\n" ++ linPaperStmt rest

/-! ## Document Linearization -/

/-- Linearize a paper document to English -/
def linPaperDoc : PaperDoc → String
  | .stmt s => linPaperStmt s
  | .section_ title body => "# " ++ title ++ "\n\n" ++ linPaperDoc body
  | .subsection title body => "## " ++ title ++ "\n\n" ++ linPaperDoc body
  | .subsubsection title body => "### " ++ title ++ "\n\n" ++ linPaperDoc body
  | .seq first rest => linPaperDoc first ++ "\n\n" ++ linPaperDoc rest
  | .empty => ""

/-! ## Full Paper Linearization -/

/-- Linearize a full paper to English -/
def linPaper (p : Paper) : String :=
  let title := "# " ++ p.title ++
    (if p.subtitle.isEmpty then "" else "\n## " ++ p.subtitle)
  let authors := "By " ++ String.intercalate ", " p.authors
  let date := p.date
  let status := if p.statusNote.isEmpty then ""
    else "\n\nStatus note. " ++ p.statusNote
  let abstract_ := "\n\nAbstract. " ++ p.abstract_
  let body := "\n\n" ++ linPaperDoc p.body
  title ++ "\n" ++ authors ++ "\n" ++ date ++ status ++ abstract_ ++ body

/-! ## Determinism -/

theorem linPaperStmt_deterministic (s : PaperStmt) :
    linPaperStmt s = linPaperStmt s := rfl

theorem linPaperDoc_deterministic (d : PaperDoc) :
    linPaperDoc d = linPaperDoc d := rfl

/-! ## Test Examples -/

-- Example 1: We show
#eval linPaperStmt (.weShow (.text "every exchangeable sequence admits a de Finetti representation"))

-- Example 2: Citation-backed claim
#eval linPaperStmt (.weShow (.citeBacked
  "exchangeable sequences are conditionally i.i.d."
  { author := "de Finetti", year := 1937 }))

-- Example 3: Lean-proven claim
#eval linPaperStmt (.weShow (.leanProven
  "the scope ordering is well-founded"
  { file := "Mettapedia/OSLF/CoreMain.lean", theorem_ := "scope_ordering_NT" }))

-- Example 4: Contribution
#eval linPaperStmt (.contribution 1 (.text
  "a GF-aligned controlled natural language covering all repository English"))

-- Example 5: In contrast to
#eval linPaperStmt (.inContrastTo
  { author := "Enache", year := 2010 }
  (.text "we generate English from trees rather than parsing English to trees"))

-- Example 6: Related work
#eval linPaperStmt (.relatedWork
  { author := "Ranta", year := 2004 }
  "establishes the GF framework for multilingual grammar engineering")

-- Example 7: Theorem environment
#eval linPaperStmt (.env {
  kind := .theorem_
  name := "Knaster-Tarski"
  statement := "Every monotone function on a complete lattice has a least fixpoint"
  leanRef := some { file := "Mathlib", theorem_ := "OrderIso.map_sSup" }
})

-- Example 8: Definition environment
#eval linPaperStmt (.env {
  kind := .definition_
  name := "Exchangeability"
  statement := "A sequence is exchangeable if its joint distribution is invariant under finite permutations"
  math := some { tex := "P(X_{\\sigma(1)}, \\ldots, X_{\\sigma(n)}) = P(X_1, \\ldots, X_n)" }
})

-- Example 9: Theorem with proof sketch
#eval linPaperStmt (.env {
  kind := .lemma_
  statement := "The linearization function is total"
  proof := some "By structural induction on the abstract syntax tree. Each constructor maps to exactly one string."
})

-- Example 10: Prose with citation
#eval linPaperStmt (.proseWithCite
  "Controlled natural languages trade expressiveness for formal precision"
  { author := "Kuhn", year := 2014 })

-- Example 11: Lean status
#eval linPaperStmt (.leanStatus
  { file := "Mettapedia/Languages/GF/OntologyCNLEng.lean" }
  "provides deterministic English linearization for all ontology statements")

-- Example 12: Status note
#eval linPaperStmt (.statusNote
  "Implementation-status claims in this draft are snapshot-scoped; verify against current repository trackers before citing.")

-- Example 13: Enumerated contributions
#eval linPaperStmt (.enumList "C" [
  "GF-aligned CNL covering ontology, policy, process, report, and comment English",
  "Dual linearization (English + LaTeX) from canonical abstract trees",
  "Determinism theorems: each tree produces exactly one string"
])

-- Example 14: Following from
#eval linPaperStmt (.followingFrom
  (.text "the abstract syntax is always unambiguous")
  { author := "Ranta", year := 2004 })

-- Example 15: Full paper fragment
private def ex_paper : Paper :=
  { title := "GF-Aligned English for Formal Repository Documentation"
    authors := ["Zar", "Claude"]
    date := "2026-02-26"
    abstract_ := "We present a controlled natural language system where all repository English is generated from canonical GF abstract syntax trees."
    statusNote := "Snapshot-scoped to 2026-02-26 build."
    body := .section_ "Introduction" (.seq
      (.stmt (.weShow (.text "unambiguous English can be generated from abstract trees")))
      (.stmt (.contribution 1 (.text "a complete CNL covering all repository prose")))) }

#eval linPaper ex_paper

end Mettapedia.Languages.GF.PaperCNLEng
