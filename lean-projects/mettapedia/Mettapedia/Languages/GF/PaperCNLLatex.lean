/-
# Paper CNL — LaTeX Linearization

Deterministic linearization of PaperCNL abstract trees to LaTeX.
Same abstract tree that produces English prose via PaperCNLEng
produces compilable LaTeX via this module.

Phase D of the GF-aligned English plan.
-/

import Mettapedia.Languages.GF.PaperCNL

namespace Mettapedia.Languages.GF.PaperCNLLatex

open Mettapedia.Languages.GF.PaperCNL

/-! ## Atom Linearization -/

private def texCitation (c : Citation) : String :=
  if c.key.isEmpty then
    "\\cite{" ++ c.author ++ toString c.year ++ "}"
  else
    "\\cite{" ++ c.key ++ "}"

private def texLeanRef (r : LeanRef) : String :=
  if r.theorem_.isEmpty then
    "\\texttt{" ++ r.file ++ "}"
  else
    "\\texttt{" ++ r.file ++ ":" ++ r.theorem_ ++ "}"

private def texMathInline (m : MathExpr) : String :=
  "$" ++ m.tex ++ "$"

private def texMathDisplay (m : MathExpr) : String :=
  "\\[\n" ++ m.tex ++ "\n\\]"

private def texEnvName : EnvKind → String
  | .theorem_ => "theorem"
  | .lemma_ => "lemma"
  | .proposition => "proposition"
  | .corollary => "corollary"
  | .definition_ => "definition"
  | .remark => "remark"
  | .example_ => "example"
  | .principle => "principle"

/-! ## Claim Linearization -/

private def texClaim : Claim → String
  | .text s => s
  | .withMath before m after => before ++ texMathInline m ++ after
  | .leanProven stmt ref =>
    stmt ++ " (Lean: " ++ texLeanRef ref ++ ")"
  | .citeBacked stmt cite =>
    stmt ++ " " ++ texCitation cite

/-! ## Environment Linearization -/

private def texTheoremEnv (e : TheoremEnv) : String :=
  let envName := texEnvName e.kind
  let nameOpt := if e.name.isEmpty then "" else "[" ++ e.name ++ "]"
  let stmt := e.statement ++
    (match e.math with
     | some m => "\n" ++ texMathDisplay m
     | none => "")
  let ref := match e.leanRef with
    | some r => "\n\\emph{Lean:} " ++ texLeanRef r
    | none => ""
  let body := "\\begin{" ++ envName ++ "}" ++ nameOpt ++ "\n" ++
    stmt ++ ref ++ "\n\\end{" ++ envName ++ "}"
  let pf := match e.proof with
    | some p => "\n\\begin{proof}\n" ++ p ++ "\n\\end{proof}"
    | none => ""
  body ++ pf

/-! ## Statement Linearization -/

/-- Linearize a paper statement to LaTeX -/
def texPaperStmt : PaperStmt → String
  | .weShow c =>
    "We show that " ++ texClaim c ++ "."
  | .followingFrom c cite =>
    texClaim c ++ ", following from " ++ texCitation cite ++ "."
  | .inContrastTo cite c =>
    "In contrast to " ++ texCitation cite ++ ", " ++ texClaim c ++ "."
  | .contribution n c =>
    "\\textbf{Contribution " ++ toString n ++ ":} " ++ texClaim c ++ "."
  | .relatedWork cite relation =>
    texCitation cite ++ " " ++ relation ++ "."
  | .env e =>
    texTheoremEnv e
  | .prose text => text
  | .proseWithCite text cite =>
    text ++ " " ++ texCitation cite ++ "."
  | .leanStatus ref desc =>
    "The Lean formalization at " ++ texLeanRef ref ++ " " ++ desc ++ "."
  | .statusNote text =>
    "\\paragraph{Status note.} " ++ text
  | .enumList pfx items =>
    let label := "label=\\textbf{" ++ pfx ++ "\\arabic*.}"
    let body := items.map fun item => "\\item " ++ item
    "\\begin{enumerate}[" ++ label ++ "]\n" ++
    String.intercalate "\n" body ++
    "\n\\end{enumerate}"
  | .codeListing lang caption code =>
    "\\begin{lstlisting}[language=" ++ lang ++ ", caption=" ++ caption ++ "]\n" ++
    code ++ "\n\\end{lstlisting}"
  | .displayMath m =>
    texMathDisplay m
  | .seq first rest =>
    texPaperStmt first ++ "\n\n" ++ texPaperStmt rest

/-! ## Document Linearization -/

/-- Linearize a paper document to LaTeX -/
def texPaperDoc : PaperDoc → String
  | .stmt s => texPaperStmt s
  | .section_ title body =>
    "\\section{" ++ title ++ "}\n\n" ++ texPaperDoc body
  | .subsection title body =>
    "\\subsection{" ++ title ++ "}\n\n" ++ texPaperDoc body
  | .subsubsection title body =>
    "\\subsubsection{" ++ title ++ "}\n\n" ++ texPaperDoc body
  | .seq first rest => texPaperDoc first ++ "\n\n" ++ texPaperDoc rest
  | .empty => ""

/-! ## Full Paper Linearization -/

private def texPreamble : String :=
  "\\documentclass[11pt]{article}\n" ++
  "\\usepackage[margin=1in]{geometry}\n" ++
  "\\usepackage{amsmath,amssymb,amsthm}\n" ++
  "\\usepackage{hyperref}\n" ++
  "\\usepackage{enumitem}\n" ++
  "\\usepackage{listings}\n" ++
  "\\newtheorem{theorem}{Theorem}[section]\n" ++
  "\\newtheorem{lemma}[theorem]{Lemma}\n" ++
  "\\newtheorem{proposition}[theorem]{Proposition}\n" ++
  "\\newtheorem{corollary}[theorem]{Corollary}\n" ++
  "\\newtheorem{principle}[theorem]{Principle}\n" ++
  "\\theoremstyle{definition}\n" ++
  "\\newtheorem{definition}[theorem]{Definition}\n" ++
  "\\newtheorem{remark}[theorem]{Remark}\n" ++
  "\\newtheorem{example}[theorem]{Example}\n"

/-- Linearize a full paper to compilable LaTeX -/
def texPaper (p : Paper) : String :=
  let preamble := texPreamble
  let title := "\\title{" ++ p.title ++
    (if p.subtitle.isEmpty then "" else " \\\\ \\large " ++ p.subtitle) ++ "}"
  let authors := "\\author{" ++ String.intercalate " \\and " p.authors ++ "}"
  let date := "\\date{" ++ p.date ++ "}"
  let status := if p.statusNote.isEmpty then ""
    else "\n\n\\paragraph{Status note.} " ++ p.statusNote
  let abstract_ := "\n\n\\begin{abstract}\n" ++ p.abstract_ ++ "\n\\end{abstract}"
  let body := "\n\n" ++ texPaperDoc p.body
  preamble ++ "\n" ++ title ++ "\n" ++ authors ++ "\n" ++ date ++
  "\n\n\\begin{document}\n\\maketitle" ++
  status ++ abstract_ ++
  "\n\\tableofcontents" ++ body ++
  "\n\n\\end{document}\n"

/-! ## Determinism -/

theorem texPaperStmt_deterministic (s : PaperStmt) :
    texPaperStmt s = texPaperStmt s := rfl

theorem texPaperDoc_deterministic (d : PaperDoc) :
    texPaperDoc d = texPaperDoc d := rfl

/-! ## Test Examples -/

-- Example 1: We show (LaTeX)
#eval texPaperStmt (.weShow (.citeBacked
  "exchangeable sequences are conditionally i.i.d."
  { author := "de Finetti", year := 1937, key := "deFinetti1937" }))

-- Example 2: Theorem environment (LaTeX)
#eval texPaperStmt (.env {
  kind := .theorem_
  name := "Knaster-Tarski"
  statement := "Every monotone function on a complete lattice has a least fixpoint."
  math := some { tex := "f : L \\to L \\text{ monotone} \\implies \\exists x, f(x) = x" }
  leanRef := some { file := "Mathlib", theorem_ := "OrderIso.map_sSup" }
})

-- Example 3: Definition with proof
#eval texPaperStmt (.env {
  kind := .definition_
  name := "Exchangeability"
  statement := "A sequence is exchangeable if its joint distribution is invariant under finite permutations."
})

-- Example 4: Contribution (LaTeX)
#eval texPaperStmt (.contribution 1 (.text
  "a GF-aligned controlled natural language covering all repository English"))

-- Example 5: Enumerated list (LaTeX)
#eval texPaperStmt (.enumList "C" [
  "GF-aligned CNL covering ontology, policy, process, report, and comment English",
  "Dual linearization (English + LaTeX) from canonical abstract trees",
  "Determinism theorems: each tree produces exactly one string"
])

-- Example 6: Code listing
#eval texPaperStmt (.codeListing "Lean" "Linearization function" "def linOntStmt : OntStmt → String")

-- Example 7: Status note
#eval texPaperStmt (.statusNote
  "Implementation-status claims in this draft are snapshot-scoped.")

-- Example 8: Display math
#eval texPaperStmt (.displayMath { tex := "P(X_{\\sigma(1)}, \\ldots, X_{\\sigma(n)}) = P(X_1, \\ldots, X_n)" })

-- Example 9: Full paper (LaTeX)
private def ex_paper : Paper :=
  { title := "GF-Aligned English for Formal Repository Documentation"
    authors := ["Zar", "Claude"]
    date := "2026-02-26"
    abstract_ := "We present a controlled natural language system where all repository English is generated from canonical GF abstract syntax trees."
    statusNote := "Snapshot-scoped to 2026-02-26 build."
    body := .section_ "Introduction" (.seq
      (.stmt (.weShow (.text "unambiguous English can be generated from abstract trees")))
      (.stmt (.contribution 1 (.text "a complete CNL covering all repository prose")))) }

#eval texPaper ex_paper

end Mettapedia.Languages.GF.PaperCNLLatex
