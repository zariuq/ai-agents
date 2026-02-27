/-
# Paper CNL — Abstract Syntax

Controlled Natural Language for academic prose: sections, claims,
theorems, proofs, citations, contributions, and status notes.

Phase D of the GF-aligned English plan.

## Design

The same abstract tree linearizes to both:
- **English concrete**: natural academic prose
- **LaTeX concrete**: `\section{}`, `\begin{theorem}`, `\cite{}`, etc.

The tree is canonical; both English and LaTeX are generated views.

## Categories

- `Citation`    — bibliographic reference
- `LeanRef`     — reference to a Lean file/theorem
- `MathExpr`    — inline or display math (opaque LaTeX string)
- `Claim`       — a factual or mathematical claim
- `TheoremEnv`  — theorem/lemma/proposition/definition environment
- `PaperStmt`   — sentence-level paper statement
- `PaperDoc`    — document structure (sections, sequences)
-/

import Mettapedia.Languages.GF.OntologyCNL
import Mettapedia.Languages.GF.CommentCNL

namespace Mettapedia.Languages.GF.PaperCNL

open Mettapedia.Languages.GF.OntologyCNL (SourceLoc)

/-! ## Atomic References -/

/-- Bibliographic citation -/
structure Citation where
  author : String     -- "Solomonoff" or "Bondy and Murty"
  year : Nat          -- 2025
  key : String := ""  -- BibTeX key, empty if not available
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a Lean formalization artifact -/
structure LeanRef where
  file : String          -- "Mettapedia/OSLF/CoreMain.lean"
  theorem_ : String := "" -- "scope_ordering_NT" (empty = whole file)
  deriving DecidableEq, Repr, Inhabited

/-- Inline mathematical expression (opaque string in LaTeX notation) -/
structure MathExpr where
  tex : String  -- e.g., "\\mathbb{P}" or "f : A \\to B"
  deriving DecidableEq, Repr, Inhabited

/-! ## Claims and Environments -/

/-- What kind of theorem-like environment -/
inductive EnvKind where
  | theorem_
  | lemma_
  | proposition
  | corollary
  | definition_
  | remark
  | example_
  | principle
  deriving DecidableEq, Repr, Inhabited

/-- A factual or mathematical claim -/
inductive Claim where
  /-- Plain text claim -/
  | text (s : String)
  /-- Claim with inline math -/
  | withMath (before : String) (m : MathExpr) (after : String)
  /-- Claim referencing a Lean theorem as evidence -/
  | leanProven (statement : String) (ref : LeanRef)
  /-- Claim backed by literature citation -/
  | citeBacked (statement : String) (cite : Citation)
  deriving Repr

/-- A theorem-like environment with optional name and proof -/
structure TheoremEnv where
  kind : EnvKind
  name : String := ""          -- "Knaster-Tarski" or empty
  statement : String           -- the theorem statement text
  math : Option MathExpr := none  -- optional formal statement
  proof : Option String := none   -- optional proof sketch
  leanRef : Option LeanRef := none -- optional Lean cross-reference
  deriving Repr

/-! ## Paper Statements -/

/-- A single statement in academic prose -/
inductive PaperStmt where
  /-- "We show that CLAIM" -/
  | weShow (c : Claim)
  /-- "CLAIM, following from CITE" -/
  | followingFrom (c : Claim) (cite : Citation)
  /-- "In contrast to CITE, CLAIM" -/
  | inContrastTo (cite : Citation) (c : Claim)
  /-- Numbered contribution: "Contribution N: CLAIM" -/
  | contribution (n : Nat) (c : Claim)
  /-- Related work: "CITE establishes/shows/addresses RELATION" -/
  | relatedWork (cite : Citation) (relation : String)
  /-- Theorem/definition/lemma environment -/
  | env (e : TheoremEnv)
  /-- Plain prose paragraph -/
  | prose (text : String)
  /-- Prose with inline citation: "TEXT (CITE)" -/
  | proseWithCite (text : String) (cite : Citation)
  /-- Lean formalization reference: "The Lean formalization at REF..." -/
  | leanStatus (ref : LeanRef) (description : String)
  /-- Status disclaimer (snapshot-scoped) -/
  | statusNote (text : String)
  /-- Enumerated list with label prefix -/
  | enumList (labelPrefix : String) (items : List String)
  /-- Code listing with language and caption -/
  | codeListing (lang : String) (caption : String) (code : String)
  /-- Display math -/
  | displayMath (m : MathExpr)
  /-- Sequencing -/
  | seq (first rest : PaperStmt)

/-! ## Document Structure -/

/-- Paper document tree -/
inductive PaperDoc where
  | stmt (s : PaperStmt)
  | section_ (title : String) (body : PaperDoc)
  | subsection (title : String) (body : PaperDoc)
  | subsubsection (title : String) (body : PaperDoc)
  | seq (first rest : PaperDoc)
  | empty

/-- Build a paper doc from a list -/
def PaperDoc.ofList : List PaperDoc → PaperDoc
  | [] => .empty
  | [d] => d
  | d :: ds => .seq d (ofList ds)

/-! ## Full Paper Structure -/

/-- A complete paper with frontmatter -/
structure Paper where
  title : String
  subtitle : String := ""
  authors : List String
  date : String               -- ISO date
  abstract_ : String
  statusNote : String := ""   -- snapshot-scoped disclaimer
  body : PaperDoc

end Mettapedia.Languages.GF.PaperCNL
