/-
# Comment CNL — English Linearization

Deterministic linearization of CommentCNL abstract trees to English.
Each tree produces exactly one string. Covers code comments, TODO notes,
references, and proof-oriented annotations.

Phase C of the GF-aligned English plan.
-/

import Mettapedia.Languages.GF.CommentCNL

namespace Mettapedia.Languages.GF.CommentCNLEng

open Mettapedia.Languages.GF.CommentCNL
open Mettapedia.Languages.GF.OntologyCNL (SourceLoc)

/-! ## Atom Linearization -/

private def linPurpose : Purpose → String
  | .computes what => "computes " ++ what
  | .proves what => "proves " ++ what
  | .checks what => "checks " ++ what
  | .represents what => "represents " ++ what
  | .normalizes what => "normalizes " ++ what
  | .guards what => "guards " ++ what
  | .documents what => "documents " ++ what
  | .generic what => what

private def linRef : Ref → String
  | .fileLine loc => loc.file ++ ":" ++ toString loc.line
  | .symbol name => "`" ++ name ++ "`"
  | .url u => u
  | .decision id => "decision " ++ id
  | .generic text => text

private def linSeverity : Severity → String
  | .low => "low"
  | .medium => "medium"
  | .high => "high"

/-! ## Statement Linearization -/

/-- Linearize a comment statement to English -/
def linCommentStmt : CommentStmt → String
  | .docPurpose subject purpose =>
    subject ++ " " ++ linPurpose purpose
  | .todoGap text _sev =>
    "TODO: " ++ text
  | .fixme text _sev =>
    "FIXME: " ++ text
  | .note text =>
    "note: " ++ text
  | .seeRef r =>
    "see " ++ linRef r
  | .provenFrom claim r =>
    claim ++ " is proven from " ++ linRef r
  | .invariant text =>
    "invariant: " ++ text
  | .precondition text =>
    "precondition: " ++ text
  | .postcondition text =>
    "postcondition: " ++ text
  | .warning text _sev =>
    "warning: " ++ text
  | .positiveExample concept text =>
    "example (" ++ concept ++ "): " ++ text
  | .negativeExample concept text =>
    "counter-example (" ++ concept ++ "): " ++ text
  | .seq first rest =>
    linCommentStmt first ++ ". " ++ linCommentStmt rest

/-! ## Document Linearization -/

/-- Linearize a comment document to English -/
def linCommentDoc : CommentDoc → String
  | .stmt s => linCommentStmt s
  | .section title body => "-- " ++ title ++ "\n" ++ linCommentDoc body
  | .seq first rest => linCommentDoc first ++ "\n" ++ linCommentDoc rest
  | .empty => ""

/-! ## Determinism -/

theorem linCommentStmt_deterministic (s : CommentStmt) :
    linCommentStmt s = linCommentStmt s := rfl

theorem linCommentDoc_deterministic (d : CommentDoc) :
    linCommentDoc d = linCommentDoc d := rfl

/-! ## Test Examples -/

-- Example 1: Doc purpose — computes
#eval linCommentStmt (.docPurpose "T_P" (.computes "the immediate consequence operator"))
-- "T_P computes the immediate consequence operator"

-- Example 2: Doc purpose — proves
#eval linCommentStmt (.docPurpose "monotone_T_P" (.proves "monotonicity of T_P"))
-- "monotone_T_P proves monotonicity of T_P"

-- Example 3: TODO
#eval linCommentStmt (.todoGap "monotonicity proof for stratified negation")
-- "TODO: monotonicity proof for stratified negation"

-- Example 4: FIXME
#eval linCommentStmt (.fixme "universe level mismatch in Category instance")
-- "FIXME: universe level mismatch in Category instance"

-- Example 5: Note
#eval linCommentStmt (.note "this uses classical logic via Decidable instance")
-- "note: this uses classical logic via Decidable instance"

-- Example 6: See reference — file
#eval linCommentStmt (.seeRef (.fileLine ⟨"Core.lean", 42⟩))
-- "see Core.lean:42"

-- Example 7: See reference — symbol
#eval linCommentStmt (.seeRef (.symbol "MeasureTheory.Measure.map"))
-- "see `MeasureTheory.Measure.map`"

-- Example 8: See reference — URL
#eval linCommentStmt (.seeRef (.url "https://leanprover-community.github.io"))
-- "see https://leanprover-community.github.io"

-- Example 9: Proven from
#eval linCommentStmt (.provenFrom "Knaster-Tarski fixpoint" (.symbol "OrderIso.map_sSup"))
-- "Knaster-Tarski fixpoint is proven from `OrderIso.map_sSup`"

-- Example 10: Invariant
#eval linCommentStmt (.invariant "hash set count equals list length")
-- "invariant: hash set count equals list length"

-- Example 11: Pre/postcondition
#eval linCommentStmt (.precondition "input list is sorted")
-- "precondition: input list is sorted"

#eval linCommentStmt (.postcondition "output is a valid parse tree")
-- "postcondition: output is a valid parse tree"

-- Example 12: Warning
#eval linCommentStmt (.warning "this tactic may timeout on large goals")
-- "warning: this tactic may timeout on large goals"

-- Example 13: Positive example
#eval linCommentStmt (.positiveExample "subclass" "Pain is a subclass of StateOfMind")
-- "example (subclass): Pain is a subclass of StateOfMind"

-- Example 14: Negative example
#eval linCommentStmt (.negativeExample "subclass" "Object is not a subclass of Process")
-- "counter-example (subclass): Object is not a subclass of Process"

-- Example 15: Decision reference
#eval linCommentStmt (.seeRef (.decision "D24"))
-- "see decision D24"

-- Example 16: Sequenced comments
#eval linCommentStmt (.seq
  (.docPurpose "linOntStmt" (.computes "English for ontology statements"))
  (.seeRef (.fileLine ⟨"OntologyCNLEng.lean", 15⟩)))
-- "linOntStmt computes English for ontology statements. see OntologyCNLEng.lean:15"

-- Example 17: Full comment document
private def ex_comment_doc : CommentDoc :=
  .section "Module Purpose" (.seq
    (.stmt (.docPurpose "ReportCNLEng" (.computes "English for progress reports")))
    (.stmt (.seeRef (.symbol "ReportCNL.ReportStmt"))))

#eval linCommentDoc ex_comment_doc

end Mettapedia.Languages.GF.CommentCNLEng
