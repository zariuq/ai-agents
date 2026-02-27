/-
# Comment CNL — Abstract Syntax

Controlled Natural Language for code comments, TODO notes, references,
and proof-oriented annotations.

Phase C of the GF-aligned English plan.
-/

import Mettapedia.Languages.GF.OntologyCNL

namespace Mettapedia.Languages.GF.CommentCNL

open Mettapedia.Languages.GF.OntologyCNL (SourceLoc)

/-! ## Core Atoms -/

/-- Why a definition/function exists. -/
inductive Purpose where
  | computes (what : String)
  | proves (what : String)
  | checks (what : String)
  | represents (what : String)
  | normalizes (what : String)
  | guards (what : String)
  | documents (what : String)
  | generic (what : String)
  deriving DecidableEq, Repr, Inhabited

/-- Reference to external or internal artifact. -/
inductive Ref where
  | fileLine (loc : SourceLoc)
  | symbol (name : String)
  | url (u : String)
  | decision (id : String)
  | generic (text : String)
  deriving DecidableEq, Repr, Inhabited

/-- Annotation severity for warnings and TODOs. -/
inductive Severity where
  | low
  | medium
  | high
  deriving DecidableEq, Repr, Inhabited

/-! ## Comment Statements -/

/-- Canonical comment statement constructors. -/
inductive CommentStmt where
  /-- "X computes Y" -/
  | docPurpose (subject : String) (purpose : Purpose)
  /-- "TODO: TEXT" -/
  | todoGap (text : String) (sev : Severity := .medium)
  /-- "FIXME: TEXT" -/
  | fixme (text : String) (sev : Severity := .high)
  /-- "note: TEXT" -/
  | note (text : String)
  /-- "see REF" -/
  | seeRef (r : Ref)
  /-- "CLAIM is proven from REF" -/
  | provenFrom (claim : String) (r : Ref)
  /-- "invariant: TEXT" -/
  | invariant (text : String)
  /-- "precondition: TEXT" -/
  | precondition (text : String)
  /-- "postcondition: TEXT" -/
  | postcondition (text : String)
  /-- "warning: TEXT" -/
  | warning (text : String) (sev : Severity := .medium)
  /-- Positive example for concept usage. -/
  | positiveExample (concept : String) (text : String)
  /-- Negative example for concept usage. -/
  | negativeExample (concept : String) (text : String)
  /-- Sequencing. -/
  | seq (first rest : CommentStmt)
  deriving Repr

/-- Comment document structure. -/
inductive CommentDoc where
  | stmt (s : CommentStmt)
  | section (title : String) (body : CommentDoc)
  | seq (first rest : CommentDoc)
  | empty
  deriving Repr

/-- Build comment doc from list. -/
def CommentDoc.ofList : List CommentDoc → CommentDoc
  | [] => .empty
  | [d] => d
  | d :: ds => .seq d (ofList ds)

end Mettapedia.Languages.GF.CommentCNL
