/-
# Report CNL — Abstract Syntax

Controlled Natural Language for progress reports, milestone updates,
coverage summaries, blockers, and next-step planning.

Phase C of the GF-aligned English plan.
-/

import Mettapedia.Languages.GF.OntologyCNL

namespace Mettapedia.Languages.GF.ReportCNL

open Mettapedia.Languages.GF.OntologyCNL (SourceLoc)

/-! ## Core Atoms -/

/-- Status labels used in progress reporting. -/
inductive Status where
  | fixed
  | logged
  | autoFixable
  | deferred
  | blocked
  | pending
  | verified
  | green
  | red
  deriving DecidableEq, Repr, Inhabited

/-- A report item: decision, file, module, target, or arbitrary unit. -/
inductive Item where
  | decision (id : String)   -- "D24"
  | module (name : String)   -- "SumoNTT"
  | file (path : String)     -- path reference
  | target (name : String)   -- build target
  | lane (name : String)     -- evidence lane
  | stratum (n : Nat)        -- dependency stratum
  | generic (name : String)
  deriving DecidableEq, Repr, Inhabited

/-- A blocker category for explicit dependency tracking. -/
inductive Blocker where
  | needsReviewQuorum
  | missingEvidence (what : String)
  | buildFailure (target : String)
  | parseCoverage (ok total : Nat)
  | unresolvedDecision (id : String)
  | infraGap (what : String)
  | generic (what : String)
  deriving DecidableEq, Repr, Inhabited

/-- Count tuple for pass/fail/N-A style reporting. -/
structure AuditCount where
  passed : Nat
  failed : Nat
  notApplicable : Nat
  deriving DecidableEq, Repr, Inhabited

/-! ## Statements -/

/-- A single report statement in abstract syntax. -/
inductive ReportStmt where
  /-- "X is STATUS" -/
  | itemIs (item : Item) (status : Status)
  /-- "N remaining for X" -/
  | remaining (count : Nat) (what : String)
  /-- "X is blocked by Y" -/
  | blockedBy (item : Item) (blocker : Blocker)
  /-- "X is completed" -/
  | completed (item : Item)
  /-- "audit: P passed, F failed, N N/A" -/
  | audit (counts : AuditCount)
  /-- "coverage for SCOPE: OK/TOTAL" -/
  | coverage (scope : String) (ok total : Nat)
  /-- "lane L has A atoms across D decisions" -/
  | laneCount (lane : String) (atoms decisions : Nat)
  /-- "top concern: TEXT" -/
  | concern (text : String)
  /-- "next step: TEXT" -/
  | nextStep (text : String)
  /-- explicit source citation for a report claim -/
  | source (loc : SourceLoc) (text : String)
  /-- sequencing -/
  | seq (first rest : ReportStmt)
  deriving Repr

/-- A report document with optional titled sections. -/
inductive ReportDoc where
  | stmt (s : ReportStmt)
  | section (title : String) (body : ReportDoc)
  | seq (first rest : ReportDoc)
  | empty
  deriving Repr

/-- Build a report doc from a list of sections/statements. -/
def ReportDoc.ofList : List ReportDoc → ReportDoc
  | [] => .empty
  | [d] => d
  | d :: ds => .seq d (ofList ds)

end Mettapedia.Languages.GF.ReportCNL
