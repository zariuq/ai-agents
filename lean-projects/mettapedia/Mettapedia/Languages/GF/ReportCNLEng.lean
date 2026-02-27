/-
# Report CNL — English Linearization

Deterministic linearization of ReportCNL abstract trees to English.
Each tree produces exactly one string. Covers progress reports,
milestone updates, coverage summaries, blockers, and next-step planning.

Phase C of the GF-aligned English plan.
-/

import Mettapedia.Languages.GF.ReportCNL

namespace Mettapedia.Languages.GF.ReportCNLEng

open Mettapedia.Languages.GF.ReportCNL

/-! ## Atom Linearization -/

private def linStatus : Status → String
  | .fixed => "fixed"
  | .logged => "logged"
  | .autoFixable => "auto-fixable"
  | .deferred => "deferred"
  | .blocked => "blocked"
  | .pending => "pending"
  | .verified => "verified"
  | .green => "green"
  | .red => "red"

private def linItem : Item → String
  | .decision id => id
  | .module name => name
  | .file path => path
  | .target name => name
  | .lane name => "lane " ++ name
  | .stratum n => "stratum " ++ toString n
  | .generic name => name

private def linBlocker : Blocker → String
  | .needsReviewQuorum => "pending review quorum"
  | .missingEvidence what => "missing evidence for " ++ what
  | .buildFailure target => "build failure in " ++ target
  | .parseCoverage ok total =>
    "parse coverage (" ++ toString ok ++ "/" ++ toString total ++ ")"
  | .unresolvedDecision id => "unresolved decision " ++ id
  | .infraGap what => "infrastructure gap: " ++ what
  | .generic what => what

/-! ## Statement Linearization -/

/-- Linearize a report statement to English -/
def linReportStmt : ReportStmt → String
  | .itemIs item status =>
    linItem item ++ " is " ++ linStatus status
  | .remaining count what =>
    toString count ++ " " ++ what ++ " remaining"
  | .blockedBy item blocker =>
    linItem item ++ " is blocked by " ++ linBlocker blocker
  | .completed item =>
    linItem item ++ " is completed"
  | .audit counts =>
    "audit: " ++ toString counts.passed ++ " passed, " ++
    toString counts.failed ++ " failed, " ++
    toString counts.notApplicable ++ " N/A"
  | .coverage scope ok total =>
    "coverage for " ++ scope ++ ": " ++
    toString ok ++ "/" ++ toString total
  | .laneCount lane atoms decisions =>
    "lane " ++ lane ++ " has " ++ toString atoms ++ " atoms across " ++
    toString decisions ++ " decisions"
  | .concern text =>
    "top concern: " ++ text
  | .nextStep text =>
    "next step: " ++ text
  | .source loc text =>
    loc.file ++ ":" ++ toString loc.line ++ " " ++ text
  | .seq first rest =>
    linReportStmt first ++ ". " ++ linReportStmt rest

/-! ## Document Linearization -/

/-- Linearize a report document to English -/
def linReportDoc : ReportDoc → String
  | .stmt s => linReportStmt s
  | .section title body => "## " ++ title ++ "\n" ++ linReportDoc body
  | .seq first rest => linReportDoc first ++ "\n" ++ linReportDoc rest
  | .empty => ""

/-! ## Determinism -/

theorem linReportStmt_deterministic (s : ReportStmt) :
    linReportStmt s = linReportStmt s := rfl

theorem linReportDoc_deterministic (d : ReportDoc) :
    linReportDoc d = linReportDoc d := rfl

/-! ## Test Examples -/

open Mettapedia.Languages.GF.OntologyCNL (SourceLoc)

-- Example 1: Decision status
#eval linReportStmt (.itemIs (.decision "D20") .fixed)
-- "D20 is fixed"

-- Example 2: Module status
#eval linReportStmt (.itemIs (.module "SumoNTT") .green)
-- "SumoNTT is green"

-- Example 3: Remaining count
#eval linReportStmt (.remaining 3 "sorries")
-- "3 sorries remaining"

-- Example 4: Blocked by review
#eval linReportStmt (.blockedBy (.decision "D26") .needsReviewQuorum)
-- "D26 is blocked by pending review quorum"

-- Example 5: Blocked by missing evidence
#eval linReportStmt (.blockedBy (.lane "KIF-parse") (.missingEvidence "stratum 2 axioms"))
-- "lane KIF-parse is blocked by missing evidence for stratum 2 axioms"

-- Example 6: Completed
#eval linReportStmt (.completed (.target "RepairLog"))
-- "RepairLog is completed"

-- Example 7: Audit counts
#eval linReportStmt (.audit ⟨42, 3, 5⟩)
-- "audit: 42 passed, 3 failed, 5 N/A"

-- Example 8: Coverage
#eval linReportStmt (.coverage "KIF axioms" 925 1100)
-- "coverage for KIF axioms: 925/1100"

-- Example 9: Lane count
#eval linReportStmt (.laneCount "doc-parse" 180 26)
-- "lane doc-parse has 180 atoms across 26 decisions"

-- Example 10: Concern
#eval linReportStmt (.concern "stratum 2 parse coverage below 80%")
-- "top concern: stratum 2 parse coverage below 80%"

-- Example 11: Next step
#eval linReportStmt (.nextStep "run GF round-trip on remaining 40 axioms")
-- "next step: run GF round-trip on remaining 40 axioms"

-- Example 12: Source citation
#eval linReportStmt (.source ⟨"Merge.kif", 925⟩ "supports Object hierarchy")
-- "Merge.kif:925 supports Object hierarchy"

-- Example 13: Sequenced report
#eval linReportStmt (.seq
  (.itemIs (.decision "D22") .fixed)
  (.remaining 2 "open decisions"))
-- "D22 is fixed. 2 open decisions remaining"

-- Example 14: Full document
private def ex_report : ReportDoc :=
  .section "SUMO Repair Status" (.seq
    (.stmt (.itemIs (.decision "D20") .fixed))
    (.seq
      (.stmt (.coverage "KIF axioms" 925 1100))
      (.stmt (.nextStep "close stratum 1 parse gaps"))))

#eval linReportDoc ex_report

end Mettapedia.Languages.GF.ReportCNLEng
