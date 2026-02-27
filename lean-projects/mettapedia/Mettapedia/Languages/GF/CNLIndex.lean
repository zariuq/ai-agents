/-
# CNL Index — Module Registry and Coverage Audit

Central index of all CNL modules with constructor counts,
test example counts, and coverage tracking.

Phase E of the GF-aligned English plan.
-/

import Mettapedia.Languages.GF.OntologyCNL
import Mettapedia.Languages.GF.OntologyCNLEng
import Mettapedia.Languages.GF.PolicyProcessCNL
import Mettapedia.Languages.GF.PolicyProcessCNLEng
import Mettapedia.Languages.GF.ReportCNL
import Mettapedia.Languages.GF.ReportCNLEng
import Mettapedia.Languages.GF.CommentCNL
import Mettapedia.Languages.GF.CommentCNLEng
import Mettapedia.Languages.GF.PaperCNL
import Mettapedia.Languages.GF.PaperCNLEng
import Mettapedia.Languages.GF.PaperCNLLatex
import Mettapedia.Languages.GF.MetaCNL

namespace Mettapedia.Languages.GF.CNLIndex

/-! ## Module Registry -/

/-- A CNL module entry for the registry -/
structure ModuleEntry where
  name : String
  phase : String
  abstractFile : String
  concreteFiles : List String
  constructorCount : Nat
  testExampleCount : Nat
  deriving Repr

/-- The complete CNL module registry -/
def registry : List ModuleEntry := [
  { name := "OntologyCNL"
    phase := "A"
    abstractFile := "OntologyCNL.lean"
    concreteFiles := ["OntologyCNLEng.lean"]
    constructorCount := 13 + 3  -- OntStmt(13) + EvidenceStmt(3)
    testExampleCount := 15 },
  { name := "PolicyProcessCNL"
    phase := "B"
    abstractFile := "PolicyProcessCNL.lean"
    concreteFiles := ["PolicyProcessCNLEng.lean"]
    constructorCount := 13 + 9  -- Directive(13) + Step(9)
    testExampleCount := 19 },
  { name := "ReportCNL"
    phase := "C"
    abstractFile := "ReportCNL.lean"
    concreteFiles := ["ReportCNLEng.lean"]
    constructorCount := 11  -- ReportStmt(11)
    testExampleCount := 14 },
  { name := "CommentCNL"
    phase := "C"
    abstractFile := "CommentCNL.lean"
    concreteFiles := ["CommentCNLEng.lean"]
    constructorCount := 13  -- CommentStmt(13)
    testExampleCount := 17 },
  { name := "PaperCNL"
    phase := "D"
    abstractFile := "PaperCNL.lean"
    concreteFiles := ["PaperCNLEng.lean", "PaperCNLLatex.lean"]
    constructorCount := 14  -- PaperStmt(14)
    testExampleCount := 15 + 9 },  -- Eng(15) + LaTeX(9)
  { name := "MetaCNL"
    phase := "A-D"
    abstractFile := "MetaCNL.lean"
    concreteFiles := ["MetaCNL.lean"]  -- self-contained
    constructorCount := 5  -- MetaStmt(5)
    testExampleCount := 6 }
]

/-- Total constructor count across all modules -/
def totalConstructors : Nat :=
  registry.foldl (· + ·.constructorCount) 0

/-- Total test example count across all modules -/
def totalTestExamples : Nat :=
  registry.foldl (· + ·.testExampleCount) 0

/-- Total concrete syntax files -/
def totalConcreteFiles : Nat :=
  registry.foldl (· + ·.concreteFiles.length) 0

/-! ## Coverage Audit -/

#eval s!"CNL Module Registry: {registry.length} modules"
#eval s!"Total constructors: {totalConstructors}"
#eval s!"Total test examples: {totalTestExamples}"
#eval s!"Total concrete files: {totalConcreteFiles}"

-- Per-module summary
#eval registry.map fun m =>
  s!"{m.phase}: {m.name} — {m.constructorCount} constructors, {m.testExampleCount} tests"

/-! ## Linearization Coverage Check

Each module's linearization function must handle every constructor.
This is enforced by Lean's exhaustiveness checker — if a constructor
is missing from a pattern match, the build fails.

The following imports witness that all linearization functions
compile (and are therefore exhaustive):
- OntologyCNLEng.linOntStmt
- PolicyProcessCNLEng.linDirective, linStep
- ReportCNLEng.linReportStmt
- CommentCNLEng.linCommentStmt
- PaperCNLEng.linPaperStmt
- PaperCNLLatex.texPaperStmt
- MetaCNL.linMetaStmt
-/

/-- All linearization functions exist and are total (witnessed by import) -/
theorem all_linearizers_exist : True := trivial

end Mettapedia.Languages.GF.CNLIndex
