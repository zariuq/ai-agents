/-
# PolicyProcess CNL — English Linearization

Deterministic linearization of PolicyProcessCNL abstract trees to English.
Each tree produces exactly one string. Covers CLAUDE.md-style directives
and build/verification workflow steps.

Phase B of the GF-Aligned English plan.
-/

import Mettapedia.Languages.GF.PolicyProcessCNL

namespace Mettapedia.Languages.GF.PolicyProcessCNLEng

open Mettapedia.Languages.GF.PolicyProcessCNL

/-! ## Atom Linearization -/

private def linActor : Actor → String
  | .agent => "the agent"
  | .user => "the user"
  | .named s => s

private def linAction : Action → String
  | .use s => "use " ++ s
  | .commit s => "commit " ++ s
  | .create s => "create " ++ s
  | .edit s => "edit " ++ s
  | .delete s => "delete " ++ s
  | .run s => "run " ++ s
  | .build s => "build " ++ s
  | .claim s => "claim " ++ s
  | .report s => "report " ++ s
  | .search s => "search " ++ s
  | .prove s => "prove " ++ s
  | .leave s => "leave " ++ s
  | .add s => "add " ++ s
  | .describe s => "describe " ++ s
  | .push s => "push " ++ s
  | .ask s => "ask " ++ s
  | .verify s => "verify " ++ s
  | .generic v o => v ++ " " ++ o

private def linCondition : Condition → String
  | .uncertain about => "uncertain about " ++ about
  | .blocked blocker => "blocked by " ++ blocker
  | .sorryExists => "sorries exist"
  | .buildFails => "the build fails"
  | .buildSucceeds => "the build succeeds"
  | .fileExists path => path ++ " exists"
  | .stratumOpen n => "stratum " ++ toString n ++ " is open"
  | .reviewPending => "review is pending"
  | .quorumReached => "review quorum is reached"
  | .hasEvidence for_ => "evidence exists for " ++ for_
  | .generic desc => desc

/-! ## Directive Linearization -/

/-- Linearize a policy directive to English -/
def linDirective : Directive → String
  | .must actor act =>
    linActor actor ++ " must " ++ linAction act
  | .mustNot actor act =>
    linActor actor ++ " must not " ++ linAction act
  | .always act =>
    "always " ++ linAction act
  | .never act =>
    "never " ++ linAction act
  | .preferOver preferred fallback =>
    "prefer to " ++ linAction preferred ++ " over " ++ linAction fallback
  | .before first then_ =>
    "before " ++ linAction then_ ++ ", " ++ linAction first
  | .after first then_ =>
    "after " ++ linAction first ++ ", " ++ linAction then_
  | .ifThen cond dir =>
    "if " ++ linCondition cond ++ " then " ++ linDirective dir
  | .unless dir cond =>
    linDirective dir ++ " unless " ++ linCondition cond
  | .and_ left right =>
    linDirective left ++ " and " ++ linDirective right
  | .onlyWhen act cond =>
    linAction act ++ " only when " ++ linCondition cond
  | .because dir reason =>
    linDirective dir ++ " because " ++ reason
  | .seq first rest =>
    linDirective first ++ ". " ++ linDirective rest

/-! ## Step Linearization -/

/-- Linearize a process step to English -/
def linStep : Step → String
  | .run cmd =>
    "run " ++ cmd
  | .verifyThat cond =>
    "verify that " ++ linCondition cond
  | .checkOutput cmd pattern =>
    "check the output of " ++ cmd ++ " for " ++ pattern
  | .buildTarget target =>
    "build " ++ target
  | .sequence first rest =>
    linStep first ++ ", then " ++ linStep rest
  | .ifThenElse cond then_ else_ =>
    "if " ++ linCondition cond ++ " then " ++ linStep then_ ++ " else " ++ linStep else_
  | .repeatUntil body cond =>
    "repeat: " ++ linStep body ++ " until " ++ linCondition cond
  | .setVar var val =>
    "set " ++ var ++ " to " ++ val
  | .note text body =>
    linStep body ++ " (" ++ text ++ ")"

/-! ## Document Linearization -/

/-- Linearize a policy document to English -/
def linPolicyDoc : PolicyDoc → String
  | .directive d => linDirective d
  | .step s => linStep s
  | .section title body => "## " ++ title ++ "\n" ++ linPolicyDoc body
  | .seq first rest => linPolicyDoc first ++ "\n" ++ linPolicyDoc rest
  | .empty => ""

/-! ## Provenance Linearization -/

/-- Append provenance comment to generated English -/
def withProvenance (text : String) (prov : Provenance) : String :=
  text ++ "  <!-- tree:" ++ prov.sourceTreeId ++
  " grammar:" ++ prov.grammarVersion ++ " -->"

/-! ## Determinism -/

theorem linDirective_deterministic (d : Directive) :
    linDirective d = linDirective d := rfl

theorem linStep_deterministic (s : Step) :
    linStep s = linStep s := rfl

/-! ## Test Examples — Policy Directives -/

-- Example 1: Simple prohibition
private def ex_never_sorry : Directive :=
  .never (.use "sorry")

#eval linDirective ex_never_sorry
-- "never use sorry"

-- Example 2: Must with actor
private def ex_must_prove : Directive :=
  .must .agent (.prove "every provable theorem")

#eval linDirective ex_must_prove
-- "the agent must prove every provable theorem"

-- Example 3: Preference
private def ex_prefer_edit : Directive :=
  .preferOver (.edit "existing files") (.create "new files")

#eval linDirective ex_prefer_edit
-- "prefer to edit existing files over create new files"

-- Example 4: Conditional directive
private def ex_if_uncertain : Directive :=
  .ifThen (.uncertain "project-specific details")
    (.must .agent (.search "the codebase and literature"))

#eval linDirective ex_if_uncertain
-- "if uncertain about project-specific details then the agent must search the codebase and literature"

-- Example 5: Before ordering
private def ex_before_build : Directive :=
  .before (.run "the build") (.edit "code")

#eval linDirective ex_before_build
-- "before edit code, run the build"

-- Example 6: Never with reason
private def ex_never_claim : Directive :=
  .because (.never (.claim "work is complete when sorries exist"))
    "sorries are not proofs"

#eval linDirective ex_never_claim
-- "never claim work is complete when sorries exist because sorries are not proofs"

-- Example 7: Stratum gate
private def ex_stratum_gate : Directive :=
  .ifThen (.stratumOpen 1)
    (.mustNot .agent (.generic "work on" "stratum 2"))

#eval linDirective ex_stratum_gate
-- "if stratum 1 is open then the agent must not work on stratum 2"

-- Example 8: Unless
private def ex_unless_review : Directive :=
  .unless
    (.mustNot .agent (.edit "ontology content"))
    (.quorumReached)

#eval linDirective ex_unless_review
-- "the agent must not edit ontology content unless review quorum is reached"

-- Example 9: Only when
private def ex_only_when : Directive :=
  .onlyWhen (.commit "ontology repairs") (.quorumReached)

#eval linDirective ex_only_when
-- "commit ontology repairs only when review quorum is reached"

-- Example 10: Compound
private def ex_compound : Directive :=
  .and_
    (.always (.run "the build after editing"))
    (.always (.verify "zero errors"))

#eval linDirective ex_compound
-- "always run the build after editing and always verify zero errors"

/-! ## Test Examples — Process Steps -/

-- Example 11: Simple run
private def ex_run_build : Step :=
  .run "lake build"

#eval linStep ex_run_build
-- "run lake build"

-- Example 12: Sequence
private def ex_build_verify : Step :=
  .sequence
    (.buildTarget "RepairLog")
    (.verifyThat .buildSucceeds)

#eval linStep ex_build_verify
-- "build RepairLog, then verify that the build succeeds"

-- Example 13: Set + run
private def ex_set_run : Step :=
  .sequence
    (.setVar "LAKE_JOBS" "3")
    (.run "nice -n 19 lake build")

#eval linStep ex_set_run
-- "set LAKE_JOBS to 3, then run nice -n 19 lake build"

-- Example 14: Check output
private def ex_check : Step :=
  .checkOutput "lake build" "zero errors"

#eval linStep ex_check
-- "check the output of lake build for zero errors"

-- Example 15: Conditional step
private def ex_cond_step : Step :=
  .ifThenElse .buildFails
    (.run "lake exe cache get")
    (.verifyThat .buildSucceeds)

#eval linStep ex_cond_step
-- "if the build fails then run lake exe cache get else verify that the build succeeds"

-- Example 16: Repeat until
private def ex_repeat : Step :=
  .repeatUntil
    (.sequence (.run "fix errors") (.buildTarget "target"))
    (.buildSucceeds)

#eval linStep ex_repeat
-- "repeat: run fix errors, then build target until the build succeeds"

-- Example 17: Step with note
private def ex_noted : Step :=
  .note "prevents mathlib rebuild"
    (.run "lake exe cache get")

#eval linStep ex_noted
-- "run lake exe cache get (prevents mathlib rebuild)"

-- Example 18: Provenance tag
#eval withProvenance
  (linDirective (.never (.use "sorry")))
  { sourceTreeId := "abc123", grammarVersion := "PolicyProcessCNL.v1", generatedAt := "" }
-- "never use sorry  <!-- tree:abc123 grammar:PolicyProcessCNL.v1 -->"

/-! ## Test Examples — Document -/

-- Example 19: Policy document section
private def ex_doc : PolicyDoc :=
  .section "Build Rules" (.seq
    (.directive (.always (.run "the build after editing")))
    (.seq
      (.directive (.never (.leave "sorry in final code")))
      (.step (.sequence
        (.setVar "LAKE_JOBS" "3")
        (.run "nice -n 19 lake build")))))

#eval linPolicyDoc ex_doc

end Mettapedia.Languages.GF.PolicyProcessCNLEng
