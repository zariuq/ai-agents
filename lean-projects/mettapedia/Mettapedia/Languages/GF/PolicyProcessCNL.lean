/-
# PolicyProcess CNL — Abstract Syntax

Controlled Natural Language for directives, policies, workflow steps,
and process descriptions. Covers CLAUDE.md-style instructions and
build/verification workflows.

Phase B of the GF-Aligned English plan.

## Design

Two sublanguages sharing common atoms:
- **Policy**: deontic modality (must/must-not/always/never/prefer)
- **Process**: imperative sequences (run/verify/check/sequence)

Both share `Action` and `Condition` atoms.
-/

import Mettapedia.Languages.GF.OntologyCNL

namespace Mettapedia.Languages.GF.PolicyProcessCNL

open OntologyCNL (SourceLoc)

/-! ## Shared Atoms -/

/-- An entity that can be directed (agent, tool, user) -/
inductive Actor where
  | agent       -- "the agent" (default: Claude)
  | user        -- "the user"
  | named (s : String)  -- specific actor by name
  deriving DecidableEq, Repr, Inhabited

/-- An action that can be performed or prohibited -/
inductive Action where
  | use (thing : String)           -- "use X"
  | commit (thing : String)        -- "commit X"
  | create (thing : String)        -- "create X"
  | edit (thing : String)          -- "edit X"
  | delete (thing : String)        -- "delete X"
  | run (cmd : String)             -- "run X"
  | build (target : String)        -- "build X"
  | claim (statement : String)     -- "claim X"
  | report (what : String)         -- "report X"
  | search (where_ : String)       -- "search X"
  | prove (what : String)          -- "prove X"
  | leave (what : String)          -- "leave X"
  | add (what : String)            -- "add X"
  | describe (what : String)       -- "describe X"
  | push (target : String)         -- "push X"
  | ask (what : String)            -- "ask X"
  | verify (what : String)         -- "verify X"
  | generic (verb obj : String)    -- "V X" (fallback)
  deriving DecidableEq, Repr

/-- A condition that can gate a directive -/
inductive Condition where
  | uncertain (about : String)     -- "uncertain about X"
  | blocked (blocker : String)      -- "blocked by X"
  | sorryExists                    -- "sorries exist"
  | buildFails                     -- "the build fails"
  | buildSucceeds                  -- "the build succeeds"
  | fileExists (path : String)     -- "file X exists"
  | stratumOpen (n : Nat)          -- "stratum N is open"
  | reviewPending                  -- "review is pending"
  | quorumReached                  -- "review quorum is reached"
  | hasEvidence (for_ : String)    -- "evidence exists for X"
  | generic (desc : String)        -- fallback
  deriving DecidableEq, Repr

/-! ## Policy Directives -/

/-- A policy directive — the sentence-level category for instructions -/
inductive Directive where
  /-- "the agent must V X" -/
  | must (actor : Actor) (act : Action)
  /-- "the agent must not V X" -/
  | mustNot (actor : Actor) (act : Action)
  /-- "always V X" -/
  | always (act : Action)
  /-- "never V X" -/
  | never (act : Action)
  /-- "prefer V X over V Y" -/
  | preferOver (preferred fallback : Action)
  /-- "before V X, V Y" -/
  | before (first then_ : Action)
  /-- "after V X, V Y" -/
  | after (first then_ : Action)
  /-- "if C then D" -/
  | ifThen (cond : Condition) (dir : Directive)
  /-- "D unless C" -/
  | unless (dir : Directive) (cond : Condition)
  /-- "D and D" -/
  | and_ (left right : Directive)
  /-- "V X only when C" -/
  | onlyWhen (act : Action) (cond : Condition)
  /-- "V X because R" -/
  | because (dir : Directive) (reason : String)
  /-- "D. D." (sequence of directives) -/
  | seq (first rest : Directive)

/-! ## Process Steps -/

/-- A process step — the sentence-level category for workflows -/
inductive Step where
  /-- "run CMD" -/
  | run (cmd : String)
  /-- "verify that C" -/
  | verifyThat (cond : Condition)
  /-- "check the output of CMD for PATTERN" -/
  | checkOutput (cmd : String) (pattern : String)
  /-- "build TARGET" -/
  | buildTarget (target : String)
  /-- "S, then S" -/
  | sequence (first rest : Step)
  /-- "if C then S else S" -/
  | ifThenElse (cond : Condition) (then_ else_ : Step)
  /-- "repeat S until C" -/
  | repeatUntil (body : Step) (cond : Condition)
  /-- "set VAR to VAL" -/
  | setVar (var val : String)
  /-- annotation/comment on a step -/
  | note (text : String) (body : Step)

/-! ## Provenance Metadata -/

/-- Provenance tag for generated English lines -/
structure Provenance where
  sourceTreeId : String     -- hash or identifier of the AST
  grammarVersion : String   -- e.g., "PolicyProcessCNL.v1"
  generatedAt : String      -- ISO timestamp or empty
  deriving DecidableEq, Repr, Inhabited

/-- A directive or step with provenance -/
structure Tagged (α : Type) where
  content : α
  prov : Provenance


/-! ## Document Structure -/

/-- A policy document: interleaved directives and process steps -/
inductive PolicyDoc where
  | directive (d : Directive)
  | step (s : Step)
  | section (title : String) (body : PolicyDoc)
  | seq (first rest : PolicyDoc)
  | empty

def PolicyDoc.ofList : List PolicyDoc → PolicyDoc
  | [] => .empty
  | [d] => d
  | d :: ds => .seq d (ofList ds)

end Mettapedia.Languages.GF.PolicyProcessCNL
