/-!
# HE MeTTa Operator Classification

Classifies each HE MeTTa operator into exactly one implementation category.
This determines how each operator flows through the export pipeline
(HELanguageDef → TransitionSpec → RewriteIR → Rust runtime).

## Classification Categories

| Category | Where implemented | Example |
|----------|------------------|---------|
| surfaceSugar | Surface parser lowering only | let, let* |
| preludeEqAndType | Injected equations + type annotation | if |
| mettaCallControl | Explicit MettaCall rewrite rule | case, switch, assert |
| minimalInstruction | OSLF MeTTaMinimalInstance layer | unify, collapse-bind, superpose-bind |
| groundedBuiltin | MC_Grounded dispatch (arithmetic, etc.) | +, -, *, /, <, >, == |

## Design Invariant

Every user-visible MeTTa operator must appear in exactly one category.
The export pipeline must carry all mettaCallControl operators as explicit
rewrite rules in HELanguageDef.lean — they must NOT be handwritten in Rust.

## References

- Interpreter.lean: mettaCall (lines 307-418) — the executable spec
- HELanguageDef.lean: mettaHE.rewrites — the exportable rewrite rules
- MeTTaMinimalInstance.lean — OSLF minimal instruction set
-/

namespace Mettapedia.Languages.MeTTa.HE.OpProfile

/-- Classification of how an HE MeTTa operator is implemented. -/
inductive OpCategory where
  /-- Lowered by the surface parser before encoding (no runtime semantics). -/
  | surfaceSugar
  /-- Equations and type annotation injected into the space at startup. -/
  | preludeEqAndType
  /-- Explicit rewrite rule in MettaCall dispatch (HELanguageDef.lean). -/
  | mettaCallControl
  /-- Implemented via OSLF MeTTaMinimalInstance instruction layer. -/
  | minimalInstruction
  /-- Dispatched via MC_Grounded (executable grounded atoms). -/
  | groundedBuiltin
deriving DecidableEq, Repr

/-- An operator's formal classification entry. -/
structure OpEntry where
  /-- Surface-level operator name as it appears in MeTTa source. -/
  name : String
  /-- Implementation category. -/
  category : OpCategory
  /-- Which Interpreter.lean branch handles this (line reference). -/
  interpreterRef : String
  /-- Which HELanguageDef rule (if any) currently covers this. -/
  languageDefRule : Option String := none
deriving Repr

/-- Complete classification of HE MeTTa Tier 1 operators.

Each entry pins down exactly where the operator's semantics live,
preventing ad-hoc Rust implementations. -/
def tier1Ops : List OpEntry :=
  [ -- Surface sugar: lowered before encoding, no runtime dispatch needed
    { name := "let"
      category := .surfaceSugar
      interpreterRef := "N/A — desugars to (case expr ((pat body)))" }
  , { name := "let*"
      category := .surfaceSugar
      interpreterRef := "N/A — desugars to nested let" }

    -- Prelude: equations + type annotation injected into space
  , { name := "if"
      category := .preludeEqAndType
      interpreterRef := "N/A — handled by (= (if True $then $else) $then) equations"
      languageDefRule := some "MC_Equation (via injected equations)" }

    -- MettaCall control: explicit rewrite rules in HELanguageDef
    -- These correspond to the switch/assert/case branches in Interpreter.lean:342-396
  , { name := "case"
      category := .mettaCallControl
      interpreterRef := "Interpreter.lean:385-396"
      languageDefRule := some "MC_Case (to be added)" }
  , { name := "switch"
      category := .mettaCallControl
      interpreterRef := "Interpreter.lean:342-356"
      languageDefRule := some "MC_Switch (to be added)" }
  , { name := "switch-minimal"
      category := .mettaCallControl
      interpreterRef := "Interpreter.lean:342-356"
      languageDefRule := some "MC_SwitchMinimal (to be added)" }
  , { name := "switch-internal"
      category := .mettaCallControl
      interpreterRef := "Interpreter.lean:357-371"
      languageDefRule := some "MC_SwitchInternal (to be added)" }
  , { name := "assert"
      category := .mettaCallControl
      interpreterRef := "Interpreter.lean:372-384"
      languageDefRule := some "MC_Assert (to be added)" }

    -- Minimal instructions: formal OSLF MeTTaMinimalInstance layer
    -- These use the MeTTaMinimalInstance.lean instruction set
  , { name := "match"
      category := .minimalInstruction
      interpreterRef := "MeTTaMinimalInstance.lean (space query + pattern match)"
      languageDefRule := none }
  , { name := "unify"
      category := .minimalInstruction
      interpreterRef := "MeTTaMinimalInstance.lean:48-49 (Unify instruction)"
      languageDefRule := none }
  , { name := "superpose"
      category := .minimalInstruction
      interpreterRef := "MeTTaMinimalInstance.lean:58-60 (SuperposeBind)"
      languageDefRule := none }
  , { name := "collapse"
      category := .minimalInstruction
      interpreterRef := "MeTTaMinimalInstance.lean:55-57 (CollapseBind)"
      languageDefRule := none }

    -- Grounded builtins: dispatched via MC_Grounded
  , { name := "+"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319 (grounded dispatch)"
      languageDefRule := some "MC_Grounded" }
  , { name := "-"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  , { name := "*"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  , { name := "/"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  , { name := "%"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  , { name := "<"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  , { name := ">"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  , { name := "=="
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  ]

/-- Operators that need new rewrite rules added to HELanguageDef.lean.
These are mettaCallControl ops whose rules are not yet in the export pipeline. -/
def opsNeedingNewRules : List OpEntry :=
  tier1Ops.filter (fun op => op.category == .mettaCallControl)

/-- Operators in the minimal instruction layer (future OSLF integration). -/
def opsMinimalInstruction : List OpEntry :=
  tier1Ops.filter (fun op => op.category == .minimalInstruction)

/-! ## Smoke checks -/

#eval do
  IO.println s!"Tier 1 ops: {tier1Ops.length}"
  IO.println s!"Ops needing new HELanguageDef rules: {opsNeedingNewRules.length}"
  for op in opsNeedingNewRules do
    IO.println s!"  {op.name} ({op.interpreterRef})"
  IO.println s!"Minimal instruction ops: {opsMinimalInstruction.length}"
  for op in opsMinimalInstruction do
    IO.println s!"  {op.name}"

end Mettapedia.Languages.MeTTa.HE.OpProfile
