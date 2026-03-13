import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mettapedia.Logic.GovernanceReasoning.PeTTaRefinement

/-!
# Canonical HE MeTTa Conformance for Governance DTS Rules

Connects the **declarative HE MeTTa specification** (the mutual inductive
relations in `EvalSpec.lean`) to the governance DTS refinement theorems.

## Architecture

The refinement chain has three levels:

1. **Inductive relation** (`MeTTaEval`): proven in `HERefinement.lean`
2. **Answer-level projection** (`HEEvalAnswers`): proven in `LetStarInterface.lean`
3. **Declarative spec** (`EvalAtom`, `MettaCall`): proven HERE via derivation witnesses

## What This Proves

- Pattern ↔ Atom bridge correctness for DTS rules (kernel-checked `rfl`/`simp`)
- DTS rule equation queries have valid `MettaCall` derivations
- Deontic interpretation of results is correct
- End-to-end chain from DTS theorem to HE derivation
-/

namespace Mettapedia.Logic.GovernanceReasoning.HECanonicalConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Logic.GovernanceReasoning.Core
open Mettapedia.Logic.GovernanceReasoning.PeTTaRefinement

/-! ## §1 DTS Rules as HE Equation Atoms -/

/-- OB⇒PE equation: `(= (ct-triple-for-add $e type permitted) (ct-triple $e type obligatory))` -/
def dtsEqAtom_ob_pe : Atom :=
  .expression [.symbol "=",
    .expression [.symbol "ct-triple-for-add", .var "e",
                 .expression [.symbol "type"],
                 .expression [.symbol "permitted"]],
    .expression [.symbol "ct-triple", .var "e",
                 .expression [.symbol "type"],
                 .expression [.symbol "obligatory"]]]

/-- OB(¬p)⇒¬PE(p) equation -/
def dtsEqAtom_ob_neg_not_pe : Atom :=
  .expression [.symbol "=",
    .expression [.symbol "not-ct-triple", .var "e",
                 .expression [.symbol "type"],
                 .expression [.symbol "permitted"]],
    .expression [.symbol "ct-triple", .var "e",
                 .expression [.symbol "type"],
                 .expression [.symbol "obligatory"]]]

/-- ¬OP(p) equation -/
def dtsEqAtom_not_optional : Atom :=
  .expression [.symbol "=",
    .expression [.symbol "not-ct-triple", .var "e",
                 .expression [.symbol "type"],
                 .expression [.symbol "optional"]],
    .expression [.symbol "ct-triple", .var "e",
                 .expression [.symbol "type"],
                 .expression [.symbol "obligatory"]]]

/-- HE space containing all three DTS equation atoms. -/
def dtsHESpace : Space := Space.ofList [
  dtsEqAtom_ob_pe,
  dtsEqAtom_ob_neg_not_pe,
  dtsEqAtom_not_optional
]

/-! ## §2 Pattern ↔ Atom Bridge Correctness -/

theorem bridge_dts_ob_pe_eq :
    dtsEqAtom_ob_pe =
    .expression [.symbol "=",
      patternToAtom dtsRule_ob_implies_pe.left,
      patternToAtom dtsRule_ob_implies_pe.right] := by
  simp [dtsEqAtom_ob_pe, dtsRule_ob_implies_pe, patternToAtom]

theorem bridge_dts_ob_neg_not_pe_eq :
    dtsEqAtom_ob_neg_not_pe =
    .expression [.symbol "=",
      patternToAtom dtsRule_ob_neg_not_pe.left,
      patternToAtom dtsRule_ob_neg_not_pe.right] := by
  simp [dtsRule_ob_neg_not_pe, patternToAtom, dtsEqAtom_ob_neg_not_pe]

theorem bridge_dts_not_optional_eq :
    dtsEqAtom_not_optional =
    .expression [.symbol "=",
      patternToAtom dtsRule_not_optional.left,
      patternToAtom dtsRule_not_optional.right] := by
  simp [dtsRule_not_optional, patternToAtom, dtsEqAtom_not_optional]

/-! ## §3 MettaCall Conformance for DTS Queries

The equation-match constructor of `MettaCall` captures the core DTS
evaluation step: query equations in space, merge bindings, recurse. -/

private def noDispatch : GroundedDispatch := .none
private def emptyB : Bindings := Bindings.empty
private def fuel : Nat := 50

/-- The OB⇒PE equation query succeeds via `MettaCall.equation_match`. -/
theorem mettaCall_ob_pe_soaMoor :
    MettaCall dtsHESpace noDispatch
      (.expression [.symbol "ct-triple-for-add",
                    .expression [.symbol "soaMoor"],
                    .expression [.symbol "type"],
                    .expression [.symbol "permitted"]])
      Atom.undefinedType emptyB
      (.expression [.symbol "ct-triple",
                    .expression [.symbol "soaMoor"],
                    .expression [.symbol "type"],
                    .expression [.symbol "obligatory"]],
       emptyB.assign "e#0" (.expression [.symbol "soaMoor"])) := by
  apply MettaCall.equation_match (fuel := fuel)
    (rhs := .expression [.symbol "ct-triple", .var "e#0",
                          .expression [.symbol "type"],
                          .expression [.symbol "obligatory"]])
    (queryBindings := emptyB.assign "e#0" (.expression [.symbol "soaMoor"]))
    (merged := emptyB.assign "e#0" (.expression [.symbol "soaMoor"]))
  case h_not_error => rfl
  case h_not_grounded => trivial
  case h_query => decide
  case h_merge => decide
  case h_no_loop => rfl
  case h_recurse =>
    apply EvalAtom.type_cast (fuel := fuel)
    · rfl
    · decide
    · right; right; rfl
    · show _ ∈ typeCast _ _ _ _ fuel; decide

/-! ## §4 Deontic Interpretation -/

/-- The result atom decodes back to the expected Pattern. -/
theorem he_result_ob_pe_decode :
    atomToPattern (.expression [.symbol "ct-triple",
                   .expression [.symbol "soaMoor"],
                   .expression [.symbol "type"],
                   .expression [.symbol "obligatory"]]) =
    some (.apply "ct-triple"
      [.apply "soaMoor" [], .apply "type" [], .apply "obligatory" []]) := by
  simp [atomToPattern]

/-- The decoded pattern has the correct deontic interpretation. -/
theorem he_result_ob_pe_interp :
    interpretDeontic (.apply "ct-triple"
      [.apply "soaMoor" [], .apply "type" [], .apply "obligatory" []]) =
    .modalAssertion "soaMoor" .obligatory := by
  simp [interpretDeontic]

/-! ## §5 End-to-End Chain -/

/-- End-to-end: the declarative spec has a valid MettaCall derivation for
    the OB⇒PE rule, the result decodes correctly, and the DTS theorem holds. -/
theorem he_spec_ob_pe_e2e :
    -- Part 1: MettaCall derivation exists
    (∃ b : Bindings, MettaCall dtsHESpace noDispatch
      (.expression [.symbol "ct-triple-for-add",
                    .expression [.symbol "soaMoor"],
                    .expression [.symbol "type"],
                    .expression [.symbol "permitted"]])
      Atom.undefinedType emptyB
      (.expression [.symbol "ct-triple",
                    .expression [.symbol "soaMoor"],
                    .expression [.symbol "type"],
                    .expression [.symbol "obligatory"]], b)) ∧
    -- Part 2: result interprets as obligatory
    (interpretDeontic (.apply "ct-triple"
       [.apply "soaMoor" [], .apply "type" [], .apply "obligatory" []]) =
     .modalAssertion "soaMoor" .obligatory) ∧
    -- Part 3: DTS theorem holds
    (∀ {P : Type*} (d : DTS P) (p : P), d.ob p → d.pe p) := by
  refine ⟨⟨_, mettaCall_ob_pe_soaMoor⟩, ?_, fun d p => d.ob_implies_pe p⟩
  simp [interpretDeontic]

end Mettapedia.Logic.GovernanceReasoning.HECanonicalConformance
