import Mettapedia.Languages.Metamath.MMLean4Bridge
import Mettapedia.Languages.Metamath.GroundedSemantics
import Mettapedia.Languages.Metamath.Simulation
import Mettapedia.Languages.Metamath.Fixtures

/-!
# Metamath Acceptance Equivalence Scaffold

This module exposes local aliases for implementation acceptance and
spec provability, then reuses `mm-lean4`'s proved biconditional directly.
-/

namespace Mettapedia.Languages.Metamath.AcceptanceEquivalence

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.GroundedSemantics
open Mettapedia.Languages.Metamath.Simulation
open Mettapedia.Languages.Metamath.Fixtures

/-- Implementation acceptance predicate (parser/checker side). -/
def ImplAccepts (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) : Prop :=
  ∃ (proof : Array String) (prFinal : Metamath.Verify.ProofState) (f' : Metamath.Verify.Formula),
    proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
      ⟨⟨0, 0⟩, label, f, (checkBytesDB bytes).frame, #[], #[], Metamath.Verify.ProofTokenParser.normal⟩ =
        Except.ok prFinal ∧
      prFinal.stack.size = 1 ∧
      prFinal.stack[0]? = some f' ∧
      Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f

/-- Spec acceptance predicate (declarative side). -/
def SpecAccepts (bytes : ByteArray) (f : Metamath.Verify.Formula) : Prop :=
  ∃ (Γ : Metamath.Spec.Database) (fr : Metamath.Spec.Frame),
    Metamath.Kernel.toDatabase (checkBytesDB bytes) = some Γ ∧
      Metamath.Kernel.toFrame (checkBytesDB bytes) (checkBytesDB bytes).frame = some fr ∧
      Metamath.Spec.Provable Γ fr (Metamath.Kernel.toExpr f)

theorem implAccepts_iff_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none) :
    ImplAccepts bytes label f ↔ SpecAccepts bytes f := by
  simpa [ImplAccepts, SpecAccepts, checkBytesDB] using
    parserAcceptance_iff_specProvable bytes label f hSuccess

/-- Initial runtime proof state used by checker acceptance witnesses. -/
def initialProofState
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) :
    Metamath.Verify.ProofState :=
  ⟨⟨0, 0⟩, label, f, (checkBytesDB bytes).frame, #[], #[], Metamath.Verify.ProofTokenParser.normal⟩

/-- Runtime provenance for proof tokens:
the token resolves to a hypothesis/assertion object in the checker DB. -/
def RuntimeLabelProvenance (db : RuntimeDB) (step : String) : Prop :=
  ∃ obj, db.find? step = some obj ∧
    match obj with
    | .hyp _ _ _ => True
    | .assert _ _ _ => True
    | _ => False

theorem runtimeLabelProvenance_of_stepNormal_ok
    {db : RuntimeDB} {pr pr' : RuntimeProofState} {step : String}
    (hStep : Metamath.Verify.DB.stepNormal db pr step = Except.ok pr') :
    RuntimeLabelProvenance db step := by
  unfold RuntimeLabelProvenance
  unfold Metamath.Verify.DB.stepNormal at hStep
  cases hFind : db.find? step with
  | none =>
      simp [hFind] at hStep
  | some obj =>
      cases obj with
      | const c =>
          simp [hFind] at hStep
      | var v =>
          simp [hFind] at hStep
      | hyp ess f nm =>
          exact ⟨Metamath.Verify.Object.hyp ess f nm, rfl, trivial⟩
      | assert f fr nm =>
          exact ⟨Metamath.Verify.Object.assert f fr nm, rfl, trivial⟩

private theorem traceLabelsAuthored_list_of_fold_ok
    (db : RuntimeDB) (steps : List String)
    (pr0 prFinal : RuntimeProofState)
    (hFold :
      steps.foldlM (fun pr step => Metamath.Verify.DB.stepNormal db pr step) pr0 =
        Except.ok prFinal) :
    ∀ step ∈ steps, RuntimeLabelProvenance db step := by
  induction steps generalizing pr0 prFinal with
  | nil =>
      intro step hMem
      cases hMem
  | cons hd tl ih =>
      simp [List.foldlM_cons, Bind.bind, Except.bind] at hFold
      cases hHead : Metamath.Verify.DB.stepNormal db pr0 hd with
      | error e =>
          simp [hHead] at hFold
      | ok pr1 =>
          rw [hHead] at hFold
          intro step hMem
          simp at hMem
          rcases hMem with rfl | hTailMem
          · exact runtimeLabelProvenance_of_stepNormal_ok hHead
          · exact ih pr1 prFinal hFold step hTailMem

/-- Authored-trace side condition sourced from runtime checker provenance:
every trace token resolves to a hypothesis/assertion object in the checker DB. -/
def TraceLabelsAuthored (bytes : ByteArray) (proof : Array String) : Prop :=
  ∀ step ∈ proof.toList, RuntimeLabelProvenance (checkBytesDB bytes) step

theorem traceLabelsAuthored_of_fold_ok
    (bytes : ByteArray) (proof : Array String)
    (pr0 prFinal : RuntimeProofState)
    (hFold :
      proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step) pr0 =
        Except.ok prFinal) :
    TraceLabelsAuthored bytes proof := by
  intro step hMem
  have hList := hFold
  rw [← Array.foldlM_toList] at hList
  exact traceLabelsAuthored_list_of_fold_ok (checkBytesDB bytes) proof.toList pr0 prFinal hList step hMem

/-- LanguageDef-side acceptance witness:
an implementation acceptance witness whose trace tokens are all authored rewrite
labels in the Lean `metamathCore` LanguageDef. -/
def LanguageDefTraceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) : Prop :=
  ∃ (proof : Array String) (prFinal : Metamath.Verify.ProofState) (f' : Metamath.Verify.Formula),
    (checkBytesDB bytes).error? = none ∧
      TraceLabelsAuthored bytes proof ∧
      proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
        (initialProofState bytes label f) =
          Except.ok prFinal ∧
      prFinal.stack.size = 1 ∧
      prFinal.stack[0]? = some f' ∧
      Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f

/-- Authored-trace completeness invariant sourced directly from runtime
provenance of successful checker execution traces. -/
theorem authoredTraceCompleteness_from_runtime
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) :
    ∀ proof prFinal f',
      proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
        (initialProofState bytes label f) = Except.ok prFinal →
      prFinal.stack.size = 1 →
      prFinal.stack[0]? = some f' →
      Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f →
      TraceLabelsAuthored bytes proof := by
  intro proof prFinal f' hFold _hSize _hTop _hExpr
  exact traceLabelsAuthored_of_fold_ok
    bytes proof (initialProofState bytes label f) prFinal hFold

/-- Forward simulation: any LanguageDef-trace acceptance witness implies
spec acceptance. -/
theorem languageDefTraceWitness_to_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : LanguageDefTraceWitness bytes label f) :
    SpecAccepts bytes f := by
  rcases hTrace with ⟨proof, prFinal, f', hSuccess, _hAuthored, hFold, hSize, hTop, hExpr⟩
  have hImpl : ImplAccepts bytes label f := ⟨proof, prFinal, f', hFold, hSize, hTop, hExpr⟩
  exact (implAccepts_iff_specAccepts bytes label f hSuccess).1 hImpl

/-- Backward simulation: spec acceptance yields a LanguageDef-trace acceptance
witness with authored-trace completeness discharged from runtime provenance. -/
theorem specAccepts_to_languageDefTraceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none)
    (hSpec : SpecAccepts bytes f) :
    LanguageDefTraceWitness bytes label f := by
  have hImpl : ImplAccepts bytes label f :=
    (implAccepts_iff_specAccepts bytes label f hSuccess).2 hSpec
  rcases hImpl with ⟨proof, prFinal, f', hFold, hSize, hTop, hExpr⟩
  have hAuthored :
      TraceLabelsAuthored bytes proof :=
    authoredTraceCompleteness_from_runtime bytes label f
      proof prFinal f' hFold hSize hTop hExpr
  exact ⟨proof, prFinal, f', hSuccess, hAuthored,
    hFold, hSize, hTop, hExpr⟩

/-- Composed bisimulation-facing scaffold theorem.
Both directions are now direct (no extra completeness hypothesis), because
trace authorship is discharged from runtime provenance. -/
theorem languageDefTraceWitness_iff_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hSuccess : (checkBytesDB bytes).error? = none) :
    LanguageDefTraceWitness bytes label f ↔ SpecAccepts bytes f := by
  constructor
  · intro hTrace
    exact languageDefTraceWitness_to_specAccepts bytes label f hTrace
  · intro hSpec
    exact specAccepts_to_languageDefTraceWitness bytes label f hSuccess hSpec

/-- Engine-facing trace compatibility: each token has an engine-labeled
top-level rewrite witness (Simulation layer, line 202 boundary). -/
def EngineTokenLift (step : String) : Prop :=
  ∃ p q, EngineLabeledTopStep p q step

def EngineTraceCompatible (proof : Array String) : Prop :=
  ∀ step ∈ proof.toList, EngineTokenLift step

/-- Stronger witness that carries both runtime provenance and engine-layer
token witnesses, so the trace is not wrapper-only. -/
def EngineBackedTraceWitness
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula) : Prop :=
  ∃ (proof : Array String) (prFinal : Metamath.Verify.ProofState) (f' : Metamath.Verify.Formula),
    (checkBytesDB bytes).error? = none ∧
      TraceLabelsAuthored bytes proof ∧
      EngineTraceCompatible proof ∧
      proof.foldlM (fun pr step => Metamath.Verify.DB.stepNormal (checkBytesDB bytes) pr step)
        (initialProofState bytes label f) =
          Except.ok prFinal ∧
      prFinal.stack.size = 1 ∧
      prFinal.stack[0]? = some f' ∧
      Metamath.Kernel.toExpr f' = Metamath.Kernel.toExpr f

theorem engineBackedTraceWitness_to_specAccepts
    (bytes : ByteArray) (label : String) (f : Metamath.Verify.Formula)
    (hTrace : EngineBackedTraceWitness bytes label f) :
    SpecAccepts bytes f := by
  rcases hTrace with
    ⟨proof, prFinal, f', hNoErr, hAuthored, _hEngine, hFold, hSize, hTop, hExpr⟩
  exact languageDefTraceWitness_to_specAccepts
    bytes label f ⟨proof, prFinal, f', hNoErr, hAuthored, hFold, hSize, hTop, hExpr⟩

/-- Fixture parity (forward): empty database fixture. -/
theorem emptyBytes_languageDefTraceWitness_to_specAccepts
    (label : String) (f : Metamath.Verify.Formula)
    (hTrace : LanguageDefTraceWitness emptyBytes label f) :
    SpecAccepts emptyBytes f := by
  exact languageDefTraceWitness_to_specAccepts emptyBytes label f hTrace

/-- Fixture parity (forward): minimal axiom database fixture. -/
theorem minimalAxiomBytes_languageDefTraceWitness_to_specAccepts
    (label : String) (f : Metamath.Verify.Formula)
    (hTrace : LanguageDefTraceWitness minimalAxiomBytes label f) :
    SpecAccepts minimalAxiomBytes f := by
  exact languageDefTraceWitness_to_specAccepts minimalAxiomBytes label f hTrace

/-- Negative fixture: parse-failing include input cannot admit a
LanguageDef-trace witness (no-success-side condition is impossible). -/
theorem brokenIncludeBytes_no_languageDefTraceWitness
    (label : String) (f : Metamath.Verify.Formula) :
    ¬ LanguageDefTraceWitness brokenIncludeBytes label f := by
  intro hTrace
  rcases hTrace with ⟨_proof, _prFinal, _f', hNoErr, _hAuthored, _hFold, _hSize, _hTop, _hExpr⟩
  have hSome :
      parseErrorCode? brokenIncludeBytes =
        some Metamath.Verify.ParseErrorCode.notACommand := by
    native_decide
  have hNone : parseErrorCode? brokenIncludeBytes = none := by
    unfold parseErrorCode?
    have hNoneDB : (checkBytesDB brokenIncludeBytes).parseErrorCode? = none := by
      unfold Metamath.Verify.DB.parseErrorCode?
      simp [hNoErr]
    simpa [checkBytesDB] using hNoneDB
  simp [hNone] at hSome

end Mettapedia.Languages.Metamath.AcceptanceEquivalence
