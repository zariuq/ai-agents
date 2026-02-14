import Mettapedia.OSLF.Formula
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNWorldModel

/-!
# Evidence-Valued OSLF Semantics

Evidence-valued formula interpretation using Evidence's Frame (complete Heyting
algebra) structure.  This is the PRIMARY semantic layer per the
Stay/Baez/Knuth/Meredith architecture:

- Evidence is a `Frame` (hence `HeytingAlgebra`, `CompleteLattice`)
- OSLF formulas map to Evidence values via lattice operations
- Threshold-Prop semantics (`sem`) is a corollary, not the foundation
- The threshold bridge is PARTIAL: it fails for disjunction/diamond because
  `τ ≤ x ⊔ y ⇏ τ ≤ x ∨ τ ≤ y` in Evidence's non-total order
  (this IS the Knuth-Skilling imprecision gate)

## Interpretation Table

| Formula   | Evidence semantics          |
|-----------|-----------------------------|
| ⊤         | ⊤ (top evidence)            |
| ⊥         | ⊥ (zero evidence)           |
| atom a    | I a p                       |
| φ ∧ ψ    | semE φ p ⊓ semE ψ p        |
| φ ∨ ψ    | semE φ p ⊔ semE ψ p        |
| φ → ψ    | semE φ p ⇨ semE ψ p        |
| ◇ φ      | ⨆ {q | R p q}, semE φ q    |
| □ φ      | ⨅ {q | R q p}, semE φ q    |

## References

- Meredith & Stay, "Operational Semantics in Logical Form"
- Knuth & Skilling, "Foundations of Inference" (totality axiom)
-/

namespace Mettapedia.Logic.OSLFEvidenceSemantics

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel

open scoped ENNReal

/-! ## Evidence-Valued Atom Semantics -/

/-- Evidence-valued atom interpretation: maps atom names and patterns to Evidence. -/
abbrev EvidenceAtomSem := String → Pattern → Evidence

/-! ## Evidence-Valued Formula Semantics -/

/-- Evidence-valued denotational semantics of OSLF formulas.

Uses Evidence's Frame structure:
- `⊓` for conjunction (coordinatewise min)
- `⊔` for disjunction (coordinatewise max)
- `⇨` for Heyting implication (residuation)
- `⨆`/`⨅` for modalities over step-related states -/
noncomputable def semE (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) :
    OSLFFormula → Pattern → Evidence
  | .top, _ => ⊤
  | .bot, _ => ⊥
  | .atom a, p => I a p
  | .and φ ψ, p => semE R I φ p ⊓ semE R I ψ p
  | .or φ ψ, p => semE R I φ p ⊔ semE R I ψ p
  | .imp φ ψ, p => semE R I φ p ⇨ semE R I ψ p
  | .dia φ, p => ⨆ (q : {q // R p q}), semE R I φ q.val
  | .box φ, p => ⨅ (q : {q // R q p}), semE R I φ q.val

/-! ## Unfolding Lemmas -/

@[simp] theorem semE_top (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (p : Pattern) :
    semE R I .top p = ⊤ := rfl

@[simp] theorem semE_bot (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (p : Pattern) :
    semE R I .bot p = ⊥ := rfl

@[simp] theorem semE_atom (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (a : String) (p : Pattern) :
    semE R I (.atom a) p = I a p := rfl

@[simp] theorem semE_and (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.and φ ψ) p = semE R I φ p ⊓ semE R I ψ p := rfl

@[simp] theorem semE_or (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.or φ ψ) p = semE R I φ p ⊔ semE R I ψ p := rfl

@[simp] theorem semE_imp (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.imp φ ψ) p = semE R I φ p ⇨ semE R I ψ p := rfl

@[simp] theorem semE_dia (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ : OSLFFormula) (p : Pattern) :
    semE R I (.dia φ) p = ⨆ (q : {q // R p q}), semE R I φ q.val := rfl

@[simp] theorem semE_box (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ : OSLFFormula) (p : Pattern) :
    semE R I (.box φ) p = ⨅ (q : {q // R q p}), semE R I φ q.val := rfl

/-! ## Structural Monotonicity -/

/-- Conjunction projects to the left component. -/
theorem semE_and_le_left (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.and φ ψ) p ≤ semE R I φ p :=
  inf_le_left

/-- Conjunction projects to the right component. -/
theorem semE_and_le_right (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.and φ ψ) p ≤ semE R I ψ p :=
  inf_le_right

/-- Left disjunct injects into disjunction. -/
theorem semE_le_or_left (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I φ p ≤ semE R I (.or φ ψ) p :=
  le_sup_left

/-- Right disjunct injects into disjunction. -/
theorem semE_le_or_right (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I ψ p ≤ semE R I (.or φ ψ) p :=
  le_sup_right

/-- A step-successor's evidence injects into diamond. -/
theorem semE_dia_le (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ : OSLFFormula) (p q : Pattern) (h : R p q) :
    semE R I φ q ≤ semE R I (.dia φ) p :=
  le_iSup (fun (s : {s // R p s}) => semE R I φ s.val) ⟨q, h⟩

/-- Box projects to any predecessor. -/
theorem semE_box_le (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ : OSLFFormula) (p q : Pattern) (h : R q p) :
    semE R I (.box φ) p ≤ semE R I φ q :=
  iInf_le (fun (s : {s // R s p}) => semE R I φ s.val) ⟨q, h⟩

/-! ## Modus Ponens (Heyting) -/

/-- Heyting modus ponens: `semE (φ → ψ) p ⊓ semE φ p ≤ semE ψ p`. -/
theorem semE_imp_mp (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.imp φ ψ) p ⊓ semE R I φ p ≤ semE R I ψ p := by
  simp only [semE_imp]
  exact himp_inf_le

/-! ## World-Model Connection -/

section WMConnection

variable {State : Type*} [EvidenceType State] [WorldModel State Pattern]

/-- Evidence atom semantics from a world-model state: the atom at pattern p
is the evidence extracted by querying `queryOfAtom a p`. -/
noncomputable def wmEvidenceAtomSem
    (W : State) (queryOfAtom : String → Pattern → Pattern) : EvidenceAtomSem :=
  fun a p => WorldModel.evidence W (queryOfAtom a p)

/-- WM revision lifts to evidence atoms: revising world states then
extracting atom evidence = extracting from each and combining. -/
theorem semE_wm_atom_revision
    (W₁ W₂ : State) (queryOfAtom : String → Pattern → Pattern)
    (R : Pattern → Pattern → Prop) (a : String) (p : Pattern) :
    semE R (wmEvidenceAtomSem (W₁ + W₂) queryOfAtom) (.atom a) p =
      semE R (wmEvidenceAtomSem W₁ queryOfAtom) (.atom a) p +
      semE R (wmEvidenceAtomSem W₂ queryOfAtom) (.atom a) p := by
  simp only [semE_atom, wmEvidenceAtomSem]
  exact WorldModel.evidence_add W₁ W₂ (queryOfAtom a p)

end WMConnection

/-! ## Threshold Bridge (Conjunctive Fragment)

The threshold bridge `τ ≤ semE R I φ p → sem R (threshI τ) φ p` works for
the conjunctive fragment (top, atom, and, box) but FAILS for the
disjunctive fragment (or, dia) because Evidence's order is non-total:
`τ ≤ x ⊔ y ⇏ τ ≤ x ∨ τ ≤ y`.

This is the formal expression of the Knuth-Skilling imprecision gate:
precise (Boolean) semantics can only be recovered on fragments where
the Heyting algebra happens to be Boolean. -/

/-- Threshold atom semantics: atom holds when evidence exceeds threshold. -/
noncomputable def threshAtomSem (I : EvidenceAtomSem) (τ : Evidence) :
    AtomSem :=
  fun a p => τ ≤ I a p

/-- Threshold bridge for atoms: direct by definition. -/
theorem threshold_atom (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (a : String) (p : Pattern) :
    τ ≤ semE R I (.atom a) p ↔ sem R (threshAtomSem I τ) (.atom a) p := by
  rfl

/-- Threshold bridge for conjunction. -/
theorem threshold_and (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (φ ψ : OSLFFormula) (p : Pattern)
    (hφ : τ ≤ semE R I φ p → sem R (threshAtomSem I τ) φ p)
    (hψ : τ ≤ semE R I ψ p → sem R (threshAtomSem I τ) ψ p) :
    τ ≤ semE R I (.and φ ψ) p → sem R (threshAtomSem I τ) (.and φ ψ) p := by
  intro h
  simp only [semE_and] at h
  exact ⟨hφ (le_trans h inf_le_left), hψ (le_trans h inf_le_right)⟩

/-- Threshold bridge FAILS for disjunction in general.

Counterexample: I "a" = (1,0), I "b" = (0,1) are incomparable in Evidence.
Their join (1,0) ⊔ (0,1) = (1,1), but τ = (1,1) exceeds neither component.
This is the imprecision gate in action: non-total order prevents Boolean
reduction of disjunction. -/
theorem threshold_or_counterexample :
    ¬ (∀ (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
       (φ ψ : OSLFFormula) (p : Pattern),
       τ ≤ semE R I (.or φ ψ) p →
       sem R (threshAtomSem I τ) (.or φ ψ) p) := by
  intro h
  -- I "a" = (1,0), I "b" = (0,1) are incomparable; τ = (1,1) = their join
  let p₀ : Pattern := .apply "x" []
  let I : EvidenceAtomSem := fun a _ =>
    if a == "a" then ⟨1, 0⟩ else ⟨0, 1⟩
  let τ₀ : Evidence := ⟨1, 1⟩
  let R₀ : Pattern → Pattern → Prop := fun _ _ => False
  have hle : τ₀ ≤ semE R₀ I (.or (.atom "a") (.atom "b")) p₀ := by
    simp only [semE_or, semE_atom]
    show (⟨1, 1⟩ : Evidence) ≤ (⟨1, 0⟩ : Evidence) ⊔ (⟨0, 1⟩ : Evidence)
    exact ⟨(@le_sup_left Evidence _ ⟨1, 0⟩ ⟨0, 1⟩).1, (@le_sup_right Evidence _ ⟨1, 0⟩ ⟨0, 1⟩).2⟩
  have habs := h I τ₀ R₀ (.atom "a") (.atom "b") p₀ hle
  simp only [sem, threshAtomSem] at habs
  have hnle : ¬ ((1 : ℝ≥0∞) ≤ (0 : ℝ≥0∞)) := by norm_num
  rcases habs with h1 | h2
  · exact hnle h1.2
  · exact hnle h2.1

/-! ### Complete Fragment Classification

The threshold bridge `τ ≤ semE ... → sem ...` works precisely for the
**conjunctive/universal fragment** {⊤, atom, ∧, →, □} and FAILS for the
**disjunctive/existential fragment** {∨, ◇}.

This is the formal expression of the Knuth-Skilling totality axiom:
point-valued (Boolean) semantics requires total order; Evidence's
non-total order forces Heyting default on disjunctive connectives. -/

/-- Threshold bridge for ⊤: always works (vacuously). -/
theorem threshold_top (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (p : Pattern) :
    τ ≤ semE R I .top p → sem R (threshAtomSem I τ) .top p := by
  intro _; trivial

/-- Threshold bridge for ⊥: works by absurdity (τ ≤ ⊥ is impossible for τ > 0). -/
theorem threshold_bot (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (p : Pattern) (hτ : ⊥ < τ) :
    τ ≤ semE R I .bot p → sem R (threshAtomSem I τ) .bot p := by
  intro h; exact absurd (lt_of_lt_of_le hτ h) (lt_irrefl _)

/-- Threshold bridge for implication (→): evidence-level modus ponens.

If `τ ≤ φ ⇨ ψ` and `τ ≤ φ` then `τ ≤ ψ`. The second hypothesis is at
the evidence level (not Prop level) because the reverse bridge
`sem (threshAtomSem I τ) φ p → τ ≤ semE R I φ p` fails for the
disjunctive fragment. -/
theorem threshold_imp (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (φ ψ : OSLFFormula) (p : Pattern)
    (hψ : τ ≤ semE R I ψ p → sem R (threshAtomSem I τ) ψ p) :
    τ ≤ semE R I (.imp φ ψ) p →
    τ ≤ semE R I φ p →
    sem R (threshAtomSem I τ) ψ p := by
  intro himp hφ
  apply hψ
  calc τ = τ ⊓ τ := (inf_idem _).symm
    _ ≤ (semE R I φ p ⇨ semE R I ψ p) ⊓ semE R I φ p := inf_le_inf himp hφ
    _ ≤ semE R I ψ p := himp_inf_le

/-- Threshold bridge for box (□): works because ⊓ distributes over threshold. -/
theorem threshold_box (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (φ : OSLFFormula) (p : Pattern)
    (hφ : ∀ q, R q p → τ ≤ semE R I φ q → sem R (threshAtomSem I τ) φ q) :
    τ ≤ semE R I (.box φ) p → sem R (threshAtomSem I τ) (.box φ) p := by
  intro h q hqp
  apply hφ q hqp
  exact le_trans h (semE_box_le R I φ p q hqp)

/-- Threshold bridge FAILS for diamond (◇) in general.

Same mechanism as `threshold_or_counterexample`: `τ ≤ ⨆ ... ⇏ ∃ ..., τ ≤ ...`
because Evidence is non-total. Two successors q₁, q₂ with incomparable evidence
(1,0) and (0,1) have supremum (1,1), but no single successor exceeds (1,1). -/
theorem threshold_dia_fails :
    ¬ (∀ (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
       (φ : OSLFFormula) (p : Pattern),
       τ ≤ semE R I (.dia φ) p →
       sem R (threshAtomSem I τ) (.dia φ) p) := by
  intro h
  let p₀ : Pattern := .apply "p" []
  let q₁ : Pattern := .apply "q1" []
  let q₂ : Pattern := .apply "q2" []
  let I : EvidenceAtomSem := fun _ q =>
    if q == q₁ then ⟨1, 0⟩ else ⟨0, 1⟩
  let τ₀ : Evidence := ⟨1, 1⟩
  let R₀ : Pattern → Pattern → Prop := fun p q => p = p₀ ∧ (q = q₁ ∨ q = q₂)
  -- τ₀ = (1,1) ≤ (1,0) ⊔ (0,1) ≤ ⨆ over {q₁, q₂} by le_iSup + sup_le
  have hle : τ₀ ≤ semE R₀ I (.dia (.atom "a")) p₀ := by
    simp only [semE_dia, semE_atom]
    have h1 := le_iSup (fun (q : {q // R₀ p₀ q}) => I "a" q.val) ⟨q₁, rfl, Or.inl rfl⟩
    have h2 := le_iSup (fun (q : {q // R₀ p₀ q}) => I "a" q.val) ⟨q₂, rfl, Or.inr rfl⟩
    refine le_trans ?_ (sup_le h1 h2)
    simp only [I, q₁, q₂, beq_iff_eq]
    exact ⟨le_sup_of_le_left (le_refl _), le_sup_of_le_right (le_refl _)⟩
  -- But no single successor has evidence ≥ (1,1)
  have habs := h I τ₀ R₀ (.atom "a") p₀ hle
  simp only [sem, threshAtomSem] at habs
  have hnle : ¬ ((1 : ℝ≥0∞) ≤ (0 : ℝ≥0∞)) := by norm_num
  rcases habs with ⟨q, ⟨_, hq⟩, hsat⟩
  rcases hq with rfl | rfl
  · exact hnle hsat.2
  · exact hnle hsat.1

end Mettapedia.Logic.OSLFEvidenceSemantics
