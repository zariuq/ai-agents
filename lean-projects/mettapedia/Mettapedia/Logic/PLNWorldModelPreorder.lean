import Mettapedia.Logic.EvidenceQuantale

/-!
# Core Evidence Preorders

Evidence-quality and support/confidence preorders for the PLN world-model layer.

These live here (rather than in governance modules) so that the core Logic/WM
theorem surface can use them without pulling in governance dependencies.

## Contents

- `EvidenceQualityLE` — pos↑ neg↓ preorder (better evidence = more positive, less negative)
- `supportConfidenceLE` — context-parameterized strength+confidence preorder

## Design note

The coordinatewise `PartialOrder` on `Evidence` (`e₁ ≤ e₂ ↔ pos₁ ≤ pos₂ ∧ neg₁ ≤ neg₂`)
is anti-correlated with strength: more negative evidence = higher in the order but lower
strength. A strength-respecting order must therefore be a separate relation.
There is no single canonical "better evidence" order — it must be parameterized by
prior context. (Hawthorne, "The Lockean Thesis and the Logic of Belief";
Foley, "Degrees of Belief".)
-/

namespace Mettapedia.Logic.PLNWorldModelPreorder

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceClass
open scoped ENNReal

/-! ## Evidence Quality Preorder -/

/-- Quality preorder on evidence:
`e₂` is at least as good as `e₁` if it has at least as much positive evidence and
no more negative evidence. -/
def EvidenceQualityLE (e₁ e₂ : Evidence) : Prop :=
  e₁.pos ≤ e₂.pos ∧ e₂.neg ≤ e₁.neg

theorem EvidenceQualityLE.refl (e : Evidence) : EvidenceQualityLE e e :=
  ⟨le_rfl, le_rfl⟩

theorem EvidenceQualityLE.trans {e₁ e₂ e₃ : Evidence}
    (h12 : EvidenceQualityLE e₁ e₂) (h23 : EvidenceQualityLE e₂ e₃) :
    EvidenceQualityLE e₁ e₃ :=
  ⟨le_trans h12.1 h23.1, le_trans h23.2 h12.2⟩

/-! ## Support/Confidence Preorder -/

variable (κ : ℝ≥0∞)

/-- Support/confidence preorder: `e₂` has at least as much support and
    confidence as `e₁`, relative to prior context `ctx` and confidence
    parameter `κ`. -/
noncomputable def supportConfidenceLE
    (ctx : BinaryContext) (κ : ℝ≥0∞) (e₁ e₂ : Evidence) : Prop :=
  Evidence.strengthWith ctx e₁ ≤ Evidence.strengthWith ctx e₂ ∧
  Evidence.toConfidence κ e₁ ≤ Evidence.toConfidence κ e₂

theorem supportConfidenceLE_refl
    (ctx : BinaryContext) (κ : ℝ≥0∞) (e : Evidence) :
    supportConfidenceLE ctx κ e e :=
  ⟨le_refl _, le_refl _⟩

theorem supportConfidenceLE_trans
    (ctx : BinaryContext) (κ : ℝ≥0∞)
    {e₁ e₂ e₃ : Evidence}
    (h₁₂ : supportConfidenceLE ctx κ e₁ e₂)
    (h₂₃ : supportConfidenceLE ctx κ e₂ e₃) :
    supportConfidenceLE ctx κ e₁ e₃ :=
  ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₁₂.2 h₂₃.2⟩

end Mettapedia.Logic.PLNWorldModelPreorder
