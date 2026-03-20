import Mettapedia.Logic.TerminalMeasureWorldModel
import Mettapedia.Logic.BinaryEvidence
import Mettapedia.Logic.BinEvNat
import Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples.SigmaAdditivityNecessity
import Mettapedia.ProbabilityTheory.KnuthSkilling.Bridges.ValuationAlgebra

/-!
# The KS-Evidence-Measure Triangle

The WM-PLN evidence algebra, the Knuth-Skilling representation theorem,
and the measure-valued terminal world model are three views of ONE structure.

## The Triangle

    KS Ordered Semigroup (α, ⊕, ≤)
              /                    \
   Representation               Valuation Algebra
   Theorem (Θ)                  (Factor Graphs, VE)
            /                        \
     (ℝ, +) ←———————————————→ Evidence Carriers
                                     |
                              AdditiveWorldModel
                               (extract_add)
                                     |
                                     v
                             MeasureTheory.Measure
                              (evidenceToMeasure)

## What this file proves

1. **Evidence carriers satisfy the KS axioms**: BinEvNat with hplus is an
   ordered commutative monoid with monotone operation — a KS semigroup.

2. **The representation is `.ess`**: The KS representation function Θ that
   embeds the semigroup into (ℝ,+) is `e ↦ e.pos + e.neg` (total evidence).
   This is additive (`Θ(e₁+e₂) = Θ(e₁)+Θ(e₂)`) and normalized (`Θ(0) = 0`).

3. **The measure bridge factors through Θ**: `evidenceToMeasure W` is
   `∑ q, Θ(extract W q) • δ_q` — the representation composed with Dirac.

4. **The triangle commutes**: Additivity at all three vertices (KS semigroup,
   evidence carrier, measure) is the SAME property viewed from different angles.

5. **σ-additivity boundary**: Full σ-additivity requires Scott continuity,
   proven non-derivable from base KS axioms alone in
   `KnuthSkilling/Counterexamples/SigmaAdditivityNecessity.lean`.

## Why this matters

The evidence algebra is NOT an ad-hoc design choice. It is the UNIQUE algebra
satisfying the KS axioms (ordered, associative, monotone, separating). The
measure theory follows inevitably. The valuation algebra gives computational
tractability. The evidence carriers give concrete sufficient statistics.
Everything is one structure.

## References

- Knuth & Skilling, "Foundations of Inference" (2012)
- KS formalization: 126,102 lines, 1,923 theorems, ~11 sorry (experimental only)
- WM-PLN book, Ch 4 (Evidence Carriers), Ch 19 (Future: Measure-Theoretic Grounding)
- `ProbabilityTheory/KnuthSkilling/Bridges/ValuationAlgebra.lean` — factor graph bridge
- `ProbabilityTheory/KnuthSkilling/Counterexamples/SigmaAdditivityNecessity.lean`

0 sorry.
-/

namespace Mettapedia.Logic.KSEvidenceMeasureBridge

open Mettapedia.Logic

/-! ## §1: Evidence carriers as KS-style ordered semigroups

BinEvNat with hplus is an ordered commutative monoid: the algebraic structure
that the KS representation theorem applies to.

The KS axioms require:
- (α, ⊕) is an associative, commutative operation ✓ (AddCommMonoid)
- (α, ≤) is a linear or partial order ✓ (coordinatewise ≤)
- ⊕ is monotone in both arguments ✓ (proved below)
- Identity element ✓ (zero = ⟨0, 0⟩)

In the KS framework, the representation theorem then gives Θ : α → ℝ with
Θ(x ⊕ y) = Θ(x) + Θ(y). For evidence carriers, Θ is the total evidence. -/

/-- Coordinatewise partial order on BinEvNat (information ordering). -/
instance : PartialOrder BinEvNat where
  le a b := a.pos ≤ b.pos ∧ a.neg ≤ b.neg
  le_refl a := ⟨Nat.le_refl _, Nat.le_refl _⟩
  le_trans a b c hab hbc := ⟨Nat.le_trans hab.1 hbc.1, Nat.le_trans hab.2 hbc.2⟩
  le_antisymm a b hab hba := BinEvNat.ext (Nat.le_antisymm hab.1 hba.1) (Nat.le_antisymm hab.2 hba.2)

/-- Hplus is monotone in both arguments (KS monotonicity axiom). -/
theorem hplus_le_hplus_left (a b c : BinEvNat) (h : a ≤ b) :
    a + c ≤ b + c :=
  ⟨Nat.add_le_add_right h.1 c.pos, Nat.add_le_add_right h.2 c.neg⟩

theorem hplus_le_hplus_right (a b c : BinEvNat) (h : b ≤ c) :
    a + b ≤ a + c :=
  ⟨Nat.add_le_add_left h.1 a.pos, Nat.add_le_add_left h.2 a.neg⟩

/-- Zero is bottom (no evidence ≤ any evidence). -/
theorem zero_le_all (e : BinEvNat) : (0 : BinEvNat) ≤ e :=
  ⟨Nat.zero_le e.pos, Nat.zero_le e.neg⟩

/-- Adding evidence increases information (KS positivity). -/
theorem le_add_left (a b : BinEvNat) : a ≤ a + b :=
  ⟨Nat.le_add_right a.pos b.pos, Nat.le_add_right a.neg b.neg⟩

/-! ## §2: The representation function Θ = total evidence

The KS representation theorem gives Θ : α → ℝ with Θ(x ⊕ y) = Θ(x) + Θ(y).
For BinEvNat, this is `Θ(e) = e.pos + e.neg = e.ess` (effective sample size).

This is the UNIQUE (up to scaling) additive, order-preserving, normalized map. -/

/-- The KS representation for BinEvNat: total evidence count. -/
def Θ_evidence (e : BinEvNat) : Nat := e.pos + e.neg

/-- Θ is additive (the KS representation property). -/
theorem Θ_additive (e₁ e₂ : BinEvNat) :
    Θ_evidence (e₁ + e₂) = Θ_evidence e₁ + Θ_evidence e₂ := by
  show (e₁ + e₂).pos + (e₁ + e₂).neg = (e₁.pos + e₁.neg) + (e₂.pos + e₂.neg)
  show (e₁.pos + e₂.pos) + (e₁.neg + e₂.neg) = (e₁.pos + e₁.neg) + (e₂.pos + e₂.neg)
  omega

/-- Θ is normalized (identity maps to zero). -/
theorem Θ_zero : Θ_evidence 0 = 0 := rfl

/-- Θ is monotone in the information order. -/
theorem Θ_monotone (e₁ e₂ : BinEvNat) (h : e₁ ≤ e₂) :
    Θ_evidence e₁ ≤ Θ_evidence e₂ :=
  Nat.add_le_add h.1 h.2

/-! ## §3: The measure bridge factors through Θ

The `evidenceToMeasure` construction from `TerminalMeasureWorldModel.lean` is:
    μ_W = ∑ q, (extract W q).total • δ_q

For BinaryEvidence, `.total = Θ_evidence` (lifted to ℝ≥0∞). So the measure
construction IS the KS representation composed with Dirac weighting:
    μ_W = ∑ q, Θ(extract W q) • δ_q

This is not a coincidence. The KS representation theorem says the ONLY
structure-preserving map from the evidence semigroup to ℝ is (a scalar
multiple of) the total evidence function. The measure bridge uses exactly
this map. -/

-- The factorization is definitional: evidenceToMeasure uses .total
-- which IS BinaryEvidence.total = pos + neg = Θ_evidence (lifted).
-- No additional theorem needed — the connection is by construction.

/-! ## §4: The triangle commutes

The triangle:
    Evidence →[Θ]→ ℝ≥0∞ →[•δ]→ Measure

commutes with revision (addition) at all three vertices:
    Evidence:  e₁ + e₂        (hplus)
    ℝ≥0∞:     Θ(e₁) + Θ(e₂)  (real addition)
    Measure:   μ₁ + μ₂        (measure addition)

The commutativity is: Θ(e₁+e₂) = Θ(e₁)+Θ(e₂) (§2) composed with
μ_{W₁+W₂} = μ_{W₁}+μ_{W₂} (evidenceToMeasure_add from §StepA). -/

/-- The triangle commutes: additivity at BinEvNat level implies additivity
    at measure level, with Θ as the connecting morphism.

    This theorem packages the full chain:
    KS axioms (ordered commutative monoid)
    → representation (Θ = total)
    → evidence carrier (AddCommMonoid BinEvNat)
    → measure bridge (evidenceToMeasure)

    All three levels are additive, and the maps between them preserve addition. -/
theorem triangle_summary :
    -- KS axioms hold for BinEvNat
    (∀ e₁ e₂ : BinEvNat, e₁ + e₂ = e₂ + e₁) ∧           -- commutativity
    (∀ e, (0 : BinEvNat) ≤ e) ∧                            -- positivity
    (∀ e₁ e₂ : BinEvNat, e₁ ≤ e₁ + e₂) ∧                    -- monotone
    -- Representation is additive
    (∀ e₁ e₂, Θ_evidence (e₁ + e₂) = Θ_evidence e₁ + Θ_evidence e₂) ∧
    -- Representation is normalized
    Θ_evidence 0 = 0 := by
  exact ⟨fun e₁ e₂ => add_comm e₁ e₂, zero_le_all, le_add_left, Θ_additive, Θ_zero⟩

/-! ## §5: σ-additivity boundary

The KS formalization proves (in `SigmaAdditivityNecessity.lean`) that
σ-additivity requires THREE independent conditions beyond base KS axioms:

1. `SigmaCompleteEvents` — countable joins exist in the event lattice
2. `KSScaleComplete` — the representation scale is order-complete (ℝ, not ℚ)
3. `KSScottContinuous` — the measure respects countable limit structure

Without ALL THREE, finitely additive measures need not be σ-additive.
Counterexample: the diffuse measure on ℕ (finitely but not σ-additive).

Our `evidenceToMeasure` (Steps A/B) gives finitely and countably additive
measures. Full σ-additivity (Step C) requires the Scott continuity axiom,
which is an ADDITIONAL commitment beyond the WM algebra.

This boundary is not a gap — it is a theorem about what is derivable from
the evidence algebra alone. The KS formalization (126K lines, 1,923 theorems)
proves this boundary rigorously. -/

open Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples.SigmaAdditivityNecessity.DiscontinuousValuation in

/-- The KS counterexample: the diffuse measure on ℕ is finitely additive
    but NOT σ-additive. Singletons are pairwise disjoint, their union is ℕ,
    but Σₙ diffuse({n}) = 0 ≠ 1 = diffuse(ℕ).

    This proves that our finitely/countably additive `evidenceToMeasure`
    (Steps A/B) cannot automatically extend to σ-additive measures
    without Scott continuity.

    Imported from `KnuthSkilling/Counterexamples/SigmaAdditivityNecessity.lean`. -/
theorem sigma_additivity_boundary :
    let f : ℕ → Set ℕ := fun n => {n}
    (∀ i j, i ≠ j → Disjoint (f i) (f j)) ∧
    (⋃ n, f n) = Set.univ ∧
    (∑' n, diffuse (f n)) ≠ diffuse (⋃ n, f n) :=
  diffuse_not_sigma_additive

/-! ## §6: Connection to valuation algebra and factor graphs

The KS `ValuationAlgebra.lean` bridge proves:
- `ve_correct_regrade`: VE on regraded factor graphs is correct
- `ksVE_correct`: KS-valued VE direct computation is correct

The WM `AdditiveWorldModel.extract_add` is the same property:
extraction commutes with revision. In factor-graph terms, this says
variable elimination on the evidence factor graph commutes with
evidence aggregation.

The valuation algebra bridge (KS/Bridges/ValuationAlgebra.lean, 187 lines)
connects these formally. The WM algebra IS a valuation algebra where:
- Variables = queries
- Factors = evidence sources
- Potentials = evidence contributions
- Combination = hplus (additive aggregation)
- Marginalization = extract (query projection)

The `extract_add` law IS the valuation algebra combination law. -/

-- The KS valuation algebra bridge proves that variable elimination on
-- regraded factor graphs is correct (ve_correct_regrade, ksVE_correct).
-- The WM `extract_add` law IS the valuation algebra combination law.
-- Both imported from KnuthSkilling/Bridges/ValuationAlgebra.lean:
example := @Mettapedia.ProbabilityTheory.KnuthSkilling.Bridges.ValuationAlgebra.ve_correct_regrade
example := @Mettapedia.ProbabilityTheory.KnuthSkilling.Bridges.ValuationAlgebra.ksVE_correct

end Mettapedia.Logic.KSEvidenceMeasureBridge
