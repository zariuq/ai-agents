import Mettapedia.Logic.PLNFirstOrder.QuantifierSemantics

/-!
# Fuzzy Quantifier Semantics (Chapter 11)

Explicit quantifier semantics parameterized by:

- `ε`   : proxy tolerance around 0/1,
- `LPC` : lower proxy confidence,
- `UPC` : upper proxy confidence,
- `PCL` : proxy confidence threshold for crisp-like `ForAll` / `ThereExists` views.

This module stays generic over a finite-domain profile `U → ℝ` so it can be fed by
ITV coordinates (`lower`, `upper`, `strength`, `credibility`, `width`) or by direct
numerical fixtures.
-/

namespace Mettapedia.Logic.PLNFirstOrder

open Classical

/-- Chapter-11 fuzzy quantifier parameters. -/
structure FuzzyQuantifierParams where
  ε : ℝ
  LPC : ℝ
  UPC : ℝ
  PCL : ℝ
  hε : 0 ≤ ε ∧ ε ≤ 1
  hLPC : 0 ≤ LPC ∧ LPC ≤ 1
  hUPC : 0 ≤ UPC ∧ UPC ≤ 1
  hPCL : 0 ≤ PCL ∧ PCL ≤ 1
  hLPC_le_UPC : LPC ≤ UPC

section Profiles

variable {U : Type*} [Fintype U]

/-- Numeric proxy for being "essentially true" (`≈ 1`). -/
def nearOne (p : FuzzyQuantifierParams) (x : ℝ) : Prop :=
  1 - p.ε ≤ x ∧ x ≤ 1

/-- Numeric proxy for being "essentially false" (`≈ 0`). -/
def nearZero (p : FuzzyQuantifierParams) (x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ p.ε

/-- Number of witnesses satisfying a predicate. -/
noncomputable def witnessCount (pred : U → Prop) [DecidablePred pred] : ℕ :=
  Fintype.card {u // pred u}

/-- Fraction of witnesses satisfying a predicate (`0` on empty domain). -/
noncomputable def witnessFraction (pred : U → Prop) [DecidablePred pred] : ℝ :=
  if _h0 : Fintype.card U = 0 then
    0
  else
    (witnessCount pred : ℝ) / (Fintype.card U : ℝ)

theorem witnessFraction_nonneg (pred : U → Prop) [DecidablePred pred] :
    0 ≤ witnessFraction pred := by
  unfold witnessFraction
  by_cases h0 : Fintype.card U = 0
  · simp [h0]
  · have hden_pos_nat : 0 < Fintype.card U := Nat.pos_of_ne_zero h0
    have hden_nonneg : 0 ≤ (Fintype.card U : ℝ) := by positivity
    have hnum_nonneg : 0 ≤ (witnessCount pred : ℝ) := by positivity
    simp [h0, div_nonneg hnum_nonneg hden_nonneg]

theorem witnessFraction_le_one (pred : U → Prop) [DecidablePred pred] :
    witnessFraction pred ≤ 1 := by
  unfold witnessFraction
  by_cases h0 : Fintype.card U = 0
  · simp [h0]
  · have hden_pos_nat : 0 < Fintype.card U := Nat.pos_of_ne_zero h0
    have hden_pos : 0 < (Fintype.card U : ℝ) := by
      exact_mod_cast hden_pos_nat
    have hnum_le_nat : witnessCount pred ≤ Fintype.card U := by
      simpa [witnessCount] using (Fintype.card_subtype_le (p := pred))
    have hnum_le : (witnessCount pred : ℝ) ≤ (Fintype.card U : ℝ) := by
      exact_mod_cast hnum_le_nat
    have hdiv' :
        (witnessCount pred : ℝ) / (Fintype.card U : ℝ) ≤
          (Fintype.card U : ℝ) / (Fintype.card U : ℝ) := by
      exact div_le_div_of_nonneg_right hnum_le (le_of_lt hden_pos)
    have hden_ne : (Fintype.card U : ℝ) ≠ 0 := ne_of_gt hden_pos
    have hdiv : (witnessCount pred : ℝ) / (Fintype.card U : ℝ) ≤ 1 := by
      simpa [hden_ne] using hdiv'
    simpa [h0] using hdiv

theorem witnessCount_mono
    (pred₁ pred₂ : U → Prop) [DecidablePred pred₁] [DecidablePred pred₂]
    (hImpl : ∀ u, pred₁ u → pred₂ u) :
    witnessCount pred₁ ≤ witnessCount pred₂ := by
  classical
  unfold witnessCount
  refine Fintype.card_le_of_injective
    (fun x : {u // pred₁ u} => (⟨x.1, hImpl x.1 x.2⟩ : {u // pred₂ u})) ?_
  intro x y hxy
  cases x with
  | mk x hx =>
    cases y with
    | mk y hy =>
      simp at hxy
      simp [hxy]

theorem witnessFraction_mono
    (pred₁ pred₂ : U → Prop) [DecidablePred pred₁] [DecidablePred pred₂]
    (hImpl : ∀ u, pred₁ u → pred₂ u) :
    witnessFraction pred₁ ≤ witnessFraction pred₂ := by
  unfold witnessFraction
  by_cases h0 : Fintype.card U = 0
  · simp [h0]
  · have hden_nonneg : 0 ≤ (Fintype.card U : ℝ) := by positivity
    have hcount : witnessCount pred₁ ≤ witnessCount pred₂ :=
      witnessCount_mono pred₁ pred₂ hImpl
    have hcount' : (witnessCount pred₁ : ℝ) ≤ (witnessCount pred₂ : ℝ) := by
      exact_mod_cast hcount
    have hdiv :
        (witnessCount pred₁ : ℝ) / (Fintype.card U : ℝ) ≤
          (witnessCount pred₂ : ℝ) / (Fintype.card U : ℝ) := by
      exact div_le_div_of_nonneg_right hcount' hden_nonneg
    simpa [h0] using hdiv

/-- Fraction of witnesses that are `nearOne`. -/
noncomputable def nearOneFraction
    (p : FuzzyQuantifierParams) (profile : U → ℝ) : ℝ :=
  witnessFraction (fun u => nearOne p (profile u))

/-- Fraction of witnesses that are `nearZero`. -/
noncomputable def nearZeroFraction
    (p : FuzzyQuantifierParams) (profile : U → ℝ) : ℝ :=
  witnessFraction (fun u => nearZero p (profile u))

theorem nearOneFraction_in_unit
    (p : FuzzyQuantifierParams) (profile : U → ℝ) :
    nearOneFraction p profile ∈ Set.Icc 0 1 :=
  ⟨witnessFraction_nonneg _, witnessFraction_le_one _⟩

theorem nearZeroFraction_in_unit
    (p : FuzzyQuantifierParams) (profile : U → ℝ) :
    nearZeroFraction p profile ∈ Set.Icc 0 1 :=
  ⟨witnessFraction_nonneg _, witnessFraction_le_one _⟩

theorem nearOneFraction_mono_of_pointwise
    (p : FuzzyQuantifierParams)
    (profile₁ profile₂ : U → ℝ)
    (hle : ∀ u, profile₁ u ≤ profile₂ u)
    (hub : ∀ u, profile₂ u ≤ 1) :
    nearOneFraction p profile₁ ≤ nearOneFraction p profile₂ := by
  unfold nearOneFraction
  exact witnessFraction_mono
    (pred₁ := fun u => nearOne p (profile₁ u))
    (pred₂ := fun u => nearOne p (profile₂ u))
    (hImpl := by
      intro u hu
      exact ⟨le_trans hu.1 (hle u), hub u⟩)

/-- Score used for existential-style Chapter-11 checks. -/
noncomputable def fuzzyExistsScore
    (p : FuzzyQuantifierParams) (profile : U → ℝ) : ℝ :=
  nearOneFraction p profile

/-- Generic fuzzy quantifier truth: near-one frequency lies in `[LPC, UPC]`. -/
noncomputable def fuzzyIntervalHolds
    (p : FuzzyQuantifierParams) (profile : U → ℝ) : Prop :=
  p.LPC ≤ nearOneFraction p profile ∧ nearOneFraction p profile ≤ p.UPC

/-- Crisp-leaning `ForAll`: near-one frequency is at least `PCL`. -/
noncomputable def fuzzyForAllHolds
    (p : FuzzyQuantifierParams) (profile : U → ℝ) : Prop :=
  p.PCL ≤ nearOneFraction p profile

/-- Crisp-leaning `ThereExists`: at least `PCL` mass is not near-zero. -/
noncomputable def fuzzyThereExistsHolds
    (p : FuzzyQuantifierParams) (profile : U → ℝ) : Prop :=
  p.PCL ≤ 1 - nearZeroFraction p profile

/-- Profile-level conjunction with a constant score, used in Ch.11 rule-4 canaries. -/
def conjoinProfile (g : ℝ) (profile : U → ℝ) : U → ℝ :=
  fun u => min g (profile u)

/-- If `LPC ≤ PCL`, interval-style truth implies crisp-leaning `ForAll`. -/
theorem fuzzyInterval_implies_fuzzyForAll
    (p : FuzzyQuantifierParams) (profile : U → ℝ)
    (h : p.PCL ≤ p.LPC)
    (hInt : fuzzyIntervalHolds p profile) :
    fuzzyForAllHolds p profile := by
  unfold fuzzyIntervalHolds fuzzyForAllHolds at *
  exact le_trans h hInt.1

end Profiles

end Mettapedia.Logic.PLNFirstOrder
