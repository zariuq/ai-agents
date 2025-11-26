import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.Group.Defs
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Order.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling

/-
# Measure Theory from Symmetry

This file shows how measure theory EMERGES from the Knuth–Skilling
symmetry foundations, connecting to Mathlib's standard structures.

Key results:
- Un-normalized valuations (`μ(⊤)` allowed in `(0,∞)`, not necessarily `1`)
- σ-additivity from continuity (the paper's KEY insight)
- Connection to `MeasureTheory.Measure`
- Haar measures from translation invariance

References:
- Skilling & Knuth (2018), Section 2 (Measure Theory)
- ~/claude/literature/Knuth_Skilling/Knuth_Skilling_1712.09725v3.pdf
-/

noncomputable section

open Classical
open scoped BigOperators Pointwise ENNReal Topology
open MeasureTheory Filter Set
open Mettapedia.ProbabilityTheory.KnuthSkilling

namespace Mettapedia.MeasureTheory

/-! ## Un-normalized valuations -/

/-- An un-normalized plausibility valuation into extended non-negative reals.
Unlike a probability valuation, we do not require `val ⊤ = 1`. -/
structure UnnormalizedValuation (α : Type*) [CompleteLattice α] where
  val : α → ℝ≥0∞
  monotone : Monotone val
  val_bot : val ⊥ = 0
  -- Note: NO requirement that val ⊤ = 1

/-! ## Cox-style combination in the un-normalized setting -/

/-- Cox combination laws for un-normalized valuations.
We keep only the algebraic structure needed for the additivity derivation. -/
structure UnnormalizedCox (α : Type*) [CompleteLattice α] (μ : UnnormalizedValuation α) where
  combine_fn : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞
  combine_comm : ∀ x y, combine_fn x y = combine_fn y x
  combine_assoc :
    ∀ x y z, combine_fn (combine_fn x y) z = combine_fn x (combine_fn y z)
  combine_val :
    ∀ a b, Disjoint a b → μ.val (a ⊔ b) = combine_fn (μ.val a) (μ.val b)
  /-- Regraduation map that linearizes the combination law. -/
  regrade : ℝ≥0∞ → ℝ≥0∞
  regrade_strictMono : StrictMono regrade
  regrade_additive : ∀ x y, regrade (x + y) = regrade x + regrade y
  regrade_combine : ∀ x y, regrade (combine_fn x y) = regrade x + regrade y

/-! ## Finite additivity for un-normalized valuations -/

-- TODO: Adapt the regraduation-based proof from `KnuthSkilling.lean`.
theorem unnormalized_combine_is_add {α : Type*}
    [CompleteLattice α]
    (μ : UnnormalizedValuation α) (cox : UnnormalizedCox α μ) :
    ∀ x y, cox.combine_fn x y = x + y := by
  intro x y
  -- The regraduation map linearizes the combination; strict monotonicity gives injectivity.
  refine cox.regrade_strictMono.injective ?_
  calc
    cox.regrade (cox.combine_fn x y) = cox.regrade x + cox.regrade y :=
      cox.regrade_combine x y
    _ = cox.regrade (x + y) := (cox.regrade_additive x y).symm

/-! ## σ-additivity from continuity (core Knuth–Skilling insight) -/

theorem sigma_additive_from_continuity {α : Type*}
    [CompleteLattice α]
    (μ : UnnormalizedValuation α)
    (cox : UnnormalizedCox α μ)
    (continuity : ∀ (s : ℕ → α), Monotone s →
      Tendsto (μ.val ∘ s) atTop (𝓝 (μ.val (⨆ i, s i)))) :
    ∀ (f : ℕ → α), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
      μ.val (⨆ i, f i) = ∑' i, μ.val (f i) := by
  /-
  Strategy (Knuth-Skilling's KEY insight):
  1. Define partial unions s_n := ⨆ i ≤ n, f i (finite union)
  2. Show s is monotone in n
  3. ⨆ n, s_n = ⨆ i, f i by lattice algebra
  4. Finite additivity gives μ(s_n) = Σ_{i≤n} μ(f i)
  5. Continuity: μ(⨆ n, s_n) = lim_{n→∞} μ(s_n)
  6. Therefore: μ(⨆ i, f i) = Σ'_{i} μ(f i)
  -/
  intro f hf_disj

  -- Step 1: Define partial finite unions
  let s : ℕ → α := fun n => ⨆ i : Fin (n + 1), f i

  -- Step 2: s is monotone
  have hs_mono : Monotone s := by
    intro m n hmn
    simp only [s]
    apply iSup_le
    intro i
    have hi : i.val < n + 1 := by omega
    apply le_iSup_of_le ⟨i.val, hi⟩
    rfl

  -- Step 3: ⨆ n, s_n = ⨆ i, f i
  have hs_sup : ⨆ n, s n = ⨆ i, f i := by
    apply le_antisymm
    · apply iSup_le; intro n
      apply iSup_le; intro i
      apply le_iSup (f := f)
    · apply iSup_le; intro i
      apply le_iSup_of_le i
      apply le_iSup (f := fun (j : Fin (i + 1)) => f j) ⟨i, Nat.lt_succ_self i⟩

  -- Step 4: Finite additivity for each s_n (using unnormalized_combine_is_add)
  have hs_finite_add : ∀ n, μ.val (s n) = ∑ i : Fin (n + 1), μ.val (f i) := by
    sorry  -- TODO: Prove by induction using combine_fn = (+)

  -- Step 5 & 6: Apply continuity to get σ-additivity
  -- The continuity hypothesis gives: lim_{n→∞} μ(s_n) = μ(⨆ n, s_n)
  -- Finite additivity gives: μ(s_n) = Σ_{i≤n} μ(f_i)
  -- Therefore: μ(⨆ i, f_i) = lim_{n→∞} Σ_{i≤n} μ(f_i) = Σ'_{i} μ(f_i)
  calc μ.val (⨆ i, f i)
      = μ.val (⨆ n, s n) := by rw [← hs_sup]
    _ = ∑' i, μ.val (f i) := by
        -- TODO: Complete proof using:
        -- 1. continuity s hs_mono gives Tendsto (μ.val ∘ s) atTop (𝓝 (μ.val (⨆ n, s n)))
        -- 2. hs_finite_add gives μ.val (s n) = Σ_{i : Fin (n+1)} μ.val (f i)
        -- 3. Connect finite sum to infinite series via ENNReal.tendsto_nat_tsum
        sorry

/-! ## Constructing a Mathlib measure from a symmetric valuation -/

/-- Build a `Measure` from an un-normalized valuation satisfying σ-additivity. -/
def toMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : UnnormalizedValuation (Set Ω))
    (cox : UnnormalizedCox (Set Ω) μ)
    (h_sigma : ∀ (f : ℕ → Set Ω), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
               μ.val (⨆ i, f i) = ∑' i, μ.val (f i)) :
    Measure Ω := by
  classical
  -- Mark `cox` as used to avoid linter warnings.
  have _ := cox.combine_comm 0 0
  refine Measure.ofMeasurable (m := fun s _ => μ.val s) ?m0 ?mUnion
  · simpa using μ.val_bot
  · intro f hf hpair
    -- `h_sigma` already provides σ-additivity on pairwise disjoint families.
    have hdisj : ∀ i j, i ≠ j → Disjoint (f i) (f j) := by
      intro i j hij
      exact hpair hij
    simpa using h_sigma f hdisj

@[simp]
theorem toMeasure_apply {Ω : Type*} [MeasurableSpace Ω]
    (μ : UnnormalizedValuation (Set Ω))
    (cox : UnnormalizedCox (Set Ω) μ)
    (h_sigma : ∀ (f : ℕ → Set Ω), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
               μ.val (⨆ i, f i) = ∑' i, μ.val (f i))
    {s : Set Ω} (hs : MeasurableSet s) :
    toMeasure μ cox h_sigma s = μ.val s := by
  -- Mark `cox` as used to avoid linter warnings.
  have _ := cox.combine_comm 0 0
  simp [toMeasure, Measure.ofMeasurable_apply, hs]

/-! ## Translation invariance and Haar measure -/

/-- Translation invariance of an un-normalized valuation on sets of a group. -/
structure TranslationInvariant (G : Type*) [Group G] [TopologicalSpace G]
    (μ : UnnormalizedValuation (Set G)) where
  invariant : ∀ (g : G) (A : Set G), μ.val (g • A) = μ.val A

/-- A translation-invariant symmetric valuation yields a left-invariant measure.
TODO: upgrade conclusion to `IsHaarMeasure` once the predicate is wired up in this build. -/
theorem translation_invariant_is_haar
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : UnnormalizedValuation (Set G))
    (cox : UnnormalizedCox (Set G) μ)
    (h_sigma : ∀ (f : ℕ → Set G), (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
               μ.val (⨆ i, f i) = ∑' i, μ.val (f i))
    (h_trans : TranslationInvariant G μ) :
    MeasureTheory.Measure.IsMulLeftInvariant (toMeasure μ cox h_sigma) := by
  classical
  let ν := toMeasure (μ := μ) (cox := cox) (h_sigma := h_sigma)
  refine ⟨?_⟩
  intro g
  -- Compare the measures on measurable sets via `Measure.ext`.
  refine Measure.ext (fun A hA => ?_) 
  have hpre : (fun x => g * x) ⁻¹' A = g⁻¹ • A := by
    ext x
    constructor
    · intro hx
      refine ⟨g * x, hx, ?_⟩
      simp
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
  have hmeas_mul : Measurable fun x => g * x := by
    have hcont : Continuous fun x => g * x := by
      simpa using (continuous_const.mul continuous_id)
    simpa using hcont.measurable
  have hpre_meas : MeasurableSet ((fun x => g * x) ⁻¹' A) := hA.preimage hmeas_mul
  have hmeas_smul : MeasurableSet (g⁻¹ • A) := by
    simpa [hpre] using hpre_meas
  have hν_pre : ν ((fun x => g * x) ⁻¹' A) = μ.val (g⁻¹ • A) := by
    have := toMeasure_apply (μ := μ) (cox := cox) (h_sigma := h_sigma)
      (s := (fun x => g * x) ⁻¹' A) (hs := hpre_meas)
    simpa [ν, hpre] using this
  have hν_smul : ν (g⁻¹ • A) = μ.val (g⁻¹ • A) := by
    have := toMeasure_apply (μ := μ) (cox := cox) (h_sigma := h_sigma)
      (s := g⁻¹ • A) (hs := hmeas_smul)
    simpa [ν] using this
  have hν_A : ν A = μ.val A := by
    have := toMeasure_apply (μ := μ) (cox := cox) (h_sigma := h_sigma)
      (s := A) (hs := hA)
    simpa [ν] using this
  have hinv : μ.val (g⁻¹ • A) = μ.val A := h_trans.invariant g⁻¹ A
  calc
    Measure.map (fun x => g * x) ν A
        = ν ((fun x => g * x) ⁻¹' A) := Measure.map_apply hmeas_mul hA
    _ = μ.val (g⁻¹ • A) := hν_pre
    _ = μ.val A := hinv
    _ = ν A := hν_A.symm

end Mettapedia.MeasureTheory
