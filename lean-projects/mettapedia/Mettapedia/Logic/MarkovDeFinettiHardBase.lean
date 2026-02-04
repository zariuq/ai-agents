import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Markov de Finetti (Hard Direction) — Base Definitions

This file packages the shared analytic infrastructure used in the Markov de Finetti “hard
direction” (Diaconis–Freedman 1980):

* a compact parameter space `MarkovParam k` of time-homogeneous Markov chains on `Fin k`,
* the cylinder kernel `wordProb : MarkovParam k → List (Fin k) → ℝ≥0∞`,
* basic regularity (`Continuous`/`Measurable`) for `wordProb`,
* Stone–Weierstrass scaffolding: a separating coordinate subalgebra of `C(MarkovParam k, ℝ)`,
  and the fact that each `wordProb` polynomial lies in that subalgebra.

The actual representation theorem (Markov exchangeability ⇒ mixture of Markov chains) is proved
in `Mettapedia.Logic.MarkovDeFinettiHard`.  We keep this file independent so that auxiliary
constructions (evidence partitions, hyperpriors, etc.) can reuse the same parameter space without
import cycles.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators
open scoped NNReal ENNReal

open MeasureTheory

namespace MarkovDeFinettiHard

variable {k : ℕ}

/-!
## Parameter space for Markov chains on `Fin k`

We represent a Markov chain by:
* an initial distribution `init : ProbabilityMeasure (Fin k)`, and
* a transition kernel given by a row distribution `trans a : ProbabilityMeasure (Fin k)` for each
  state `a : Fin k`.

This is a finite product of compact spaces, hence compact (via `Prokhorov`), which is the right
setting for RMK.
-/

structure MarkovParam (k : ℕ) where
  init : MeasureTheory.ProbabilityMeasure (Fin k)
  trans : Fin k → MeasureTheory.ProbabilityMeasure (Fin k)

namespace MarkovParam

variable {k : ℕ}

def toProd (θ : MarkovParam k) :
    MeasureTheory.ProbabilityMeasure (Fin k) × (Fin k → MeasureTheory.ProbabilityMeasure (Fin k)) :=
  (θ.init, θ.trans)

def ofProd (p :
    MeasureTheory.ProbabilityMeasure (Fin k) × (Fin k → MeasureTheory.ProbabilityMeasure (Fin k))) :
    MarkovParam k :=
  ⟨p.1, p.2⟩

@[simp] lemma toProd_ofProd
    (p : MeasureTheory.ProbabilityMeasure (Fin k) × (Fin k → MeasureTheory.ProbabilityMeasure (Fin k))) :
    toProd (ofProd (k := k) p) = p := by
  cases p
  rfl

@[simp] lemma ofProd_toProd (θ : MarkovParam k) : ofProd (k := k) (toProd θ) = θ := by
  cases θ
  rfl

instance : TopologicalSpace (MarkovParam k) :=
  TopologicalSpace.induced (toProd (k := k)) inferInstance

lemma continuous_toProd : Continuous (toProd (k := k)) :=
  continuous_induced_dom

lemma continuous_ofProd : Continuous (ofProd (k := k)) := by
  have : Continuous ((toProd (k := k)) ∘ (ofProd (k := k))) := by
    simpa using
      (continuous_id :
        Continuous (fun p :
          MeasureTheory.ProbabilityMeasure (Fin k) × (Fin k → MeasureTheory.ProbabilityMeasure (Fin k)) =>
            p))
  exact (continuous_induced_rng (f := toProd (k := k)) (g := ofProd (k := k))).2 this

noncomputable def homeomorphProd :
    MarkovParam k ≃ₜ
      (MeasureTheory.ProbabilityMeasure (Fin k) × (Fin k → MeasureTheory.ProbabilityMeasure (Fin k))) :=
{ toEquiv :=
  { toFun := toProd (k := k)
    invFun := ofProd (k := k)
    left_inv := by intro θ; simp
    right_inv := by intro p; simp }
  continuous_toFun := continuous_toProd (k := k)
  continuous_invFun := continuous_ofProd (k := k) }

instance : CompactSpace (MarkovParam k) :=
  (homeomorphProd (k := k)).symm.compactSpace

instance : T2Space (MarkovParam k) :=
  (homeomorphProd (k := k)).symm.t2Space

/-!
We intentionally take the measurable sets on `MarkovParam k` to be the Borel sets of its compact
topology. This avoids relying on any `BorelSpace` instances for `ProbabilityMeasure` itself, which
Mathlib does not currently provide in general.
-/
instance : MeasurableSpace (MarkovParam k) := borel (MarkovParam k)
instance : BorelSpace (MarkovParam k) := ⟨rfl⟩

end MarkovParam

/-- One-step transition probability `P(b | a)` under a Markov parameter. -/
def stepProb (θ : MarkovParam k) (a b : Fin k) : ℝ≥0 :=
  θ.trans a (Set.singleton b)

/-- Initial probability `P(a)` under a Markov parameter. -/
def initProb (θ : MarkovParam k) (a : Fin k) : ℝ≥0 :=
  θ.init (Set.singleton a)

/-- Tail probability: given current state `a`, probability of a suffix `xs` under `θ`. -/
def wordProbAux (θ : MarkovParam k) (a : Fin k) : List (Fin k) → ℝ≥0
  | [] => 1
  | b :: xs => stepProb (k := k) θ a b * wordProbAux θ b xs

/-- Probability of a finite word under a Markov parameter, as an `ℝ≥0` number. -/
def wordProbNN (θ : MarkovParam k) : List (Fin k) → ℝ≥0
  | [] => 1
  | a :: xs => initProb (k := k) θ a * wordProbAux (k := k) θ a xs

-- The same probability, coerced to `ℝ≥0∞` for use with `lintegral`/mixture measures.
def wordProb (θ : MarkovParam k) (xs : List (Fin k)) : ℝ≥0∞ :=
  (wordProbNN (k := k) θ xs : ℝ≥0∞)

/-! ## Basic regularity: continuity/measurability of the cylinder kernels -/

private lemma continuous_apply_singleton_enn (b : Fin k) :
    Continuous (fun μ : MeasureTheory.ProbabilityMeasure (Fin k) =>
      ((μ : Measure (Fin k)) (Set.singleton b))) := by
  classical
  -- View `μ {b}` as the integral of the continuous indicator `1_{ {b} }`.
  let f : C(Fin k, ℝ≥0) :=
    { toFun := fun x => if x = b then 1 else 0
      continuous_toFun := by
        simpa using continuous_of_discreteTopology }
  have hcont :
      Continuous (fun μ : MeasureTheory.ProbabilityMeasure (Fin k) =>
        ∫⁻ x, f x ∂(μ : Measure (Fin k))) :=
    MeasureTheory.ProbabilityMeasure.continuous_lintegral_continuousMap (X := Fin k) (f := f)
  have hEq :
      (fun μ : MeasureTheory.ProbabilityMeasure (Fin k) => ∫⁻ x, f x ∂(μ : Measure (Fin k))) =
        fun μ : MeasureTheory.ProbabilityMeasure (Fin k) => ((μ : Measure (Fin k)) (Set.singleton b)) := by
    funext μ
    have hs : MeasurableSet (Set.singleton b) := by simp
    have hf :
        (fun x : Fin k => (f x : ℝ≥0∞)) = (Set.singleton b).indicator (1 : Fin k → ℝ≥0∞) := by
      funext x
      by_cases hxb : x = b
      · subst hxb
        have hx : x ∈ (Set.singleton x : Set (Fin k)) := rfl
        simp [f, Set.indicator, hx]
      · have hxnot : x ∉ Set.singleton b := fun hx => hxb hx
        simp [f, hxb, Set.indicator, hxnot]
    simp [hf, MeasureTheory.lintegral_indicator_one hs]
  simpa [hEq] using hcont

private lemma continuous_apply_singleton (b : Fin k) :
    Continuous (fun μ : MeasureTheory.ProbabilityMeasure (Fin k) => μ (Set.singleton b)) := by
  classical
  -- The `ProbabilityMeasure` evaluation is `ENNReal.toNNReal` of the underlying `Measure`.
  have henn :
      Continuous (fun μ : MeasureTheory.ProbabilityMeasure (Fin k) =>
        ((μ : Measure (Fin k)) (Set.singleton b))) :=
    continuous_apply_singleton_enn (k := k) b
  -- Use that `ENNReal.toNNReal` is continuous at finite values.
  have hnn :
      Continuous (fun μ : MeasureTheory.ProbabilityMeasure (Fin k) =>
        ((μ : Measure (Fin k)) (Set.singleton b)).toNNReal) := by
    refine continuous_iff_continuousAt.2 ?_
    intro μ
    have hμfin : ((μ : Measure (Fin k)) (Set.singleton b)) ≠ (∞ : ℝ≥0∞) := by
      simp
    exact (ENNReal.tendsto_toNNReal hμfin).comp (henn.tendsto μ)
  simpa [MeasureTheory.ProbabilityMeasure.coeFn_def] using hnn

private lemma continuous_initProb (a : Fin k) :
    Continuous (fun θ : MarkovParam k => initProb (k := k) θ a) := by
  -- `θ ↦ θ.init` is continuous (as a coordinate projection through `toProd`).
  have hθ : Continuous (fun θ : MarkovParam k => θ.init) := by
    simpa [MarkovParam.toProd] using (continuous_fst.comp (MarkovParam.continuous_toProd (k := k)))
  exact (continuous_apply_singleton (k := k) a).comp hθ

private lemma continuous_stepProb (a b : Fin k) :
    Continuous (fun θ : MarkovParam k => stepProb (k := k) θ a b) := by
  have hθ : Continuous (fun θ : MarkovParam k => θ.trans a) := by
    -- `θ.trans a` is the composite of `toProd` with the second projection and evaluation at `a`.
    have :
        Continuous (fun θ :
          MarkovParam k => (MarkovParam.toProd (k := k) θ).2 a) := by
      exact (continuous_apply a).comp (continuous_snd.comp (MarkovParam.continuous_toProd (k := k)))
    simpa [MarkovParam.toProd] using this
  exact (continuous_apply_singleton (k := k) b).comp hθ

private lemma continuous_wordProbAux (a : Fin k) :
    ∀ xs : List (Fin k), Continuous (fun θ : MarkovParam k => wordProbAux (k := k) θ a xs) := by
  intro xs
  induction xs generalizing a with
  | nil =>
      simpa [wordProbAux] using (continuous_const : Continuous (fun _θ : MarkovParam k => (1 : ℝ≥0)))
  | cons b xs ih =>
      -- `wordProbAux θ a (b :: xs) = stepProb θ a b * wordProbAux θ b xs`
      simpa [wordProbAux] using
        (continuous_stepProb (k := k) a b).mul (ih (a := b))

theorem continuous_wordProbNN :
    ∀ xs : List (Fin k), Continuous (fun θ : MarkovParam k => wordProbNN (k := k) θ xs) := by
  intro xs
  cases xs with
  | nil =>
      simpa [wordProbNN] using (continuous_const : Continuous (fun _θ : MarkovParam k => (1 : ℝ≥0)))
  | cons a xs =>
      -- `wordProbNN θ (a :: xs) = initProb θ a * wordProbAux θ a xs`
      simpa [wordProbNN] using
        (continuous_initProb (k := k) a).mul (continuous_wordProbAux (k := k) (a := a) xs)

theorem continuous_wordProb :
    ∀ xs : List (Fin k), Continuous (fun θ : MarkovParam k => wordProb (k := k) θ xs) := by
  intro xs
  -- Coercion `ℝ≥0 → ℝ≥0∞` is continuous.
  exact ENNReal.continuous_coe.comp (continuous_wordProbNN (k := k) xs)

theorem measurable_wordProb (xs : List (Fin k)) :
    Measurable (fun θ : MarkovParam k => wordProb (k := k) θ xs) :=
  (continuous_wordProb (k := k) xs).measurable

/-!
## Point-separation (Stone–Weierstrass scaffolding)

To follow the `HausdorffMoment.lean` playbook, the hard direction will likely construct a positive
linear functional on a dense subalgebra of `C(MarkovParam k, ℝ)`.  The key density input is the
Stone–Weierstrass theorem, which requires a separating family of continuous coordinates.

Here we record the (easy) point-separation lemma: two distinct Markov parameters differ on some
singleton cylinder probability.
-/

private lemma exists_singleton_ne_of_ne
    {μ ν : MeasureTheory.ProbabilityMeasure (Fin k)} (hμν : μ ≠ ν) :
    ∃ b : Fin k, μ (Set.singleton b) ≠ ν (Set.singleton b) := by
  classical
  -- If all singleton masses agree, the measures agree (via `toPMF`).
  by_contra h
  push_neg at h
  have hENN : ∀ b : Fin k, ((μ : Measure (Fin k)) (Set.singleton b)) = ((ν : Measure (Fin k)) (Set.singleton b)) := by
    intro b
    have h' : ((μ : Measure (Fin k)) (Set.singleton b)).toNNReal =
        ((ν : Measure (Fin k)) (Set.singleton b)).toNNReal := by
      simpa using h b
    exact
      (ENNReal.toNNReal_eq_toNNReal_iff'
          (measure_ne_top (μ := (μ : Measure (Fin k))) (Set.singleton b))
          (measure_ne_top (μ := (ν : Measure (Fin k))) (Set.singleton b))).1 h'
  have hpmf :
      MeasureTheory.Measure.toPMF (μ := (μ : Measure (Fin k)))
          = MeasureTheory.Measure.toPMF (μ := (ν : Measure (Fin k))) := by
    ext b
    simpa [MeasureTheory.Measure.toPMF_apply] using hENN b
  have hmeas : (μ : Measure (Fin k)) = (ν : Measure (Fin k)) := by
    -- Convert equality of PMFs back to equality of measures.
    calc
      (μ : Measure (Fin k))
          = (MeasureTheory.Measure.toPMF (μ := (μ : Measure (Fin k)))).toMeasure := by
              simp
      _ = (MeasureTheory.Measure.toPMF (μ := (ν : Measure (Fin k)))).toMeasure := by
            simp [hpmf]
      _ = (ν : Measure (Fin k)) := by
            simp
  exact hμν (MeasureTheory.ProbabilityMeasure.toMeasure_injective hmeas)

private lemma exists_coord_ne_of_ne (θ₁ θ₂ : MarkovParam k) (hθ : θ₁ ≠ θ₂) :
    (∃ a : Fin k, initProb (k := k) θ₁ a ≠ initProb (k := k) θ₂ a) ∨
      ∃ a b : Fin k, stepProb (k := k) θ₁ a b ≠ stepProb (k := k) θ₂ a b := by
  classical
  -- Either the initial distributions differ, or some transition row differs.
  by_cases hinit : θ₁.init = θ₂.init
  · right
    have htrans : θ₁.trans ≠ θ₂.trans := by
      intro htrans_eq
      apply hθ
      cases θ₁
      cases θ₂
      cases hinit
      cases htrans_eq
      rfl
    -- Pick a row `a` where the row measures differ, then a column `b`.
    have : ∃ a : Fin k, θ₁.trans a ≠ θ₂.trans a := by
      classical
      -- Otherwise, `θ₁.trans = θ₂.trans` by function ext, contradicting `htrans`.
      by_contra hall
      apply htrans
      funext a
      have : ¬θ₁.trans a ≠ θ₂.trans a := by
        intro hne
        apply hall
        exact ⟨a, hne⟩
      exact (not_ne_iff.mp this)
    rcases this with ⟨a, ha⟩
    rcases exists_singleton_ne_of_ne (k := k) ha with ⟨b, hb⟩
    refine ⟨a, b, ?_⟩
    simpa [stepProb] using hb
  · left
    rcases exists_singleton_ne_of_ne (k := k) hinit with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    simpa [initProb] using ha

/-!
## Coordinate functions and a separating subalgebra

We package the basic coordinate maps into continuous functions on `MarkovParam k`, then build
the subalgebra they generate.  This is the Stone–Weierstrass input.
-/

private def initCoord (a : Fin k) : C(MarkovParam k, ℝ) :=
  { toFun := fun θ => (initProb (k := k) θ a : ℝ)
    continuous_toFun := by
      simpa using (NNReal.continuous_coe.comp (continuous_initProb (k := k) a)) }

private def stepCoord (a b : Fin k) : C(MarkovParam k, ℝ) :=
  { toFun := fun θ => (stepProb (k := k) θ a b : ℝ)
    continuous_toFun := by
      simpa using (NNReal.continuous_coe.comp (continuous_stepProb (k := k) a b)) }

private def coordSet : Set C(MarkovParam k, ℝ) :=
  {f | ∃ a : Fin k, f = initCoord (k := k) a} ∪
    {f | ∃ a b : Fin k, f = stepCoord (k := k) a b}

noncomputable def coordSubalg : Subalgebra ℝ C(MarkovParam k, ℝ) :=
  Algebra.adjoin ℝ (coordSet (k := k))

lemma initCoord_mem_coordSubalg (a : Fin k) : initCoord (k := k) a ∈ coordSubalg (k := k) := by
  -- `initCoord a` is in the generating set.
  have hsubset : coordSet (k := k) ⊆ Algebra.adjoin ℝ (coordSet (k := k)) :=
    (Algebra.gc.le_u_l (coordSet (k := k)))
  exact hsubset (Or.inl ⟨a, rfl⟩)

lemma stepCoord_mem_coordSubalg (a b : Fin k) :
    stepCoord (k := k) a b ∈ coordSubalg (k := k) := by
  have hsubset : coordSet (k := k) ⊆ Algebra.adjoin ℝ (coordSet (k := k)) :=
    (Algebra.gc.le_u_l (coordSet (k := k)))
  exact hsubset (Or.inr ⟨a, b, rfl⟩)

lemma coordSubalg_separatesPoints : (coordSubalg (k := k)).SeparatesPoints := by
  classical
  intro θ₁ θ₂ hne
  rcases exists_coord_ne_of_ne (k := k) θ₁ θ₂ hne with h | h
  · rcases h with ⟨a, ha⟩
    refine ⟨(initCoord (k := k) a : MarkovParam k → ℝ), ?_, ?_⟩
    ·
      have hsubset : coordSet (k := k) ⊆ Algebra.adjoin ℝ (coordSet (k := k)) :=
        (Algebra.gc.le_u_l (coordSet (k := k)))
      refine ⟨initCoord (k := k) a, ?_, rfl⟩
      exact hsubset (Or.inl ⟨a, rfl⟩)
    · intro h'
      apply ha
      exact NNReal.coe_injective h'
  · rcases h with ⟨a, b, hb⟩
    refine ⟨(stepCoord (k := k) a b : MarkovParam k → ℝ), ?_, ?_⟩
    ·
      have hsubset : coordSet (k := k) ⊆ Algebra.adjoin ℝ (coordSet (k := k)) :=
        (Algebra.gc.le_u_l (coordSet (k := k)))
      refine ⟨stepCoord (k := k) a b, ?_, rfl⟩
      exact hsubset (Or.inr ⟨a, b, rfl⟩)
    · intro h'
      apply hb
      exact NNReal.coe_injective h'

lemma coordSubalg_topologicalClosure_eq_top :
    (coordSubalg (k := k)).topologicalClosure = ⊤ := by
  simpa using
    (ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
      (A := coordSubalg (k := k))
      (w := coordSubalg_separatesPoints (k := k)))

/-!
## Word-probability functions lie in the coordinate subalgebra

This will let us interpret cylinder probabilities as evaluations of elements of `coordSubalg`.
-/

def wordProbAuxReal (a : Fin k) : List (Fin k) → C(MarkovParam k, ℝ)
  | [] =>
      (1 : C(MarkovParam k, ℝ))
  | b :: xs =>
      (stepCoord (k := k) a b) * wordProbAuxReal b xs

def wordProbReal : List (Fin k) → C(MarkovParam k, ℝ)
  | [] => (1 : C(MarkovParam k, ℝ))
  | a :: xs => (initCoord (k := k) a) * wordProbAuxReal (k := k) a xs

/-! ## Relating `wordProbReal` to `wordProbNN` -/

lemma wordProbAuxReal_apply (a : Fin k) (xs : List (Fin k)) (θ : MarkovParam k) :
    wordProbAuxReal (k := k) a xs θ = (wordProbAux (k := k) θ a xs : ℝ) := by
  induction xs generalizing a with
  | nil =>
      simp [wordProbAuxReal, wordProbAux]
  | cons b xs ih =>
      -- unfold both sides and use induction
      simp [wordProbAuxReal, wordProbAux, ih, stepCoord, stepProb, NNReal.coe_mul]

lemma wordProbReal_apply (xs : List (Fin k)) (θ : MarkovParam k) :
    wordProbReal (k := k) xs θ = (wordProbNN (k := k) θ xs : ℝ) := by
  cases xs with
  | nil =>
      simp [wordProbReal, wordProbNN]
  | cons a xs =>
      -- unfold and use `wordProbAuxReal_apply`
      simp [wordProbReal, wordProbNN, initCoord, initProb, wordProbAuxReal_apply, NNReal.coe_mul]

private lemma wordProbAuxReal_mem_coordSubalg (a : Fin k) :
    ∀ xs, wordProbAuxReal (k := k) a xs ∈ coordSubalg (k := k) := by
  intro xs
  induction xs generalizing a with
  | nil =>
      change (1 : C(MarkovParam k, ℝ)) ∈ coordSubalg (k := k)
      exact (coordSubalg (k := k)).one_mem
  | cons b xs ih =>
      -- product of step coordinate and inductive term
      have hb : stepCoord (k := k) a b ∈ coordSubalg (k := k) :=
        stepCoord_mem_coordSubalg (k := k) a b
      simpa [wordProbAuxReal] using (coordSubalg (k := k)).mul_mem hb (ih (a := b))

lemma wordProbReal_mem_coordSubalg :
    ∀ xs, wordProbReal (k := k) xs ∈ coordSubalg (k := k) := by
  intro xs
  cases xs with
  | nil =>
      change (1 : C(MarkovParam k, ℝ)) ∈ coordSubalg (k := k)
      exact (coordSubalg (k := k)).one_mem
  | cons a xs =>
      have ha : initCoord (k := k) a ∈ coordSubalg (k := k) :=
        initCoord_mem_coordSubalg (k := k) a
      have haux : wordProbAuxReal (k := k) a xs ∈ coordSubalg (k := k) :=
        wordProbAuxReal_mem_coordSubalg (k := k) (a := a) xs
      simpa [wordProbReal] using (coordSubalg (k := k)).mul_mem ha haux

end MarkovDeFinettiHard

end Mettapedia.Logic
