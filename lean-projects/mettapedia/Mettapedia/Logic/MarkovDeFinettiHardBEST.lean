import Mettapedia.Logic.MarkovDeFinettiHardEuler
import Mettapedia.Logic.MarkovDeFinettiHardBESTCore
import Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
import Mettapedia.Logic.MarkovDeFinettiHardEmpirical

/-! LLM primer:
- `MarkovState k` encodes (start : Fin k, counts : TransCounts k).
- `fiber k N eN` = trajectories of length N whose `stateOfTraj` = eN.
- The BEST theorem: #EulerTrails = #arborescences(root) × ∏_{v} (outdeg(v) - 1)!

Status: The main theorem `excursion_bound_from_decomposition` reduces to a single
sorry `excursion_wor_wr_core`. This sorry IS the Diaconis-Freedman core lemma:
for states with many returns, |W(empiricalParam) - prefixCoeff| ≤ 4n²/R.
Proving it requires the BEST theorem for Euler trail counting.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHardBEST

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiHardEuler
open Mettapedia.Logic.MarkovDeFinettiHard
open Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
open Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacementModel
open Mettapedia.Logic.MarkovDeFinettiHardExcursions
open Mettapedia.Logic.MarkovDeFinettiHardBESTCore
open Mettapedia.Logic.EvidenceDirichlet

variable {k : ℕ}

/-! ## Excursion-count helpers -/

lemma excursionListOfTraj_length {n : ℕ} (xs : Traj k n) :
    (excursionListOfTraj (k := k) xs).length = numExcursions (k := k) xs := by
  simp [excursionListOfTraj, excursionsOfTraj, length_excursionPairs]

lemma excursionMultiset_card_eq_numExcursions {n : ℕ} (xs : Traj k n) :
    (excursionMultiset (k := k) (excursionListOfTraj (k := k) xs)).card =
      numExcursions (k := k) xs := by
  simp [excursionMultiset, excursionListOfTraj_length]

/-- Number of excursions in the first `n` transitions of a trajectory. -/
def prefixExcursionCount {n N : ℕ} (hN : n ≤ N) (xs : Traj k N) : ℕ :=
  numExcursions (k := k) (trajPrefix (k := k) hN xs)

lemma prefixExcursionCount_le_n {n N : ℕ} (hN : n ≤ N) (xs : Traj k N) :
    prefixExcursionCount (k := k) hN xs ≤ n := by
  unfold prefixExcursionCount numExcursions
  have hcard : (returnPositions (k := k) (trajPrefix (k := k) hN xs)).card ≤ n + 1 := by
    have := Finset.card_le_univ (returnPositions (k := k) (trajPrefix (k := k) hN xs))
    simpa [Fintype.card_fin] using this
  omega

/-- The excursion list of any trajectory in the fiber of `s` has length
`returnsToStart s`. -/
lemma excursionList_length_eq_returnsToStart
    {N : ℕ} (s : MarkovState k) (xs : Traj k N) (hxs : xs ∈ fiber k N s) :
    (excursionListOfTraj (k := k) xs).length = returnsToStart (k := k) s := by
  have h1 := excursionListOfTraj_length (k := k) xs
  have h2 := numExcursions_eq_returnsToStart (k := k) xs
  have h3 : stateOfTraj (k := k) xs = s := (Finset.mem_filter.1 hxs).2
  rw [h1, h2, h3]

/-! ## Empirical parameter step probability -/

/-- `empiricalStepProb` is nonneg. -/
lemma empiricalStepProb_nonneg' (hk : 0 < k) (c : TransCounts k) (a b : Fin k) :
    0 ≤ empiricalStepProb (k := k) hk c a b := by
  unfold empiricalStepProb
  apply div_nonneg
  · have h1 : 0 ≤ (c.counts a b : ℝ) := by exact_mod_cast Nat.zero_le _
    have h2 : 0 ≤ (DirichletParams.uniformPrior (k := k)).priorParams b := by
      simp [DirichletParams.uniformPrior, DirichletParams.uniform]
    linarith
  · have h1 : 0 ≤ (c.rowTotal a : ℝ) := by exact_mod_cast Nat.zero_le _
    have h2 : 0 < (DirichletParams.uniformPrior (k := k)).totalConcentration :=
      DirichletParams.totalConcentration_pos (k := k) (p := DirichletParams.uniformPrior) hk
    linarith

/-- `stepProb` of the empirical parameter equals the Laplace-smoothed empirical probability,
cast to NNReal. -/
lemma stepProb_empiricalParam (hk : 0 < k) (s : MarkovState k) (a b : Fin k) :
    (stepProb (k := k) (empiricalParam (k := k) hk s) a b : ℝ) =
      empiricalStepProb (k := k) hk s.counts a b := by
  unfold stepProb empiricalParam empiricalRowMeasure
  dsimp only []
  rw [MeasureTheory.ProbabilityMeasure.mk_apply]
  have hsingle :
      (empiricalRowPMF (k := k) hk s.counts a).toMeasure (Set.singleton b) =
        empiricalRowPMF (k := k) hk s.counts a b := by
    exact PMF.toMeasure_apply_singleton
      (p := empiricalRowPMF (k := k) hk s.counts a)
      (a := b)
      (h := measurableSet_singleton b)
  rw [hsingle]
  simp only [empiricalRowPMF, PMF.ofFinset_apply]
  rw [ENNReal.coe_toNNReal_eq_toReal]
  exact ENNReal.toReal_ofReal (empiricalStepProb_nonneg' hk s.counts a b)

/-! ## wordProbNN of empiricalParam on fiber members -/

/-- For any trajectory `xs` in `fiber(N, s)`, `wordProbNN(empiricalParam(s), xs)` depends
only on `s` (not the choice of `xs`), since `wordProbNN` is constant on fibers. -/
lemma wordProbNN_empiricalParam_const_on_fiber
    (hk : 0 < k) {N : ℕ} (s : MarkovState k) {xs ys : Traj k N}
    (hxs : xs ∈ fiber k N s) (hys : ys ∈ fiber k N s) :
    wordProbNN (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) xs) =
      wordProbNN (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys) := by
  have hstate_xs : stateOfTraj (k := k) xs = s := (Finset.mem_filter.1 hxs).2
  have hstate_ys : stateOfTraj (k := k) ys = s := (Finset.mem_filter.1 hys).2
  exact wordProbNN_const_on_state_fiber (k := k) (empiricalParam (k := k) hk s)
    (by rw [hstate_xs, hstate_ys])

/-- `W(N, s, θ) = |fiber(N, s)| × wordProb(θ, xs₀)` for any `xs₀ ∈ fiber(N, s)`,
since `wordProb` is constant on the fiber. -/
lemma W_eq_card_mul_wordProb_of_mem_fiber
    {N : ℕ} (θ : MarkovParam k) (s : MarkovState k)
    (xs₀ : Traj k N) (hxs₀ : xs₀ ∈ fiber k N s) :
    W (k := k) N s θ =
      (fiber k N s).card *
        wordProb (k := k) θ (trajToList (k := k) xs₀) := by
  classical
  simp only [W]
  have hfib : (trajFinset k N).filter (fun xs => stateOfTraj (k := k) xs = s) = fiber k N s := rfl
  rw [hfib]
  have hconst : ∀ xs ∈ fiber k N s,
      wordProb (k := k) θ (trajToList (k := k) xs) =
        wordProb (k := k) θ (trajToList (k := k) xs₀) := by
    intro xs hxs
    exact wordProb_const_on_state_fiber (k := k) θ
      (by rw [(Finset.mem_filter.1 hxs).2, (Finset.mem_filter.1 hxs₀).2])
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]
  simp [nsmul_eq_mul]

/-! ## Pattern index set `P(n,e,s)` and decomposition identities -/

/-- Finite excursion-prefix pattern set `P(n,e,s)`.

It includes:
1. patterns coming from long-horizon prefix fibers (`prefixFiber(hN,e,s)`), and
2. all short-horizon WR patterns in `fiber(n+1,e)`.

This shared index set lets the WOR and WR decompositions range over one finite
carrier; WR then has no residual term outside `P`. -/
def excursionPatternSet
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) : Finset (ExcursionList k) :=
  ((prefixFiber (k := k) (h := hN) e s).image
    (fun xs => excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs))) ∪
  ((fiber k (Nat.succ n) e).image
    (fun ys => excursionListOfTraj (k := k) ys))

/-- The `p`-fiber inside `prefixFiber(hN,e,s)`. -/
def prefixPatternFiber
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) :
    Finset (Traj k N) :=
  (prefixFiber (k := k) (h := hN) e s).filter
    (fun xs => excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = p)

/-- WOR-side mass for pattern `p`: cardinality ratio in the long-horizon fiber. -/
def worPatternMass
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) : ENNReal :=
  ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
    ((fiber k N s).card : ENNReal)

/-- WR-side mass for pattern `p`: indicator-sum over short trajectories in `fiber(n+1,e)`. -/
def wrPatternMass
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k) : ENNReal :=
  ∑ ys ∈ fiber k (Nat.succ n) e,
    if excursionListOfTraj (k := k) ys = p then
      wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys)
    else 0

/-- WR residual mass outside `P(n,e,s)`. -/
def wrResidualMass
    {N : ℕ} (hk : 0 < k) (n : ℕ) (hN : Nat.succ n ≤ N) (e s : MarkovState k) : ENNReal :=
  ∑ ys ∈ fiber k (Nat.succ n) e,
    if excursionListOfTraj (k := k) ys ∈ excursionPatternSet (k := k) (hN := hN) e s then
      0
    else
      wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys)

lemma sum_worPatternMass_eq_prefixCoeff
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      worPatternMass (k := k) (hN := hN) e s p =
        prefixCoeff (k := k) (h := hN) e s := by
  classical
  let P₀ : Finset (ExcursionList k) :=
    (prefixFiber (k := k) (h := hN) e s).image
      (fun xs => excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs))
  let P : Finset (ExcursionList k) := excursionPatternSet (k := k) (hN := hN) e s
  have hcard : (fiber k N s).card ≠ 0 :=
    fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := s) hs
  have hcard_pf0 :
      (prefixFiber (k := k) (h := hN) e s).card =
        ∑ p ∈ P₀,
          (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
    simpa [P₀, prefixPatternFiber] using
      (Finset.card_eq_sum_card_image
        (f := fun xs : Traj k N =>
          excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs))
        (s := prefixFiber (k := k) (h := hN) e s))
  have hsubset : P₀ ⊆ P := by
    intro p hp
    exact Finset.mem_union.2 (Or.inl hp)
  have hzero_out :
      ∀ p ∈ P, p ∉ P₀ →
        (prefixPatternFiber (k := k) (hN := hN) e s p).card = 0 := by
    intro p hpP hpNot
    have hempty :
        prefixPatternFiber (k := k) (hN := hN) e s p = ∅ := by
      ext xs
      constructor
      · intro hxs
        have hx : excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = p :=
          (Finset.mem_filter.1 hxs).2
        have hxP0 : p ∈ P₀ := by
          refine Finset.mem_image.2 ?_
          exact ⟨xs, (Finset.mem_filter.1 hxs).1, hx⟩
        exact False.elim (hpNot hxP0)
      · intro hxs
        simp at hxs
    simp [hempty]
  have hcard_pf :
      (prefixFiber (k := k) (h := hN) e s).card =
        ∑ p ∈ P, (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
    calc
      (prefixFiber (k := k) (h := hN) e s).card
          = ∑ p ∈ P₀, (prefixPatternFiber (k := k) (hN := hN) e s p).card := hcard_pf0
      _ = ∑ p ∈ P, (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
          have hsum :
              ∑ p ∈ P₀, (prefixPatternFiber (k := k) (hN := hN) e s p).card =
                ∑ p ∈ P, (prefixPatternFiber (k := k) (hN := hN) e s p).card :=
            Finset.sum_subset hsubset hzero_out
          simpa using hsum
  calc
    ∑ p ∈ P,
      worPatternMass (k := k) (hN := hN) e s p
        = (((∑ p ∈ P,
              (prefixPatternFiber (k := k) (hN := hN) e s p).card) : ℕ) : ENNReal) /
            ((fiber k N s).card : ENNReal) := by
              simp [worPatternMass, div_eq_mul_inv, Finset.sum_mul]
    _ = (((prefixFiber (k := k) (h := hN) e s).card : ℕ) : ENNReal) /
          ((fiber k N s).card : ENNReal) := by
          rw [hcard_pf]
    _ = prefixCoeff (k := k) (h := hN) e s := by
          simp [prefixCoeff, hcard]

lemma wrResidualMass_eq_zero
    {N : ℕ} (hk : 0 < k) (n : ℕ) (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    wrResidualMass (k := k) hk n hN e s = 0 := by
  classical
  let P : Finset (ExcursionList k) := excursionPatternSet (k := k) (hN := hN) e s
  have hmem :
      ∀ ys ∈ fiber k (Nat.succ n) e,
        excursionListOfTraj (k := k) ys ∈ P := by
    intro ys hys
    exact Finset.mem_union.2 (Or.inr <|
      Finset.mem_image.2 ⟨ys, hys, rfl⟩
    )
  unfold wrResidualMass
  refine Finset.sum_eq_zero ?_
  intro ys hys
  have hyP : excursionListOfTraj (k := k) ys ∈ excursionPatternSet (k := k) (hN := hN) e s :=
    hmem ys hys
  simp [hyP]

lemma sum_wrPatternMass_add_residual_eq_W
    {N : ℕ} (hk : 0 < k) (n : ℕ) (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        wrPatternMass (k := k) hk n e s p) +
      wrResidualMass (k := k) hk n hN e s =
      W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) := by
  classical
  let θ := empiricalParam (k := k) hk s
  let P := excursionPatternSet (k := k) (hN := hN) e s
  have hmain :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          wrPatternMass (k := k) hk n e s p
        =
      ∑ ys ∈ fiber k (Nat.succ n) e,
        if excursionListOfTraj (k := k) ys ∈ P then
          wordProb (k := k) θ (trajToList (k := k) ys)
        else 0 := by
    calc
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          wrPatternMass (k := k) hk n e s p
          =
        ∑ p ∈ P, ∑ ys ∈ fiber k (Nat.succ n) e,
          if excursionListOfTraj (k := k) ys = p then
            wordProb (k := k) θ (trajToList (k := k) ys) else 0 := by
            simp [wrPatternMass, P, θ]
      _ =
        ∑ ys ∈ fiber k (Nat.succ n) e, ∑ p ∈ P,
          if excursionListOfTraj (k := k) ys = p then
            wordProb (k := k) θ (trajToList (k := k) ys) else 0 := by
            rw [Finset.sum_comm]
      _ =
        ∑ ys ∈ fiber k (Nat.succ n) e,
          if excursionListOfTraj (k := k) ys ∈ P then
            wordProb (k := k) θ (trajToList (k := k) ys) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro ys hys
            by_cases hp : excursionListOfTraj (k := k) ys ∈ P
            · have hone :
                ∑ p ∈ P,
                    (if excursionListOfTraj (k := k) ys = p then
                      wordProb (k := k) θ (trajToList (k := k) ys) else 0) =
                  wordProb (k := k) θ (trajToList (k := k) ys) := by
                rw [Finset.sum_eq_single (excursionListOfTraj (k := k) ys)]
                · simp
                · intro p hpP hpneq
                  simp [eq_comm, hpneq]
                · intro hnotin
                  exact (hnotin hp).elim
              simp [hp, hone]
            · have hzero :
                ∑ p ∈ P,
                    (if excursionListOfTraj (k := k) ys = p then
                      wordProb (k := k) θ (trajToList (k := k) ys) else 0) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro p hpP
                have hneq : excursionListOfTraj (k := k) ys ≠ p := by
                  intro heq
                  exact hp (heq ▸ hpP)
                simp [hneq]
              simp [hp, hzero]
  calc
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        wrPatternMass (k := k) hk n e s p) +
      wrResidualMass (k := k) hk n hN e s
        =
      (∑ ys ∈ fiber k (Nat.succ n) e,
        if excursionListOfTraj (k := k) ys ∈ P then
          wordProb (k := k) θ (trajToList (k := k) ys) else 0) +
      ∑ ys ∈ fiber k (Nat.succ n) e,
        if excursionListOfTraj (k := k) ys ∈ P then 0 else
          wordProb (k := k) θ (trajToList (k := k) ys) := by
          simpa [wrResidualMass, P, θ] using congrArg (fun z => z + wrResidualMass (k := k) hk n hN e s) hmain
    _ =
      ∑ ys ∈ fiber k (Nat.succ n) e,
        ((if excursionListOfTraj (k := k) ys ∈ P then
            wordProb (k := k) θ (trajToList (k := k) ys) else 0) +
          (if excursionListOfTraj (k := k) ys ∈ P then 0 else
            wordProb (k := k) θ (trajToList (k := k) ys))) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ ys ∈ fiber k (Nat.succ n) e, wordProb (k := k) θ (trajToList (k := k) ys) := by
          refine Finset.sum_congr rfl ?_
          intro ys hys
          by_cases hp : excursionListOfTraj (k := k) ys ∈ P <;> simp [hp]
    _ = W (k := k) (Nat.succ n) e θ := by
          simp [W, fiber, Nat.succ_eq_add_one]

lemma sum_wrPatternMass_eq_W
    {N : ℕ} (hk : 0 < k) (n : ℕ) (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      wrPatternMass (k := k) hk n e s p =
        W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) := by
  have h := sum_wrPatternMass_add_residual_eq_W (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
  have hres0 := wrResidualMass_eq_zero (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
  simpa [hres0] using h

lemma worPatternMass_toReal_nonneg
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) :
    0 ≤ (worPatternMass (k := k) (hN := hN) e s p).toReal := by
  exact ENNReal.toReal_nonneg

lemma wrPatternMass_toReal_nonneg
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k) :
    0 ≤ (wrPatternMass (k := k) hk n e s p).toReal := by
  exact ENNReal.toReal_nonneg

lemma abs_sum_wrPatternMass_toReal_sub_sum_worPatternMass_toReal_le
    {n N : ℕ} (hk : 0 < k) (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    |(∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        ((wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal))| ≤
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| := by
  simpa using
    (Finset.abs_sum_le_sum_abs
      (f := fun p =>
        (wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal)
      (s := excursionPatternSet (k := k) (hN := hN) e s))

lemma wrPatternMass_ne_top
    {n : ℕ} (hk : 0 < k) (e s : MarkovState k) (p : ExcursionList k) :
    wrPatternMass (k := k) hk n e s p ≠ ⊤ := by
  classical
  unfold wrPatternMass
  refine (ENNReal.sum_ne_top).2 ?_
  intro ys hys
  by_cases hp : excursionListOfTraj (k := k) ys = p
  · simp [hp, wordProb]
  · simp [hp]

lemma worPatternMass_ne_top
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) (p : ExcursionList k) :
    worPatternMass (k := k) (hN := hN) e s p ≠ ⊤ := by
  have hden_nat : (fiber k N s).card ≠ 0 :=
    fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := s) hs
  have hden : ((fiber k N s).card : ENNReal) ≠ 0 := by
    exact_mod_cast hden_nat
  unfold worPatternMass
  apply ENNReal.div_ne_top
  · simp
  · exact hden

lemma toReal_sum_wrPatternMass
    {n N : ℕ} (hk : 0 < k) (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      wrPatternMass (k := k) hk n e s p).toReal =
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        (wrPatternMass (k := k) hk n e s p).toReal := by
  exact ENNReal.toReal_sum (fun p hp => wrPatternMass_ne_top (k := k) (hk := hk) (n := n) (e := e) (s := s) p)

lemma toReal_sum_worPatternMass
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      worPatternMass (k := k) (hN := hN) e s p).toReal =
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        (worPatternMass (k := k) (hN := hN) e s p).toReal := by
  exact ENNReal.toReal_sum
    (fun p hp => worPatternMass_ne_top (k := k) (hN := hN) (e := e) (s := s) hs p)

lemma abs_toReal_sum_wr_sub_toReal_sum_wor_le_sum_abs
    {n N : ℕ} (hk : 0 < k) (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) :
    |(∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        wrPatternMass (k := k) hk n e s p).toReal -
      (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        worPatternMass (k := k) (hN := hN) e s p).toReal| ≤
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| := by
  rw [toReal_sum_wrPatternMass (k := k) (hk := hk) (hN := hN) (e := e) (s := s)]
  rw [toReal_sum_worPatternMass (k := k) (hN := hN) (e := e) (s := s) hs]
  calc
    |(∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        (wrPatternMass (k := k) hk n e s p).toReal) -
      (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        (worPatternMass (k := k) (hN := hN) e s p).toReal)| =
      |(∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        ((wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal))| := by
      simp [Finset.sum_sub_distrib]
    _ ≤ ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| :=
      abs_sum_wrPatternMass_toReal_sub_sum_worPatternMass_toReal_le
        (k := k) (hk := hk) (hN := hN) (e := e) (s := s)

/-! ## Core reduction: correspondence identities imply the Diaconis-Freedman bound -/

/-- If the two excursion correspondence identities are available for one fiber
witness trajectory `xs`, then the desired `O(n^2 / R)` bound follows directly
from `abs_excursion_wor_wr_le_take`. -/
private lemma excursion_bound_of_wor_wr_correspondence
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hRlarge : 4 * (Nat.succ n) * (Nat.succ n) < returnsToStart (k := k) s)
    (xs : Traj k N) (hxs : xs ∈ fiber k N s)
    (hW :
      (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal =
        excursionWithReplacementProb (k := k)
          (excursionListOfTraj (k := k) xs)
          ((excursionListOfTraj (k := k) xs).take
            (prefixExcursionCount (k := k) hN xs)))
    (hPC :
      (prefixCoeff (k := k) (h := hN) e s).toReal =
        excursionWithoutReplacementProb (k := k)
          (excursionListOfTraj (k := k) xs)
          ((excursionListOfTraj (k := k) xs).take
            (prefixExcursionCount (k := k) hN xs))) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  let elist : ExcursionList k := excursionListOfTraj (k := k) xs
  let m : ℕ := prefixExcursionCount (k := k) hN xs
  have hm_le : m ≤ Nat.succ n := by
    unfold m
    simpa using
      (prefixExcursionCount_le_n (k := k) (n := Nat.succ n) (N := N) hN xs)
  have hlen_elist : elist.length = returnsToStart (k := k) s := by
    unfold elist
    exact excursionList_length_eq_returnsToStart (k := k) s xs hxs
  have hsn_sq : Nat.succ n ≤ Nat.succ n * Nat.succ n := by
    exact Nat.le_mul_of_pos_right (Nat.succ n) (Nat.succ_pos n)
  have hsq_le4 : Nat.succ n * Nat.succ n ≤ 4 * (Nat.succ n * Nat.succ n) := by
    calc
      Nat.succ n * Nat.succ n = 1 * (Nat.succ n * Nat.succ n) := by simp
      _ ≤ 4 * (Nat.succ n * Nat.succ n) := by
          exact Nat.mul_le_mul_right (Nat.succ n * Nat.succ n) (by decide : (1 : ℕ) ≤ 4)
  have hsn_le_quad : Nat.succ n ≤ 4 * (Nat.succ n) * (Nat.succ n) := by
    have htmp : Nat.succ n ≤ 4 * (Nat.succ n * Nat.succ n) := le_trans hsn_sq hsq_le4
    simpa [Nat.mul_assoc] using htmp
  have hm_len : m ≤ elist.length := by
    have hsn_le_R : Nat.succ n ≤ returnsToStart (k := k) s := by
      exact le_trans hsn_le_quad (Nat.le_of_lt hRlarge)
    exact le_trans hm_le (by simpa [hlen_elist] using hsn_le_R)
  have hR2 : 2 * m ≤ (excursionMultiset (k := k) elist).card := by
    have hm2 : 2 * m ≤ 2 * Nat.succ n := Nat.mul_le_mul_left 2 hm_le
    have hs2a : 2 * Nat.succ n ≤ 2 * (Nat.succ n * Nat.succ n) := by
      exact Nat.mul_le_mul_left 2 hsn_sq
    have hs2b : 2 * (Nat.succ n * Nat.succ n) ≤ 4 * (Nat.succ n * Nat.succ n) := by
      exact Nat.mul_le_mul_right (Nat.succ n * Nat.succ n) (by decide : (2 : ℕ) ≤ 4)
    have hs2 : 2 * Nat.succ n ≤ 4 * (Nat.succ n) * (Nat.succ n) := by
      have htmp : 2 * Nat.succ n ≤ 4 * (Nat.succ n * Nat.succ n) := le_trans hs2a hs2b
      simpa [Nat.mul_assoc] using htmp
    have h2R : 2 * m ≤ returnsToStart (k := k) s := by
      exact le_trans hm2 (le_trans hs2 (Nat.le_of_lt hRlarge))
    simpa [excursionMultiset, hlen_elist] using h2R
  have hworwr :
      |excursionWithoutReplacementProb (k := k) elist (elist.take m) -
          excursionWithReplacementProb (k := k) elist (elist.take m)| ≤
        (4 * (m : ℝ) * (m : ℝ)) / ((excursionMultiset (k := k) elist).card : ℝ) :=
    abs_excursion_wor_wr_le_take (k := k) elist m hm_len hR2
  have hworwr' :
      |excursionWithoutReplacementProb (k := k) elist (elist.take m) -
          excursionWithReplacementProb (k := k) elist (elist.take m)| ≤
        (4 * (m : ℝ) * (m : ℝ)) / (returnsToStart (k := k) s : ℝ) := by
    simpa [excursionMultiset, hlen_elist] using hworwr
  have hm_real : (m : ℝ) ≤ ((Nat.succ n : ℕ) : ℝ) := by
    exact_mod_cast hm_le
  have hnum_le :
      4 * (m : ℝ) * (m : ℝ) ≤
        4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ) := by
    nlinarith
  have hRpos_nat : 0 < returnsToStart (k := k) s := by
    have : 0 < 4 * (Nat.succ n) * (Nat.succ n) := by positivity
    exact lt_trans this hRlarge
  have hRnonneg_real : 0 ≤ (returnsToStart (k := k) s : ℝ) := by
    exact Nat.cast_nonneg _
  have hfrac_le :
      (4 * (m : ℝ) * (m : ℝ)) / (returnsToStart (k := k) s : ℝ) ≤
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
    exact div_le_div_of_nonneg_right hnum_le hRnonneg_real
  calc
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal|
        = |excursionWithReplacementProb (k := k) elist (elist.take m) -
            excursionWithoutReplacementProb (k := k) elist (elist.take m)| := by
          simp [hW, hPC, elist, m]
    _ = |excursionWithoutReplacementProb (k := k) elist (elist.take m) -
            excursionWithReplacementProb (k := k) elist (elist.take m)| := by
          rw [abs_sub_comm]
    _ ≤ (4 * (m : ℝ) * (m : ℝ)) / (returnsToStart (k := k) s : ℝ) := hworwr'
    _ ≤ (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := hfrac_le

/-! ## Diaconis-Freedman core lemma

The key bound connecting `W(empiricalParam)` and `prefixCoeff` via the
excursion decomposition. This is the mathematical heart of the proof.

The proof requires the BEST theorem (or excursion ordering bijection):
1. Uniform fiber sampling → uniform excursion ordering
2. `prefixCoeff` = ∑ WOR probabilities over excursion prefix patterns
3. `W(empiricalParam)` ≈ ∑ WR probabilities (up to Laplace smoothing)
4. WOR/WR bound gives `4n²/R`
-/

/-- **Diaconis-Freedman core**: for `R > 4n²`, the difference between
`W(empiricalParam s)` and `prefixCoeff` is bounded by `4n²/R`.

TODO: Prove via BEST theorem consequence (Euler trail counting / excursion
ordering bijection). The key missing pieces are:
- Fiber cardinality formula: `|fiber(N, s)| = t_s(G) × ∏_a (outdeg(a) - 1)!`
- Excursion ordering uniformity (consequence of BEST)
- Product decomposition of `wordProbNN` through excursion frequencies -/
theorem excursion_bound_from_decomposition
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (hRlarge : 4 * (Nat.succ n) * (Nat.succ n) < returnsToStart (k := k) s) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
  classical
  have hWdecomp :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          wrPatternMass (k := k) hk n e s p =
        W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) :=
    sum_wrPatternMass_eq_W (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)
  have hPCdecomp :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        worPatternMass (k := k) (hN := hN) e s p =
          prefixCoeff (k := k) (h := hN) e s :=
    sum_worPatternMass_eq_prefixCoeff (k := k) (hN := hN) (e := e) (s := s) hs
  have hrepr :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
          - (prefixCoeff (k := k) (h := hN) e s).toReal| =
      |(∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          wrPatternMass (k := k) hk n e s p).toReal
        - (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
            worPatternMass (k := k) (hN := hN) e s p).toReal| := by
    rw [← hWdecomp, ← hPCdecomp]
  -- Remaining core gap (Diaconis-Freedman / BEST):
  -- prove the WR-vs-WOR pattern comparison over the shared finite index set
  -- `P(n,e,s)` (WR residual is zero by construction).
  have hcore :
      |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
          - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
    -- Remaining core gap (Diaconis-Freedman / BEST): bound the pattern-level
    -- WR-vs-WOR absolute difference sum over the shared finite index set.
    rw [hrepr]
    have hsumAbs :
        ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
          |(wrPatternMass (k := k) hk n e s p).toReal -
            (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤
          (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
            (returnsToStart (k := k) s : ℝ) := by
      sorry
    exact le_trans
      (abs_toReal_sum_wr_sub_toReal_sum_wor_le_sum_abs
        (k := k) (hk := hk) (hN := hN) (e := e) (s := s) hs)
      hsumAbs
  exact hcore

end MarkovDeFinettiHardBEST

end Mettapedia.Logic
