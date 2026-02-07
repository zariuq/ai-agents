import Mettapedia.Logic.MarkovDeFinettiHardEuler
import Mettapedia.Logic.MarkovDeFinettiHardBESTCore
import Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
import Mettapedia.Logic.MarkovDeFinettiHardEmpirical
import Mettapedia.Logic.MarkovDeFinettiHardCopyPerm
import Mettapedia.Logic.MarkovDeFinettiHardEulerTrails
import Mettapedia.Logic.MarkovDeFinettiHardExcursionBridge

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
open Mettapedia.Logic.MarkovDeFinettiHardCopyPerm
open Mettapedia.Logic.MarkovDeFinettiHardEulerTrails
open Mettapedia.Logic.MarkovDeFinettiHardEulerTrailFiber
open Mettapedia.Logic.MarkovDeFinettiHard
open Mettapedia.Logic.MarkovDeFinettiHardExcursionModel
open Mettapedia.Logic.MarkovDeFinettiHardWithoutReplacementModel
open Mettapedia.Logic.MarkovDeFinettiHardExcursions
open Mettapedia.Logic.MarkovDeFinettiHardExcursionBridge
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

lemma mem_excursionPatternSet_of_prefixFiber
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    {xs : Traj k N} (hxs : xs ∈ prefixFiber (k := k) (h := hN) e s) :
    excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) ∈
      ((fiber k (Nat.succ n) e).image
        (fun ys => excursionListOfTraj (k := k) ys)) := by
  refine Finset.mem_image.2 ?_
  refine ⟨trajPrefix (k := k) hN xs, ?_, rfl⟩
  -- The prefix trajectory has state `e` by definition of `prefixFiber`.
  have hstate : prefixState (k := k) hN xs = e := (Finset.mem_filter.1 hxs).2
  have htraj : trajPrefix (k := k) hN xs ∈ trajFinset k (Nat.succ n) := by
    simp [trajFinset]
  exact Finset.mem_filter.2 ⟨htraj, by simpa [prefixState] using hstate⟩

lemma excursionPatternSet_eq_shortImage
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    excursionPatternSet (k := k) (hN := hN) e s =
      ((fiber k (Nat.succ n) e).image
        (fun ys => excursionListOfTraj (k := k) ys)) := by
  classical
  apply Finset.ext
  intro p
  constructor
  · intro hp
    rcases Finset.mem_union.1 hp with hpL | hpR
    · rcases Finset.mem_image.1 hpL with ⟨xs, hxs, rfl⟩
      exact mem_excursionPatternSet_of_prefixFiber (k := k) (hN := hN) (e := e) (s := s) hxs
    · exact hpR
  · intro hp
    exact Finset.mem_union.2 (Or.inr hp)

/-- The `p`-fiber inside `prefixFiber(hN,e,s)`. -/
def prefixPatternFiber
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) :
    Finset (Traj k N) :=
  (prefixFiber (k := k) (h := hN) e s).filter
    (fun xs => excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = p)

lemma segmentSwap_mem_prefixPatternFiber_of_prefix_before_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (xs : Traj k N) (hxs : xs ∈ prefixPatternFiber (k := k) (hN := hN) e s p)
    (a L1 L2 : ℕ) (hna : Nat.succ n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N)
    (ha_ret : xs ⟨a, by omega⟩ = xs 0)
    (hb_ret : xs ⟨a + L1, by omega⟩ = xs 0)
    (hc_ret : xs ⟨a + L1 + L2, by omega⟩ = xs 0) :
    segmentSwap xs a L1 L2 hL1 hL2 hcN ∈
      prefixPatternFiber (k := k) (hN := hN) e s p := by
  have hxs_pf : xs ∈ prefixFiber (k := k) (h := hN) e s := (Finset.mem_filter.1 hxs).1
  have hmem_pf :
      segmentSwap xs a L1 L2 hL1 hL2 hcN ∈ prefixFiber (k := k) (h := hN) e s :=
    segmentSwap_mem_prefixFiber_of_prefix_before_swap
      (k := k) (h := hN) (e := e) (eN := s) (xs := xs)
      (a := a) (L1 := L1) (L2 := L2) (hna := hna)
      (hL1 := hL1) (hL2 := hL2) (hcN := hcN)
      (ha_ret := ha_ret) (hb_ret := hb_ret) (hc_ret := hc_ret) hxs_pf
  have hpat : excursionListOfTraj (k := k) (trajPrefix (k := k) hN xs) = p :=
    (Finset.mem_filter.1 hxs).2
  have hprefix_eq :
      trajPrefix (k := k) hN (segmentSwap xs a L1 L2 hL1 hL2 hcN) =
        trajPrefix (k := k) hN xs :=
    trajPrefix_segmentSwap_eq_of_prefix_before_swap
      (k := k) (h := hN) (xs := xs) (a := a) (L1 := L1) (L2 := L2)
      (hna := hna) (hL1 := hL1) (hL2 := hL2) (hcN := hcN)
  refine Finset.mem_filter.2 ?_
  refine ⟨hmem_pf, ?_⟩
  simpa [hprefix_eq] using hpat

lemma card_image_segmentSwap_prefixPatternFiber_of_prefix_before_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (a L1 L2 : ℕ) (_hna : Nat.succ n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    ((prefixPatternFiber (k := k) (hN := hN) e s p).image
      (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcN)).card =
      (prefixPatternFiber (k := k) (hN := hN) e s p).card := by
  classical
  refine Finset.card_image_iff.mpr ?_
  intro x hx y hy hxy
  exact segmentSwap_injective (k := k) (a := a) (L1 := L1) (L2 := L2)
    (hL1 := hL1) (hL2 := hL2) (hcN := hcN) hxy

/-- WOR-side mass for pattern `p`: cardinality ratio in the long-horizon fiber. -/
def worPatternMass
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) : ENNReal :=
  ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
    ((fiber k N s).card : ENNReal)

/-- Pattern ratio inside the long-prefix fiber:
`|prefixPatternFiber(hN,e,s,p)| / |prefixFiber(hN,e,s)|`. -/
def prefixPatternRatio
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) : ENNReal :=
  ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
    ((prefixFiber (k := k) (h := hN) e s).card : ENNReal)

/-- WR-side mass for pattern `p`: indicator-sum over short trajectories in `fiber(n+1,e)`. -/
def wrPatternMass
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k) : ENNReal :=
  ∑ ys ∈ fiber k (Nat.succ n) e,
    if excursionListOfTraj (k := k) ys = p then
      wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys)
    else 0

/-- The short-horizon trajectories in state `e` with excursion list exactly `p`. -/
def shortPatternFiber
    (n : ℕ) (e : MarkovState k) (p : ExcursionList k) : Finset (Traj k (Nat.succ n)) :=
  (fiber k (Nat.succ n) e).filter (fun ys => excursionListOfTraj (k := k) ys = p)

/-- Pattern ratio inside the short fiber:
`|shortPatternFiber(n,e,p)| / |fiber(n+1,e)|`. -/
def shortPatternRatio
    (n : ℕ) (e : MarkovState k) (p : ExcursionList k) : ENNReal :=
  ((shortPatternFiber (k := k) n e p).card : ENNReal) /
    ((fiber k (Nat.succ n) e).card : ENNReal)

/-- Long-prefix pattern ratio is invariant under segment-swap image cardinality
in the post-prefix regime (`n+1 ≤ a`). -/
lemma prefixPatternRatio_card_image_segmentSwap_of_prefix_before_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (a L1 L2 : ℕ) (hna : Nat.succ n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    (((prefixPatternFiber (k := k) (hN := hN) e s p).image
      (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcN)).card : ENNReal) /
      ((prefixFiber (k := k) (h := hN) e s).card : ENNReal) =
    prefixPatternRatio (k := k) (hN := hN) e s p := by
  rw [card_image_segmentSwap_prefixPatternFiber_of_prefix_before_swap
      (k := k) (hN := hN) (e := e) (s := s) (p := p)
      (a := a) (L1 := L1) (L2 := L2) hna hL1 hL2 hcN]
  rfl

lemma worPatternMass_card_image_segmentSwap_of_prefix_before_swap
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (a L1 L2 : ℕ) (hna : Nat.succ n ≤ a)
    (hL1 : 0 < L1) (hL2 : 0 < L2) (hcN : a + L1 + L2 ≤ N) :
    (((prefixPatternFiber (k := k) (hN := hN) e s p).image
      (fun xs => segmentSwap xs a L1 L2 hL1 hL2 hcN)).card : ENNReal) /
      ((fiber k N s).card : ENNReal) =
    worPatternMass (k := k) (hN := hN) e s p := by
  rw [card_image_segmentSwap_prefixPatternFiber_of_prefix_before_swap
      (k := k) (hN := hN) (e := e) (s := s) (p := p)
      (a := a) (L1 := L1) (L2 := L2) hna hL1 hL2 hcN]
  rfl

lemma wrPatternMass_eq_card_mul_wordProb_of_mem_shortPatternFiber
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k)
    {ys₀ : Traj k (Nat.succ n)} (hys₀ : ys₀ ∈ shortPatternFiber (k := k) n e p) :
    wrPatternMass (k := k) hk n e s p =
      (shortPatternFiber (k := k) n e p).card *
        wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) := by
  classical
  have hconst :
      ∀ ys ∈ shortPatternFiber (k := k) n e p,
        wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys) =
          wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) := by
    intro ys hys
    have hstate : stateOfTraj (k := k) ys = stateOfTraj (k := k) ys₀ := by
      have hyse : stateOfTraj (k := k) ys = e := (Finset.mem_filter.1 ((Finset.mem_filter.1 hys).1)).2
      have hys0e : stateOfTraj (k := k) ys₀ = e := (Finset.mem_filter.1 ((Finset.mem_filter.1 hys₀).1)).2
      exact hyse.trans hys0e.symm
    exact wordProb_const_on_state_fiber (k := k)
      (θ := empiricalParam (k := k) hk s) hstate
  unfold wrPatternMass shortPatternFiber
  have hsum_filter :
      ∑ ys ∈ fiber k (Nat.succ n) e,
        (if excursionListOfTraj (k := k) ys = p then
          wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys) else 0) =
      ∑ ys ∈ (fiber k (Nat.succ n) e).filter (fun ys => excursionListOfTraj (k := k) ys = p),
        wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys) := by
    simpa using
      (Finset.sum_filter
        (s := fiber k (Nat.succ n) e)
        (p := fun ys => excursionListOfTraj (k := k) ys = p)
        (f := fun ys =>
          wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys))).symm
  rw [hsum_filter]
  have hsum_const :
      ∑ ys ∈ (fiber k (Nat.succ n) e).filter (fun ys => excursionListOfTraj (k := k) ys = p),
        wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys) =
      ∑ ys ∈ (fiber k (Nat.succ n) e).filter (fun ys => excursionListOfTraj (k := k) ys = p),
        wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) := by
    refine Finset.sum_congr rfl ?_
    intro ys hys
    exact hconst ys (by simpa [shortPatternFiber] using hys)
  rw [hsum_const]
  rw [Finset.sum_const]
  simp [nsmul_eq_mul, mul_comm]

lemma wrPatternMass_eq_shortRatio_mul_W
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k)
    {ys₀ : Traj k (Nat.succ n)} (hys₀ : ys₀ ∈ shortPatternFiber (k := k) n e p) :
    wrPatternMass (k := k) hk n e s p =
      shortPatternRatio (k := k) n e p *
      W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) := by
  have hysFiber : ys₀ ∈ fiber k (Nat.succ n) e := (Finset.mem_filter.1 hys₀).1
  have hwr :=
    wrPatternMass_eq_card_mul_wordProb_of_mem_shortPatternFiber
      (k := k) (hk := hk) (n := n) (e := e) (s := s) (p := p) hys₀
  have hW :=
    W_eq_card_mul_wordProb_of_mem_fiber
      (k := k) (N := Nat.succ n)
      (θ := empiricalParam (k := k) hk s) (s := e) ys₀ hysFiber
  have hden_ne_zero_nat : (fiber k (Nat.succ n) e).card ≠ 0 := by
    exact Finset.card_ne_zero.mpr ⟨ys₀, hysFiber⟩
  have hden_ne_zero : ((fiber k (Nat.succ n) e).card : ENNReal) ≠ 0 := by
    exact_mod_cast hden_ne_zero_nat
  have hden_ne_top : ((fiber k (Nat.succ n) e).card : ENNReal) ≠ ⊤ := by
    simp
  have hWdiv :
      (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)) /
          ((fiber k (Nat.succ n) e).card : ENNReal) =
        wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) := by
    have hcancel :
        (((fiber k (Nat.succ n) e).card : ENNReal) *
            (((fiber k (Nat.succ n) e).card : ENNReal)⁻¹)) = 1 := by
      exact ENNReal.mul_inv_cancel hden_ne_zero hden_ne_top
    calc
      (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)) /
          ((fiber k (Nat.succ n) e).card : ENNReal)
          = (((fiber k (Nat.succ n) e).card : ENNReal) *
              wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀)) *
              (((fiber k (Nat.succ n) e).card : ENNReal)⁻¹) := by
                simp [hW, div_eq_mul_inv]
      _ = wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) *
            ((((fiber k (Nat.succ n) e).card : ENNReal) *
              (((fiber k (Nat.succ n) e).card : ENNReal)⁻¹))) := by
              ac_rfl
      _ = wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) := by
            simp [hcancel]
  calc
    wrPatternMass (k := k) hk n e s p
        = ((shortPatternFiber (k := k) n e p).card : ENNReal) *
            wordProb (k := k) (empiricalParam (k := k) hk s) (trajToList (k := k) ys₀) := hwr
    _ = ((shortPatternFiber (k := k) n e p).card : ENNReal) *
          ((W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)) /
            ((fiber k (Nat.succ n) e).card : ENNReal)) := by
          rw [hWdiv]
    _ = shortPatternRatio (k := k) n e p *
          W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) := by
          simp [shortPatternRatio, div_eq_mul_inv]
          ac_rfl

lemma wrPatternMass_eq_shortRatio_mul_W_uncond
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k) :
    wrPatternMass (k := k) hk n e s p =
      shortPatternRatio (k := k) n e p *
      W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) := by
  by_cases hcard : (shortPatternFiber (k := k) n e p).card = 0
  · have hempty : shortPatternFiber (k := k) n e p = ∅ := Finset.card_eq_zero.mp hcard
    have hwr0 : wrPatternMass (k := k) hk n e s p = 0 := by
      unfold wrPatternMass
      refine Finset.sum_eq_zero ?_
      intro ys hys
      have hyne : excursionListOfTraj (k := k) ys ≠ p := by
        intro hy
        have hmem : ys ∈ shortPatternFiber (k := k) n e p := by
          exact Finset.mem_filter.2 ⟨hys, hy⟩
        have : False := by
          simp [hempty] at hmem
        exact this.elim
      simp [hyne]
    have hnum0 : ((shortPatternFiber (k := k) n e p).card : ENNReal) = 0 := by
      exact_mod_cast hcard
    have hshort0 : shortPatternRatio (k := k) n e p = 0 := by
      unfold shortPatternRatio
      simp [hnum0]
    simp [hwr0, hshort0]
  · rcases Finset.card_ne_zero.mp hcard with ⟨ys₀, hys₀⟩
    exact wrPatternMass_eq_shortRatio_mul_W
      (k := k) (hk := hk) (n := n) (e := e) (s := s) (p := p) hys₀

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

lemma worPatternMass_eq_prefixRatio_mul_prefixCoeff
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) (p : ExcursionList k) :
    worPatternMass (k := k) (hN := hN) e s p =
      prefixPatternRatio (k := k) (hN := hN) e s p *
      prefixCoeff (k := k) (h := hN) e s := by
  have hden_nat : (fiber k N s).card ≠ 0 :=
    fiber_card_ne_zero_of_mem_stateFinset (k := k) (N := N) (eN := s) hs
  have hden : ((fiber k N s).card : ENNReal) ≠ 0 := by
    exact_mod_cast hden_nat
  by_cases hpf0 : (prefixFiber (k := k) (h := hN) e s).card = 0
  · have hnum0 : ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) = 0 := by
      have hsubset :
          prefixPatternFiber (k := k) (hN := hN) e s p ⊆
            prefixFiber (k := k) (h := hN) e s := by
        intro xs hxs
        exact (Finset.mem_filter.1 hxs).1
      have hcard_le :
          (prefixPatternFiber (k := k) (hN := hN) e s p).card ≤
            (prefixFiber (k := k) (h := hN) e s).card := Finset.card_le_card hsubset
      have hcard0 : (prefixPatternFiber (k := k) (hN := hN) e s p).card = 0 := by
        omega
      exact_mod_cast hcard0
    have hpc0 : prefixCoeff (k := k) (h := hN) e s = 0 := by
      simp [prefixCoeff, hpf0]
    unfold worPatternMass
    simp [hnum0, hpc0]
  · have hpf_ne_zero : ((prefixFiber (k := k) (h := hN) e s).card : ENNReal) ≠ 0 := by
      exact_mod_cast hpf0
    have hpf_ne_top : ((prefixFiber (k := k) (h := hN) e s).card : ENNReal) ≠ ⊤ := by
      simp
    have hpc :
        prefixCoeff (k := k) (h := hN) e s =
          (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) /
            ((fiber k N s).card : ENNReal)) := by
      unfold prefixCoeff
      simp [hden_nat]
    unfold worPatternMass
    have hcancel :
        (((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
            ((prefixFiber (k := k) (h := hN) e s).card : ENNReal)) *
          (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) /
            ((fiber k N s).card : ENNReal)) =
        ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
          ((fiber k N s).card : ENNReal) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hmid :
          (((prefixFiber (k := k) (h := hN) e s).card : ENNReal)⁻¹ *
              (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) *
                (((fiber k N s).card : ENNReal)⁻¹))) =
            (((fiber k N s).card : ENNReal)⁻¹) := by
        calc
          (((prefixFiber (k := k) (h := hN) e s).card : ENNReal)⁻¹ *
              (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) *
                (((fiber k N s).card : ENNReal)⁻¹))) =
              ((((prefixFiber (k := k) (h := hN) e s).card : ENNReal)⁻¹ *
                  ((prefixFiber (k := k) (h := hN) e s).card : ENNReal)) *
                (((fiber k N s).card : ENNReal)⁻¹)) := by
                  ac_rfl
          _ = (1 : ENNReal) * (((fiber k N s).card : ENNReal)⁻¹) := by
                rw [ENNReal.inv_mul_cancel hpf_ne_zero hpf_ne_top]
          _ = (((fiber k N s).card : ENNReal)⁻¹) := by simp
      calc
        (((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) *
            ((prefixFiber (k := k) (h := hN) e s).card : ENNReal)⁻¹) *
            (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) *
              (((fiber k N s).card : ENNReal)⁻¹)) =
          ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) *
            (((prefixFiber (k := k) (h := hN) e s).card : ENNReal)⁻¹ *
              (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) *
                (((fiber k N s).card : ENNReal)⁻¹))) := by
                  ac_rfl
        _ =
          ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) *
            (((fiber k N s).card : ENNReal)⁻¹) := by rw [hmid]
        _ = ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
              ((fiber k N s).card : ENNReal) := by simp [div_eq_mul_inv]
    calc
      worPatternMass (k := k) (hN := hN) e s p
          = ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
              ((fiber k N s).card : ENNReal) := by rfl
      _ = (((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
            ((prefixFiber (k := k) (h := hN) e s).card : ENNReal)) *
          (((prefixFiber (k := k) (h := hN) e s).card : ENNReal) /
            ((fiber k N s).card : ENNReal)) := by
            exact hcancel.symm
      _ = prefixPatternRatio (k := k) (hN := hN) e s p *
          prefixCoeff (k := k) (h := hN) e s := by
            simp [prefixPatternRatio, hpc]

lemma wrPatternMass_toReal_eq_shortRatio_toReal_mul_W_toReal
    (hk : 0 < k) (n : ℕ) (e s : MarkovState k) (p : ExcursionList k) :
    (wrPatternMass (k := k) hk n e s p).toReal =
      (shortPatternRatio (k := k) n e p).toReal *
        (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal := by
  have hEq :
      wrPatternMass (k := k) hk n e s p =
        shortPatternRatio (k := k) n e p *
          W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) :=
    wrPatternMass_eq_shortRatio_mul_W_uncond
      (k := k) (hk := hk) (n := n) (e := e) (s := s) (p := p)
  calc
    (wrPatternMass (k := k) hk n e s p).toReal
        = (shortPatternRatio (k := k) n e p *
            W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal := by
            simp [hEq]
    _ = (shortPatternRatio (k := k) n e p).toReal *
          (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal := by
          simp [ENNReal.toReal_mul]

lemma worPatternMass_toReal_eq_prefixRatio_toReal_mul_prefixCoeff_toReal
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) (p : ExcursionList k) :
    (worPatternMass (k := k) (hN := hN) e s p).toReal =
      (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
        (prefixCoeff (k := k) (h := hN) e s).toReal := by
  have hEq :
      worPatternMass (k := k) (hN := hN) e s p =
        prefixPatternRatio (k := k) (hN := hN) e s p *
          prefixCoeff (k := k) (h := hN) e s :=
    worPatternMass_eq_prefixRatio_mul_prefixCoeff
      (k := k) (hN := hN) (e := e) (s := s) hs p
  calc
    (worPatternMass (k := k) (hN := hN) e s p).toReal
        = (prefixPatternRatio (k := k) (hN := hN) e s p *
            prefixCoeff (k := k) (h := hN) e s).toReal := by
            simp [hEq]
    _ = (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
          (prefixCoeff (k := k) (h := hN) e s).toReal := by
          simp [ENNReal.toReal_mul]

lemma abs_wr_wor_patternMass_toReal_eq_abs_ratio_form
    {n N : ℕ} (hk : 0 < k) (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) (p : ExcursionList k) :
    |(wrPatternMass (k := k) hk n e s p).toReal -
      (worPatternMass (k := k) (hN := hN) e s p).toReal| =
      |(shortPatternRatio (k := k) n e p).toReal *
          (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
          (prefixCoeff (k := k) (h := hN) e s).toReal| := by
  rw [wrPatternMass_toReal_eq_shortRatio_toReal_mul_W_toReal
      (k := k) (hk := hk) (n := n) (e := e) (s := s) (p := p)]
  rw [worPatternMass_toReal_eq_prefixRatio_toReal_mul_prefixCoeff_toReal
      (k := k) (hN := hN) (e := e) (s := s) (hs := hs) (p := p)]

lemma sum_abs_wr_wor_patternMass_toReal_eq_sum_abs_ratio_form
    {n N : ℕ} (hk : 0 < k) (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) :
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(wrPatternMass (k := k) hk n e s p).toReal -
        (worPatternMass (k := k) (hN := hN) e s p).toReal|) =
    (∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
      |(shortPatternRatio (k := k) n e p).toReal *
          (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
        (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
          (prefixCoeff (k := k) (h := hN) e s).toReal|) := by
  refine Finset.sum_congr rfl ?_
  intro p hp
  exact abs_wr_wor_patternMass_toReal_eq_abs_ratio_form
    (k := k) (hk := hk) (hN := hN) (e := e) (s := s) (hs := hs) (p := p)

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

lemma sum_wrPatternMass_over_shortImage_eq_W
    {n N : ℕ} (hk : 0 < k) (hN : Nat.succ n ≤ N) (e s : MarkovState k) :
    ∑ p ∈ ((fiber k (Nat.succ n) e).image
        (fun ys => excursionListOfTraj (k := k) ys)),
      wrPatternMass (k := k) hk n e s p =
        W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s) := by
  simpa [excursionPatternSet_eq_shortImage (k := k) (hN := hN) (e := e) (s := s)]
    using sum_wrPatternMass_eq_W (k := k) (hk := hk) (n := n) (hN := hN) (e := e) (s := s)

lemma sum_worPatternMass_over_shortImage_eq_prefixCoeff
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k)
    (hs : s ∈ stateFinset k N) :
    ∑ p ∈ ((fiber k (Nat.succ n) e).image
        (fun ys => excursionListOfTraj (k := k) ys)),
      worPatternMass (k := k) (hN := hN) e s p =
        prefixCoeff (k := k) (h := hN) e s := by
  simpa [excursionPatternSet_eq_shortImage (k := k) (hN := hN) (e := e) (s := s)]
    using sum_worPatternMass_eq_prefixCoeff (k := k) (hN := hN) (e := e) (s := s) hs

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

/-! ## BEST-side transport for WOR pattern masses

These lemmas move WOR masses from trajectory fibers to Euler-trail filters
using the already-proved copy-permutation cardinality formulas.
-/

lemma prefixPatternFiber_subset_fiber
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k) :
    prefixPatternFiber (k := k) (hN := hN) e s p ⊆ fiber k N s := by
  intro xs hxs
  exact prefixFiber_subset_fiber (k := k) (h := hN) (e := e) (eN := s)
    ((Finset.mem_filter.1 hxs).1)

lemma eulerTrailFinset_card_filter_prefixPatternFiber
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (hs : s ∈ stateFinset k N) :
    ((eulerTrailFinset (graphOfState s) s.start s.last).filter
      (fun f =>
        castTraj
            (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
            (trailVertexSeq (graphOfState s) s.start f) ∈
          prefixPatternFiber (k := k) (hN := hN) e s p)).card =
      (prefixPatternFiber (k := k) (hN := hN) e s p).card *
        ∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial := by
  have hTok : totalEdgeTokens (k := k) (graphOfState s) = N :=
    totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs
  subst hTok
  have hA :
      prefixPatternFiber (k := k) (hN := hN) e s p ⊆
        fiber k (totalEdgeTokens (k := k) (graphOfState s)) s :=
    prefixPatternFiber_subset_fiber (k := k) (hN := hN) (e := e) (s := s) (p := p)
  simpa using
    eulerTrailFinset_card_filter_trajSubset (k := k) (s := s)
      (A := prefixPatternFiber (k := k) (hN := hN) e s p) hA

lemma worPatternMass_eq_eulerTrail_ratio
    {n N : ℕ} (hN : Nat.succ n ≤ N) (e s : MarkovState k) (p : ExcursionList k)
    (hs : s ∈ stateFinset k N) :
    worPatternMass (k := k) (hN := hN) e s p =
      (((eulerTrailFinset (graphOfState s) s.start s.last).filter
          (fun f =>
            castTraj
                (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
                (trailVertexSeq (graphOfState s) s.start f) ∈
              prefixPatternFiber (k := k) (hN := hN) e s p)).card : ENNReal) /
        ((eulerTrailFinset (graphOfState s) s.start s.last).card : ENNReal) := by
  have hTok : totalEdgeTokens (k := k) (graphOfState s) = N :=
    totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs
  subst hTok
  have hcopy_ne_zero_nat :
      (∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    exact Nat.factorial_ne_zero (graphOfState s a b)
  have hcopy_ne_zero_enn :
      ((∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial) : ENNReal) ≠ 0 := by
    exact_mod_cast hcopy_ne_zero_nat
  have hnum_mul :
      (((eulerTrailFinset (graphOfState s) s.start s.last).filter
          (fun f =>
            trailVertexSeq (graphOfState s) s.start f ∈
              prefixPatternFiber (k := k) (hN := hN) e s p)).card : ENNReal) =
        ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) *
          ((∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial) : ENNReal) := by
    have h :=
      eulerTrailFinset_card_filter_prefixPatternFiber (k := k) (hN := hN) (e := e) (s := s) (p := p) hs
    exact_mod_cast h
  have hcast_filter :
      (((eulerTrailFinset (graphOfState s) s.start s.last).filter
          (fun f =>
            castTraj
                (totalEdgeTokens_graphOfState_eq_of_mem_stateFinset (k := k) hs)
                (trailVertexSeq (graphOfState s) s.start f) ∈
              prefixPatternFiber (k := k) (hN := hN) e s p)).card : ENNReal) =
      (((eulerTrailFinset (graphOfState s) s.start s.last).filter
          (fun f =>
            trailVertexSeq (graphOfState s) s.start f ∈
              prefixPatternFiber (k := k) (hN := hN) e s p)).card : ENNReal) := by
    simp [castTraj]
  have hden_mul :
      (((eulerTrailFinset (graphOfState s) s.start s.last).card : ℕ) : ENNReal) =
        ((fiber k (totalEdgeTokens (k := k) (graphOfState s)) s).card : ENNReal) *
          ((∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial) : ENNReal) := by
    have h := eulerTrailFinset_card_eq (k := k) (s := s) hs
    exact_mod_cast h
  unfold worPatternMass
  rw [hcast_filter]
  rw [hnum_mul, hden_mul]
  set F : ENNReal := ((∏ a : Fin k, ∏ b : Fin k, (graphOfState s a b).factorial) : ENNReal)
  have hcopy_ne_top : F ≠ ⊤ := by
    dsimp [F]
    refine ENNReal.prod_ne_top ?_
    intro a ha
    refine ENNReal.prod_ne_top ?_
    intro b hb
    exact ENNReal.natCast_ne_top _
  have hcancel :
      (((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) * F) /
          (((fiber k (totalEdgeTokens (k := k) (graphOfState s)) s).card : ENNReal) * F) =
        ((prefixPatternFiber (k := k) (hN := hN) e s p).card : ENNReal) /
          ((fiber k (totalEdgeTokens (k := k) (graphOfState s)) s).card : ENNReal) := by
    rw [mul_comm _ F, mul_comm _ F,
      ENNReal.mul_div_mul_left _ _ (by simpa [F] using hcopy_ne_zero_enn) hcopy_ne_top]
  simpa [F] using hcancel.symm

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
private lemma excursion_bound_from_pattern_abs_sum
    (hk : 0 < k) (n : ℕ) (e : MarkovState k)
    {N : ℕ} (hN : Nat.succ n ≤ N) (s : MarkovState k)
    (hs : s ∈ stateFinset k N)
    (hsumAbs :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ)) :
    |(W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal
        - (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
      (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
        (returnsToStart (k := k) s : ℝ) := by
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
  rw [hrepr]
  exact le_trans
    (abs_toReal_sum_wr_sub_toReal_sum_wor_le_sum_abs
      (k := k) (hk := hk) (hN := hN) (e := e) (s := s) hs)
    hsumAbs

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
  -- Remaining core gap (Diaconis-Freedman / BEST) in ratio form:
  -- compare short-fiber pattern ratios against long-prefix pattern ratios on the
  -- shared finite index set `P(n,e,s)`.
  have hsumAbsRatio :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(shortPatternRatio (k := k) n e p).toReal *
            (W (k := k) (Nat.succ n) e (empiricalParam (k := k) hk s)).toReal -
          (prefixPatternRatio (k := k) (hN := hN) e s p).toReal *
            (prefixCoeff (k := k) (h := hN) e s).toReal| ≤
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
    sorry
  have hsumAbs :
      ∑ p ∈ excursionPatternSet (k := k) (hN := hN) e s,
        |(wrPatternMass (k := k) hk n e s p).toReal -
          (worPatternMass (k := k) (hN := hN) e s p).toReal| ≤
        (4 * ((Nat.succ n : ℕ) : ℝ) * ((Nat.succ n : ℕ) : ℝ)) /
          (returnsToStart (k := k) s : ℝ) := by
    simpa [sum_abs_wr_wor_patternMass_toReal_eq_sum_abs_ratio_form
      (k := k) (hk := hk) (hN := hN) (e := e) (s := s) hs] using hsumAbsRatio
  exact excursion_bound_from_pattern_abs_sum
    (k := k) hk n e hN s hs hsumAbs

end MarkovDeFinettiHardBEST

end Mettapedia.Logic
