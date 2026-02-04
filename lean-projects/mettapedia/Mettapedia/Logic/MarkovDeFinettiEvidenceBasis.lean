import Mathlib.Data.List.OfFn
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mettapedia.Logic.MarkovDeFinettiHardBase
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti — Evidence Partitions (Basis Infrastructure)

This file implements the “Markov analogue of the Bernstein basis” suggested by the classical
Diaconis–Freedman proof strategy:

For each horizon `n`, consider the **finite** set of length-`n+1` trajectories `Fin (n+1) → Fin k`.
Each such trajectory has a Markov sufficient-statistic summary:

* `start : Fin k`
* transition-count matrix `counts : TransCounts k`
* `last : Fin k`

This induces:

* a weight `wμ n e` for any prefix measure `μ` (sum of `μ(xs)` over trajectories with summary `e`),
* a continuous “evidence polynomial” `W n e : MarkovParam k → ℝ≥0∞` (sum of `wordProb θ xs` over the
  same fiber).

The key property is that for each fixed `n`, the family `{W n e}` forms a **finite partition of
unity** on `MarkovParam k`, and `{wμ n e}` forms a probability vector.

These are the reusable objects needed to restate the Markov de Finetti hard direction as one
representability lemma:

> ∃ π on `MarkovParam k` such that `∫ W n e dπ = wμ n e` for all `n,e`.

Once such a `π` exists, per-word mixture formulas follow by regrouping.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators
open scoped NNReal ENNReal

open MeasureTheory

namespace MarkovDeFinettiHard

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovExchangeability

variable {k : ℕ}

/-! ## Horizon-`n` trajectories and their evidence summaries -/

/-- Length-`n+1` trajectories over `Fin k` (so there are `n` transitions). -/
abbrev Traj (k : ℕ) (n : ℕ) := Fin (n + 1) → Fin k

/-- Coerce a trajectory to the corresponding list. -/
def trajToList {n : ℕ} (xs : Traj k n) : List (Fin k) :=
  List.ofFn xs

@[simp] lemma length_trajToList {n : ℕ} (xs : Traj k n) :
    (trajToList (k := k) xs).length = n + 1 := by
  simp [trajToList]

/-- Evidence state = (start, transition counts, last). -/
@[ext]
structure MarkovState (k : ℕ) where
  start : Fin k
  counts : TransCounts k
  last : Fin k
deriving DecidableEq

/-- The evidence state of a trajectory. -/
def stateOfTraj {n : ℕ} (xs : Traj k n) : MarkovState k :=
  ⟨xs 0, MarkovExchangeabilityBridge.countsOfFn (k := k) xs, xs (Fin.last n)⟩

@[simp] lemma stateOfTraj_start {n : ℕ} (xs : Traj k n) :
    (stateOfTraj (k := k) xs).start = xs 0 := rfl

@[simp] lemma stateOfTraj_last {n : ℕ} (xs : Traj k n) :
    (stateOfTraj (k := k) xs).last = xs (Fin.last n) := rfl

/-! ## Extending trajectories and evidence states -/

/-- Append a symbol to a trajectory. -/
def trajSnoc {n : ℕ} (xs : Traj k n) (x : Fin k) : Traj k (n + 1) :=
  Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs x

/-- Drop the last symbol of a trajectory. -/
def trajInit {n : ℕ} (xs : Traj k (n + 1)) : Traj k n :=
  fun i => xs (Fin.castSucc i)

/-- `trajToList` of an extended trajectory is list append. -/
lemma trajToList_trajSnoc {n : ℕ} (xs : Traj k n) (x : Fin k) :
    trajToList (k := k) (trajSnoc (k := k) xs x) = trajToList (k := k) xs ++ [x] := by
  -- `List.ofFn` for a `Fin.snoc` is a `concat`/append.
  unfold trajToList trajSnoc
  -- `ofFn_succ'` turns `List.ofFn` into a `concat` form; we rewrite `concat` into `++ [x]`.
  rw [List.ofFn_succ' (f := Fin.snoc (α := fun _ : Fin (n + 2) => Fin k) xs x)]
  simp [List.concat_eq_append]

/-- `trajInit` is left inverse to `trajSnoc`. -/
lemma trajInit_trajSnoc {n : ℕ} (xs : Traj k n) (x : Fin k) :
    trajInit (k := k) (trajSnoc (k := k) xs x) = xs := by
  funext i
  simp [trajInit, trajSnoc]

/-- `trajSnoc` is right inverse to `trajInit` with the last symbol. -/
lemma trajSnoc_trajInit {n : ℕ} (xs : Traj k (n + 1)) :
    trajSnoc (k := k) (trajInit (k := k) xs) (xs (Fin.last (n + 1))) = xs := by
  funext i
  cases i using Fin.lastCases with
  | last =>
      simp [trajSnoc]
  | cast j =>
      simp [trajSnoc, trajInit]

/-- Update an evidence state by appending a next symbol. -/
def MarkovState.snoc (e : MarkovState k) (x : Fin k) : MarkovState k :=
  ⟨e.start, TransCounts.bump e.counts e.last x, x⟩

@[simp] lemma MarkovState.snoc_start (e : MarkovState k) (x : Fin k) :
    (MarkovState.snoc (k := k) e x).start = e.start := rfl

@[simp] lemma MarkovState.snoc_last (e : MarkovState k) (x : Fin k) :
    (MarkovState.snoc (k := k) e x).last = x := rfl

lemma countsOfFn_trajSnoc {n : ℕ} (xs : Traj k n) (x : Fin k) :
    MarkovExchangeabilityBridge.countsOfFn (k := k) (trajSnoc (k := k) xs x) =
      TransCounts.bump (MarkovExchangeabilityBridge.countsOfFn (k := k) xs) (xs (Fin.last n)) x := by
  classical
  ext a b
  -- Expand the `transCount` recursion.
  have htc :
      transCount (n := n + 1) (trajSnoc (k := k) xs x) a b =
        transCount (n := n) xs a b + (if xs (Fin.last n) = a ∧ x = b then 1 else 0) := by
    -- `trajSnoc` is definitional `Fin.snoc`.
    simpa [trajSnoc] using
      (transCount_snoc (n := n) (xs := xs) (x := x) (a := a) (b := b))
  -- Turn the `transCount` statement into `TransCounts.bump`.
  by_cases h : a = xs (Fin.last n) ∧ b = x
  · rcases h with ⟨ha, hb⟩
    subst ha; subst hb
    -- Both sides are `transCount xs (xs last) x + 1`.
    simp [MarkovExchangeabilityBridge.countsOfFn, TransCounts.bump, htc]
  · have h' : ¬(xs (Fin.last n) = a ∧ x = b) := by
        intro h'
        apply h
        exact ⟨h'.1.symm, h'.2.symm⟩
    -- Both sides reduce to `transCount xs a b`.
    simp [MarkovExchangeabilityBridge.countsOfFn, TransCounts.bump, htc, h, h']

lemma stateOfTraj_trajSnoc {n : ℕ} (xs : Traj k n) (x : Fin k) :
    stateOfTraj (k := k) (trajSnoc (k := k) xs x) =
      MarkovState.snoc (k := k) (stateOfTraj (k := k) xs) x := by
  classical
  refine MarkovState.ext ?_ ?_ ?_
  · -- start
    simp [stateOfTraj, trajSnoc, MarkovState.snoc]
  · -- counts
    simpa [stateOfTraj, MarkovState.snoc] using countsOfFn_trajSnoc (k := k) (xs := xs) (x := x)
  · -- last
    simp [stateOfTraj, trajSnoc, MarkovState.snoc]

/-! ## Finite partitions over evidence classes -/

/-- Finite set of all length-`n+1` trajectories. -/
def trajFinset (k : ℕ) (n : ℕ) : Finset (Traj k n) :=
  Finset.univ

/-! ### Aliases matching the “evidence partition” terminology -/

/-- Alias: finite set of words (trajectories) of length `n+1`. -/
def Words (k : ℕ) (n : ℕ) : Finset (Traj k n) :=
  trajFinset k n

/-- The finite set of evidence states realized at horizon `n`. -/
def stateFinset (k : ℕ) (n : ℕ) : Finset (MarkovState k) :=
  (trajFinset k n).image (stateOfTraj (k := k))

/-- Alias: finite evidence class set at horizon `n`. -/
def E_n (k : ℕ) (n : ℕ) : Finset (MarkovState k) :=
  stateFinset k n

lemma stateOfTraj_mem_stateFinset {n : ℕ} (xs : Traj k n) :
    stateOfTraj (k := k) xs ∈ stateFinset k n := by
  classical
  refine Finset.mem_image.2 ?_
  exact ⟨xs, by simp [trajFinset], rfl⟩

/-! ## Evidence weights `wμ` and evidence polynomials `W` -/

/-- Weight of an evidence state under a prefix measure `μ` at horizon `n`. -/
def wμ (μ : PrefixMeasure (Fin k)) (n : ℕ) (e : MarkovState k) : ENNReal :=
  ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
    μ (trajToList (k := k) xs)

/-- Evidence polynomial: probability (under parameter `θ`) of landing in evidence class `e` at
horizon `n`, computed by summing `wordProb θ` over the fiber. -/
def W (n : ℕ) (e : MarkovState k) : MarkovParam k → ℝ≥0∞ :=
  fun θ =>
    ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
      wordProb (k := k) θ (trajToList (k := k) xs)

/-! ## `ℝ`-valued evidence polynomials live in the coordinate subalgebra -/

/-- `ℝ`-valued evidence polynomial (finite sum of `wordProbReal`). -/
def Wreal (n : ℕ) (e : MarkovState k) : C(MarkovParam k, ℝ) :=
  (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e)
    |>.sum (fun xs => wordProbReal (k := k) (trajToList (k := k) xs))

lemma Wreal_apply (n : ℕ) (e : MarkovState k) (θ : MarkovParam k) :
    Wreal (k := k) n e θ =
      ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e),
        (wordProbNN (k := k) θ (trajToList (k := k) xs) : ℝ) := by
  classical
  -- unfold and use `wordProbReal_apply`
  simp [Wreal, wordProbReal_apply]

lemma Wreal_mem_coordSubalg (n : ℕ) (e : MarkovState k) :
    Wreal (k := k) n e ∈ coordSubalg (k := k) := by
  classical
  -- `coordSubalg` is closed under finite sums; each `wordProbReal` term lies in it.
  -- We prove this by induction on the filtered finite set.
  let s : Finset (Traj k n) :=
    (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e)
  have hterm : ∀ xs : Traj k n,
      wordProbReal (k := k) (trajToList (k := k) xs) ∈ coordSubalg (k := k) := by
    intro xs
    exact wordProbReal_mem_coordSubalg (k := k) (trajToList (k := k) xs)
  -- Use the Subalgebra sum lemma directly.
  have hsum :
      s.sum (fun xs => wordProbReal (k := k) (trajToList (k := k) xs)) ∈ coordSubalg (k := k) := by
    refine Subalgebra.sum_mem (S := coordSubalg (k := k)) ?_
    intro xs hxs
    exact hterm xs
  -- Unfold `Wreal` and rewrite to the `Finset.sum` form.
  simpa [Wreal, s] using hsum

@[simp] lemma wμ_nonneg (μ : PrefixMeasure (Fin k)) (n : ℕ) (e : MarkovState k) :
    0 ≤ wμ (k := k) μ n e := by
  classical
  simp [wμ]

@[simp] lemma W_nonneg (n : ℕ) (e : MarkovState k) (θ : MarkovParam k) :
    0 ≤ W (k := k) n e θ := by
  classical
  simp [W]

/-! ## Partition-of-unity identities (finite, hence proof-friendly) -/

private lemma sum_wordProb_trajToList_eq_one (θ : MarkovParam k) (n : ℕ) :
    (∑ xs : Traj k n, wordProb (k := k) θ (trajToList (k := k) xs)) = 1 := by
  classical
  -- Package `wordProb` as a finite-alphabet prefix measure and use `prefixPMF`'s normalization.
  -- TODO: build `PrefixMeasure` for `wordProb` and reuse `FiniteAlphabet.prefixPMF`.
  -- First show that singleton masses of a `ProbabilityMeasure (Fin k)` sum to `1` (in `NNReal`).
  have sum_singleton_eq_one (μ0 : MeasureTheory.ProbabilityMeasure (Fin k)) :
      (∑ a : Fin k, μ0 (Set.singleton a)) = 1 := by
    classical
    let μ : Measure (Fin k) := (μ0 : Measure (Fin k))
    -- Work in `ENNReal` first, using the finite partition of `univ` by singletons.
    have hsum0 :
        (∑ a ∈ (Finset.univ : Finset (Fin k)), μ (Set.singleton a)) =
          μ (Finset.univ : Finset (Fin k)) :=
      (MeasureTheory.sum_measure_singleton (μ := μ) (s := (Finset.univ : Finset (Fin k))))
    have hsum :
        (∑ a : Fin k, μ (Set.singleton a)) = μ Set.univ := by
      -- Avoid `simp` on `hsum0` (it would rewrite it to `True` using `[simp]` itself).
      simpa [μ, Finset.coe_univ] using hsum0
    have hμuniv : μ Set.univ = 1 := by
      simp [μ]
    have hsum1 : (∑ a : Fin k, μ (Set.singleton a)) = (1 : ENNReal) := by
      simpa [hμuniv] using hsum
    -- Convert the ENNReal identity to NNReal by `toNNReal`, distributing over finite sums.
    have hf :
        ∀ a ∈ (Finset.univ : Finset (Fin k)), μ (Set.singleton a) ≠ (⊤ : ENNReal) := by
      intro a ha
      simp [μ]
    have htoNN :
        ENNReal.toNNReal (∑ a : Fin k, μ (Set.singleton a)) =
          ∑ a : Fin k, ENNReal.toNNReal (μ (Set.singleton a)) := by
      simpa using
        (ENNReal.toNNReal_sum (s := (Finset.univ : Finset (Fin k)))
          (f := fun a : Fin k => μ (Set.singleton a)) hf)
    have hpm :
        (∑ a : Fin k, μ0 (Set.singleton a)) =
          ∑ a : Fin k, ENNReal.toNNReal (μ (Set.singleton a)) := by
      simp [MeasureTheory.ProbabilityMeasure.coeFn_def, μ]
    calc
      (∑ a : Fin k, μ0 (Set.singleton a))
          = ∑ a : Fin k, ENNReal.toNNReal (μ (Set.singleton a)) := hpm
      _ = ENNReal.toNNReal (∑ a : Fin k, μ (Set.singleton a)) := by
            exact htoNN.symm
      _ = ENNReal.toNNReal (1 : ENNReal) := by
            simp [hsum1]
      _ = 1 := by simp

  -- Markov recursion: show the auxiliary tail kernel is prefix-additive.
  have wordProbAux_additive (prev : Fin k) :
      ∀ xs : List (Fin k),
        (∑ a : Fin k, wordProbAux (k := k) θ prev (xs ++ [a])) =
          wordProbAux (k := k) θ prev xs := by
    intro xs
    induction xs generalizing prev with
    | nil =>
        -- `xs = []`: `wordProbAux prev [a] = stepProb prev a`, and `∑ a, stepProb prev a = 1`.
        have hstep : (∑ a : Fin k, stepProb (k := k) θ prev a) = 1 := by
          simpa [stepProb] using (sum_singleton_eq_one (μ0 := θ.trans prev))
        -- Now simplify the goal to `hstep`.
        simpa [wordProbAux, stepProb, hstep]
    | cons b xs ih =>
        -- Factor out the constant first transition probability.
        have hmul :
            (∑ a : Fin k, stepProb (k := k) θ prev b * wordProbAux (k := k) θ b (xs ++ [a])) =
              stepProb (k := k) θ prev b * ∑ a : Fin k, wordProbAux (k := k) θ b (xs ++ [a]) := by
          -- `∑ a, c * f a = c * ∑ a, f a`.
          simpa using
            (Finset.mul_sum (a := stepProb (k := k) θ prev b)
              (s := (Finset.univ : Finset (Fin k)))
              (f := fun a : Fin k => wordProbAux (k := k) θ b (xs ++ [a]))).symm
        calc
          (∑ a : Fin k, wordProbAux (k := k) θ prev ((b :: xs) ++ [a]))
              = ∑ a : Fin k, stepProb (k := k) θ prev b * wordProbAux (k := k) θ b (xs ++ [a]) := by
                  simp [wordProbAux, List.cons_append]
          _ = stepProb (k := k) θ prev b * ∑ a : Fin k, wordProbAux (k := k) θ b (xs ++ [a]) := hmul
          _ = stepProb (k := k) θ prev b * wordProbAux (k := k) θ b xs := by
                simp [ih (prev := b)]
          _ = wordProbAux (k := k) θ prev (b :: xs) := by
                simp [wordProbAux]

  -- Now show `wordProb` is a `PrefixMeasure`, and use `prefixPMF` normalization.
  let μθ : PrefixMeasure (Fin k) :=
    { toFun := fun xs => wordProb (k := k) θ xs
      root_eq_one' := by
        simp [wordProb, wordProbNN]
      additive' := by
        intro xs
        classical
        cases xs with
        | nil =>
            -- `wordProb [a] = initProb a`, so the sum is `1`.
            have hinitNN : (∑ a : Fin k, initProb (k := k) θ a) = 1 := by
              simpa [initProb] using (sum_singleton_eq_one (μ0 := θ.init))
            have hinitENN : (∑ a : Fin k, (initProb (k := k) θ a : ENNReal)) = 1 := by
              have hcast :
                  ((∑ a : Fin k, initProb (k := k) θ a) : ENNReal) = (1 : ENNReal) := by
                simpa using congrArg (fun t : NNReal => (t : ENNReal)) hinitNN
              -- Rewrite the casted sum to a sum of casts.
              have hcoe :
                  ((∑ a : Fin k, initProb (k := k) θ a) : ENNReal) =
                    ∑ a : Fin k, (initProb (k := k) θ a : ENNReal) := by
                simp
              -- Finish.
              simpa [hcoe] using hcast
            simpa [wordProb, wordProbNN, wordProbAux] using hinitENN
        | cons a xs =>
            -- Factor out the fixed initial probability `initProb a`.
            have hmul :
                (∑ b : Fin k,
                      (initProb (k := k) θ a : ℝ≥0∞) *
                        (wordProbAux (k := k) θ a (xs ++ [b]) : ℝ≥0∞)) =
                  (initProb (k := k) θ a : ℝ≥0∞) *
                    ∑ b : Fin k, (wordProbAux (k := k) θ a (xs ++ [b]) : ℝ≥0∞) := by
              simpa using
                (Finset.mul_sum (a := (initProb (k := k) θ a : ℝ≥0∞))
                  (s := (Finset.univ : Finset (Fin k)))
                  (f := fun b : Fin k => (wordProbAux (k := k) θ a (xs ++ [b]) : ℝ≥0∞))).symm
            -- Use additivity of the auxiliary kernel.
            have haux :
                (∑ b : Fin k, (wordProbAux (k := k) θ a (xs ++ [b]) : ℝ≥0∞)) =
                  (wordProbAux (k := k) θ a xs : ℝ≥0∞) := by
              -- Coerce the NNReal equality, and rewrite casts so the sum is of casts (not a cast of a sum).
              have hNN : (∑ b : Fin k, wordProbAux (k := k) θ a (xs ++ [b])) =
                  wordProbAux (k := k) θ a xs := by
                simpa using (wordProbAux_additive (prev := a) xs)
              have hcast :
                  ((∑ b : Fin k, wordProbAux (k := k) θ a (xs ++ [b])) : ENNReal) =
                    (wordProbAux (k := k) θ a xs : ENNReal) := by
                simpa using congrArg (fun t : NNReal => (t : ENNReal)) hNN
              have hcoe :
                  ((∑ b : Fin k, wordProbAux (k := k) θ a (xs ++ [b])) : ENNReal) =
                    ∑ b : Fin k, (wordProbAux (k := k) θ a (xs ++ [b]) : ENNReal) := by
                simp
              -- Conclude.
              simpa [hcoe] using hcast
            calc
              (∑ b : Fin k, wordProb (k := k) θ ((a :: xs) ++ [b]))
                  = ∑ b : Fin k, (initProb (k := k) θ a : ℝ≥0∞) *
                        (wordProbAux (k := k) θ a (xs ++ [b]) : ℝ≥0∞) := by
                        simp [wordProb, wordProbNN, List.cons_append]
              _ = (initProb (k := k) θ a : ℝ≥0∞) *
                    ∑ b : Fin k, (wordProbAux (k := k) θ a (xs ++ [b]) : ℝ≥0∞) := hmul
              _ = (initProb (k := k) θ a : ℝ≥0∞) *
                    (wordProbAux (k := k) θ a xs : ℝ≥0∞) := by
                      simp [haux]
              _ = wordProb (k := k) θ (a :: xs) := by
                    simp [wordProb, wordProbNN]
    }

  -- `prefixPMF μθ (n+1)` is a PMF on length-`n+1` trajectories.
  have htsum : (∑' xs : Traj k n, μθ (trajToList (k := k) xs)) = 1 := by
    simpa [FiniteAlphabet.prefixPMF, trajToList] using
      (PMF.tsum_coe (FiniteAlphabet.prefixPMF μθ (n + 1)))
  -- Convert the `tsum` on a fintype into a finite sum.
  simpa [tsum_fintype, μθ, trajToList] using htsum

theorem sum_W_eq_one (n : ℕ) (θ : MarkovParam k) :
    (∑ e ∈ stateFinset k n, W (k := k) n e θ) =
      (∑ xs : Traj k n, wordProb (k := k) θ (trajToList (k := k) xs)) := by
  classical
  -- Each trajectory contributes exactly once, to its own evidence class.
  let f : Traj k n → ENNReal := fun xs => wordProb (k := k) θ (trajToList (k := k) xs)
  -- Rewrite the filtered fiber sum as an `ite` over all trajectories.
  have hfilter :
      ∀ e : MarkovState k,
        (∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e), f xs) =
          ∑ xs ∈ trajFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
    intro e
    -- `sum_filter` expands the fiber sum.
    simpa [f] using
      (Finset.sum_filter (s := trajFinset k n) (p := fun xs => stateOfTraj (k := k) xs = e) (f := f))
  -- Now swap the two finite sums.
  have hswap :
      (∑ e ∈ stateFinset k n,
          ∑ xs ∈ trajFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0)) =
        ∑ xs ∈ trajFinset k n,
          ∑ e ∈ stateFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
    exact
      (Finset.sum_comm (s := stateFinset k n) (t := trajFinset k n)
        (f := fun e xs => if stateOfTraj (k := k) xs = e then f xs else 0))
  -- For a fixed trajectory, the inner sum over `e` collapses to `f xs`.
  have hcollapse :
      ∀ xs : Traj k n,
        (∑ e ∈ stateFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0)) = f xs := by
    intro xs
    have hmem : stateOfTraj (k := k) xs ∈ stateFinset k n :=
      stateOfTraj_mem_stateFinset (k := k) xs
    -- `sum_ite_eq` evaluates the sum of a single-support indicator.
    -- `Finset.sum_ite_eq` is stated using `e = a`; rewrite with `eq_comm`.
    simp [eq_comm, hmem]
  -- Put it together.
  calc
    (∑ e ∈ stateFinset k n, W (k := k) n e θ)
        = ∑ e ∈ stateFinset k n,
            ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e), f xs := by
              simp [W, f]
    _ = ∑ e ∈ stateFinset k n,
            ∑ xs ∈ trajFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
              refine Finset.sum_congr rfl ?_
              intro e he
              simp [hfilter e]
    _ = ∑ xs ∈ trajFinset k n,
            ∑ e ∈ stateFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
              simp [hswap]
    _ = ∑ xs ∈ trajFinset k n, f xs := by
          refine Finset.sum_congr rfl ?_
          intro xs hxs
          simp [hcollapse xs]
    _ = ∑ xs : Traj k n, f xs := by
          simp [trajFinset]
    _ = ∑ xs : Traj k n, wordProb (k := k) θ (trajToList (k := k) xs) := by
          rfl

theorem sum_W_eq_one' (n : ℕ) (θ : MarkovParam k) :
    (∑ e ∈ stateFinset k n, W (k := k) n e θ) = 1 := by
  classical
  -- Combine regrouping with the fact that the Markov kernel is a prefix measure.
  have hregroup := sum_W_eq_one (k := k) n θ
  -- TODO: finish once `sum_wordProb_trajToList_eq_one` is proved.
  simpa [hregroup] using (sum_wordProb_trajToList_eq_one (k := k) θ n)

-- Same statement with the `E_n` alias.
theorem sum_W_eq_one_E (n : ℕ) (θ : MarkovParam k) :
    (∑ e ∈ E_n k n, W (k := k) n e θ) = 1 := by
  simpa [E_n] using (sum_W_eq_one' (k := k) n θ)

theorem sum_wμ_eq_one (μ : PrefixMeasure (Fin k)) (n : ℕ) :
    (∑ e ∈ stateFinset k n, wμ (k := k) μ n e) =
      (∑ xs : Traj k n, μ (trajToList (k := k) xs)) := by
  classical
  let f : Traj k n → ENNReal := fun xs => μ (trajToList (k := k) xs)
  have hfilter :
      ∀ e : MarkovState k,
        (∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e), f xs) =
          ∑ xs ∈ trajFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
    intro e
    simpa [f] using
      (Finset.sum_filter (s := trajFinset k n) (p := fun xs => stateOfTraj (k := k) xs = e) (f := f))
  have hswap :
      (∑ e ∈ stateFinset k n,
          ∑ xs ∈ trajFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0)) =
        ∑ xs ∈ trajFinset k n,
          ∑ e ∈ stateFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
    exact
      (Finset.sum_comm (s := stateFinset k n) (t := trajFinset k n)
        (f := fun e xs => if stateOfTraj (k := k) xs = e then f xs else 0))
  have hcollapse :
      ∀ xs : Traj k n,
        (∑ e ∈ stateFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0)) = f xs := by
    intro xs
    have hmem : stateOfTraj (k := k) xs ∈ stateFinset k n :=
      stateOfTraj_mem_stateFinset (k := k) xs
    simp [eq_comm, hmem]
  calc
    (∑ e ∈ stateFinset k n, wμ (k := k) μ n e)
        = ∑ e ∈ stateFinset k n,
            ∑ xs ∈ (trajFinset k n).filter (fun xs => stateOfTraj (k := k) xs = e), f xs := by
              simp [wμ, f]
    _ = ∑ e ∈ stateFinset k n,
            ∑ xs ∈ trajFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
                refine Finset.sum_congr rfl ?_
                intro e he
                simp [hfilter e]
      _ = ∑ xs ∈ trajFinset k n,
              ∑ e ∈ stateFinset k n, (if stateOfTraj (k := k) xs = e then f xs else 0) := by
                simp [hswap]
    _ = ∑ xs ∈ trajFinset k n, f xs := by
            refine Finset.sum_congr rfl ?_
            intro xs hxs
            simp [hcollapse xs]
    _ = ∑ xs : Traj k n, f xs := by
          simp [trajFinset]
    _ = ∑ xs : Traj k n, μ (trajToList (k := k) xs) := by
          rfl

theorem sum_wμ_eq_one' (μ : PrefixMeasure (Fin k)) (n : ℕ) :
    (∑ e ∈ stateFinset k n, wμ (k := k) μ n e) = 1 := by
  classical
  have hregroup := sum_wμ_eq_one (k := k) (μ := μ) n
  -- The RHS is exactly the normalization statement already proved for `prefixPMF`.
  have hsum : (∑ xs : Traj k n, μ (trajToList (k := k) xs)) = 1 := by
    have htsum : (∑' xs : Traj k n, μ (trajToList (k := k) xs)) = 1 := by
      simpa [FiniteAlphabet.prefixPMF, trajToList] using
        (PMF.tsum_coe (FiniteAlphabet.prefixPMF μ (n + 1)))
    simpa [tsum_fintype] using htsum
  simp [hregroup, hsum]

-- Same statement with the `E_n` alias.
theorem sum_wμ_eq_one_E (μ : PrefixMeasure (Fin k)) (n : ℕ) :
    (∑ e ∈ E_n k n, wμ (k := k) μ n e) = 1 := by
  simpa [E_n] using (sum_wμ_eq_one' (k := k) (μ := μ) n)


end MarkovDeFinettiHard

end Mettapedia.Logic
