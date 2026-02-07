import Mettapedia.Logic.MarkovDeFinettiHardEuler
import Mettapedia.Logic.MarkovDeFinettiHardApprox
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Zip

/-!
# Markov de Finetti (Hard Direction) — Excursion bookkeeping

This file sets up lightweight combinatorial facts about **returns to the start**
and the positions of those returns inside a finite trajectory.  These lemmas are
used by the excursion‑based proof of the Diaconis–Freedman good‑state bound.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHardExcursions

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiHardEuler
open Mettapedia.Logic.MarkovDeFinettiHard

variable {k : ℕ}

/-! ## Return positions -/

/-- Positions in a trajectory where the state equals the start state. -/
def returnPositions {n : ℕ} (xs : Traj k n) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => xs i = xs 0)

/-- Return positions as a sorted list. -/
def returnPositionsList {n : ℕ} (xs : Traj k n) : List (Fin (n + 1)) :=
  (returnPositions (k := k) xs).sort (· ≤ ·)

@[simp] lemma length_returnPositionsList {n : ℕ} (xs : Traj k n) :
    (returnPositionsList (k := k) xs).length =
      (returnPositions (k := k) xs).card := by
  classical
  -- Unfold and use `Finset.length_sort`.
  dsimp [returnPositionsList]
  exact (Finset.length_sort (s := returnPositions (k := k) xs) (r := (· ≤ ·)))

/-! ## Excursion count -/

/-- Number of excursions = number of returns minus the initial position. -/
def numExcursions {n : ℕ} (xs : Traj k n) : ℕ :=
  (returnPositions (k := k) xs).card - 1

/-! ## Excursion pairs -/

/-- Consecutive return positions, used to define excursions. -/
def excursionPairs {n : ℕ} (xs : Traj k n) :
    List (Fin (n + 1) × Fin (n + 1)) :=
  (returnPositionsList (k := k) xs).zip (returnPositionsList (k := k) xs).tail

/-! ## Adjacent-pair order facts -/

private lemma mem_zip_tail_fst_lt_snd_of_sorted
    {α : Type*} [LinearOrder α] {l : List α}
    (hs : l.SortedLT) {p : α × α} (hp : p ∈ l.zip l.tail) :
    p.1 < p.2 := by
  induction l with
  | nil =>
      simp at hp
  | cons a tl ih =>
      cases tl with
      | nil =>
          simp at hp
      | cons b tl2 =>
          simp [List.tail] at hp
          rcases hp with hhead | htail
          · rcases hhead with ⟨rfl, rfl⟩
            have hsPair : List.Pairwise (· < ·) (a :: b :: tl2) :=
              (List.sortedLT_iff_pairwise.mp hs)
            cases hsPair with
            | cons hrel _ =>
                exact hrel b (by simp)
          · have hsTail : (b :: tl2).SortedLT := by
              have hsPair : List.Pairwise (· < ·) (a :: b :: tl2) :=
                (List.sortedLT_iff_pairwise.mp hs)
              cases hsPair with
              | cons _ htailPair =>
                  exact (List.sortedLT_iff_pairwise.mpr htailPair)
            exact ih hsTail htail

lemma fst_lt_snd_of_mem_excursionPairs {n : ℕ} (xs : Traj k n)
    {p : Fin (n + 1) × Fin (n + 1)} (hp : p ∈ excursionPairs (k := k) xs) :
    p.1 < p.2 := by
  exact mem_zip_tail_fst_lt_snd_of_sorted
    (hs := Finset.sortedLT_sort (returnPositions (k := k) xs))
    (hp := by simpa [excursionPairs] using hp)

private lemma mem_zip_tail_of_succ_lt_length
    {α : Type*} (l : List α) (i : ℕ) (hi : i + 1 < l.length) :
    (l[i], l[i + 1]) ∈ l.zip l.tail := by
  apply List.mem_iff_getElem.mpr
  refine ⟨i, ?_, ?_⟩
  · have hiZip : i < l.length - 1 := by
      omega
    simpa [List.length_zip, List.length_tail,
      Nat.min_eq_right (Nat.sub_le _ _)] using hiZip
  · simp [List.getElem_tail]

/-- If `a` and `b` are return positions with no return strictly between them,
then `(a,b)` appears in `excursionPairs`. -/
lemma mem_excursionPairs_of_return_consecutive
    {n : ℕ} (xs : Traj k n) (a b : Fin (n + 1))
    (ha : a ∈ returnPositions (k := k) xs)
    (hb : b ∈ returnPositions (k := k) xs)
    (hab : a < b)
    (hgap : ∀ c ∈ returnPositions (k := k) xs, ¬ (a < c ∧ c < b)) :
    (a, b) ∈ excursionPairs (k := k) xs := by
  classical
  let l : List (Fin (n + 1)) := returnPositionsList (k := k) xs
  have hs : l.SortedLT := by
    simpa [l, returnPositionsList] using
      (Finset.sortedLT_sort (returnPositions (k := k) xs))
  have haL : a ∈ l := by
    simpa [l, returnPositionsList] using
      (Finset.mem_sort (s := returnPositions (k := k) xs) (r := (· ≤ ·))).2 ha
  have hbL : b ∈ l := by
    simpa [l, returnPositionsList] using
      (Finset.mem_sort (s := returnPositions (k := k) xs) (r := (· ≤ ·))).2 hb
  rcases (List.mem_iff_getElem.mp haL) with ⟨ia, hia_lt, hia⟩
  rcases (List.mem_iff_getElem.mp hbL) with ⟨ib, hib_lt, hib⟩
  have hab_lt : ia < ib := by
    have hlt_ab : l[ia] < l[ib] := by
      simpa [hia, hib] using hab
    exact (List.SortedLT.getElem_lt_getElem_iff
      (l := l) hs (i := ia) (j := ib) (hi := hia_lt) (hj := hib_lt)).1 hlt_ab
  have hnot_skip : ¬ (ia + 1 < ib) := by
    intro hskip
    have hic_lt : ia + 1 < l.length := by
      exact lt_trans hskip hib_lt
    let c : Fin (n + 1) := l[ia + 1]
    have hcMemL : c ∈ l := by
      exact List.getElem_mem hic_lt
    have hcMemS : c ∈ returnPositions (k := k) xs := by
      simpa [l, returnPositionsList] using
        (Finset.mem_sort (s := returnPositions (k := k) xs) (r := (· ≤ ·))).1 hcMemL
    have hac : a < c := by
      have hidx : ia < ia + 1 := by omega
      have hlt := (List.SortedLT.getElem_lt_getElem_iff
        (l := l) hs (i := ia) (j := ia + 1) (hi := hia_lt) (hj := hic_lt)).2 hidx
      simpa [hia] using hlt
    have hcb : c < b := by
      have hidx : ia + 1 < ib := hskip
      have hlt := (List.SortedLT.getElem_lt_getElem_iff
        (l := l) hs (i := ia + 1) (j := ib) (hi := hic_lt) (hj := hib_lt)).2 hidx
      simpa [hib] using hlt
    exact (hgap c hcMemS) ⟨hac, hcb⟩
  have hib_eq : ib = ia + 1 := by
    omega
  have hia1 : l[ia + 1] = b := by
    simpa [hib_eq] using hib
  have hi : ia + 1 < l.length := by
    simpa [hib_eq] using hib_lt
  have hmem_zip : (l[ia], l[ia + 1]) ∈ l.zip l.tail :=
    mem_zip_tail_of_succ_lt_length l ia hi
  simpa [excursionPairs, l, hia, hia1] using hmem_zip

@[simp] lemma length_excursionPairs {n : ℕ} (xs : Traj k n) :
    (excursionPairs (k := k) xs).length = numExcursions (k := k) xs := by
  classical
  -- Let `l` be the return positions list; it is nonempty.
  let l : List (Fin (n + 1)) := returnPositionsList (k := k) xs
  have hlen : (returnPositions (k := k) xs).card = l.length := by
    simp [l, length_returnPositionsList]
  have hpos : 0 < l.length := by
    have hmem : (0 : Fin (n + 1)) ∈ returnPositions (k := k) xs := by
      simp [returnPositions]
    have hcardpos : 0 < (returnPositions (k := k) xs).card := by
      exact Finset.card_pos.mpr ⟨0, hmem⟩
    simp [hlen] at hcardpos
    exact hcardpos
  -- Split on the list form, keeping the defining equation.
  cases h : l with
  | nil =>
      -- contradiction: `l.length = 0`
      have hzero : l.length = 0 := by simp [h]
      have hpos0 : (0 : ℕ) < 0 := by
        have hpos' : 0 < l.length := hpos
        rw [hzero] at hpos'
        exact hpos'
      exact (False.elim (Nat.lt_irrefl 0 hpos0))
  | cons a t =>
      -- `zip` with tail has length `t.length`.
      have hlenzip : (excursionPairs (k := k) xs).length = t.length := by
        simp [excursionPairs, l, h, List.length_zip]
      -- `numExcursions = (card) - 1 = t.length`.
      have hlen' : (returnPositions (k := k) xs).card = t.length + 1 := by
        simpa [h] using hlen
      have hnum : numExcursions xs = t.length := by
        change MarkovDeFinettiHardExcursions.numExcursions (k := k) xs = t.length
        unfold MarkovDeFinettiHardExcursions.numExcursions
        calc
          (returnPositions (k := k) xs).card - 1 = (t.length + 1) - 1 := by
            rw [hlen']
          _ = t.length := by
            exact Nat.add_sub_cancel _ _
      exact hlenzip.trans hnum.symm

@[simp] lemma mem_returnPositions {n : ℕ} (xs : Traj k n) (i : Fin (n + 1)) :
    i ∈ returnPositions (k := k) xs ↔ xs i = xs 0 := by
  simp [returnPositions]

@[simp] lemma mem_returnPositions_zero {n : ℕ} (xs : Traj k n) :
    (0 : Fin (n + 1)) ∈ returnPositions (k := k) xs := by
  simp [returnPositions]

/-- The return positions consist of index `0` plus the indices `succ i`
where `xs (succ i) = xs 0`. -/
lemma returnPositions_card
    {n : ℕ} (xs : Traj k n) :
    (returnPositions (k := k) xs).card =
      (Finset.univ.filter (fun i : Fin n => xs i.succ = xs 0)).card + 1 := by
  classical
  -- Split the return positions into `{0}` and successors.
  have hsplit :
      returnPositions (k := k) xs =
        ({0} : Finset (Fin (n + 1))) ∪
          (Finset.image Fin.succ
            (Finset.univ.filter (fun i : Fin n => xs i.succ = xs 0))) := by
    ext i
    constructor
    · intro hi
      have hi' : xs i = xs 0 := (mem_returnPositions (k := k) xs i).1 hi
      by_cases h0 : (i : ℕ) = 0
      · have : i = 0 := by
          apply Fin.ext
          simpa using h0
        subst this
        simp
      · -- i = succ j for some j
        have hpos : 0 < (i : ℕ) := Nat.pos_of_ne_zero h0
        have hpred : (i : ℕ) - 1 < n := by
          have hi_lt : (i : ℕ) < n + 1 := i.is_lt
          have hi_le : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp hi_lt
          have hpred_lt : (i : ℕ) - 1 < (i : ℕ) := by
            -- `n - 1 < n` for positive `n`
            have : Nat.pred (i : ℕ) < (i : ℕ) := Nat.pred_lt (Nat.ne_of_gt hpos)
            simpa [Nat.pred_eq_sub_one] using this
          exact lt_of_lt_of_le hpred_lt hi_le
        let j : Fin n := ⟨(i : ℕ) - 1, hpred⟩
        have hij : Fin.succ j = i := by
          apply Fin.ext
          simp [j, Nat.sub_add_cancel (Nat.succ_le_iff.mp hpos)]
        have hmem : j ∈ Finset.univ.filter (fun t : Fin n => xs t.succ = xs 0) := by
          simp [Finset.mem_filter, hi', hij]
        have himage : i ∈ Finset.image Fin.succ
            (Finset.univ.filter (fun t : Fin n => xs t.succ = xs 0)) := by
          exact Finset.mem_image.2 ⟨j, hmem, hij⟩
        exact Finset.mem_union.2 (Or.inr himage)
    · intro hi
      rcases Finset.mem_union.1 hi with hi | hi
      · -- i = 0
        have : i = 0 := by
          simpa using (Finset.mem_singleton.1 hi)
        subst this
        simp [returnPositions]
      · rcases Finset.mem_image.1 hi with ⟨j, hj, rfl⟩
        have hj' : xs j.succ = xs 0 := by
          simpa using (Finset.mem_filter.1 hj).2
        simpa [returnPositions] using hj'
  have hdisjoint :
      Disjoint ({0} : Finset (Fin (n + 1)))
        (Finset.image Fin.succ
          (Finset.univ.filter (fun i : Fin n => xs i.succ = xs 0))) := by
    classical
    refine Finset.disjoint_left.2 ?_
    intro i hi0 hi1
    have hi0' : i = 0 := by
      simp [Finset.mem_singleton] at hi0
      exact hi0
    subst hi0'
    rcases Finset.mem_image.1 hi1 with ⟨j, _hj, hij⟩
    -- `Fin.succ j` is never `0`
    exact (Fin.succ_ne_zero j) hij
  let s : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => xs i.succ = xs 0)
  have hsplit' :
      returnPositions (k := k) xs =
        ({0} : Finset (Fin (n + 1))) ∪ Finset.image Fin.succ s := by
    simp [hsplit, s]
  have hcard_image :
      (Finset.image Fin.succ s).card = s.card := by
    refine Finset.card_image_of_injective (s := s) (f := Fin.succ) ?_
    intro i j h
    apply Fin.ext
    simpa using congrArg Fin.val h
  have hcard_union : (returnPositions (k := k) xs).card = 1 + s.card := by
    calc
      (returnPositions (k := k) xs).card
          = (({0} : Finset (Fin (n + 1))) ∪
              (Finset.image Fin.succ s)).card := by
            simp [hsplit']
      _ = ({0} : Finset (Fin (n + 1))).card +
            (Finset.image Fin.succ s).card := by
            simp [add_comm]
      _ = 1 + s.card := by
            simp [hcard_image]
  simpa [Nat.add_comm] using hcard_union

/-- The number of return positions equals `returnsToStart + 1`. -/
lemma card_returnPositions_eq_returnsToStart_add_one
    {n : ℕ} (xs : Traj k n) :
    (returnPositions (k := k) xs).card =
      returnsToStart (k := k) (stateOfTraj (k := k) xs) + 1 := by
  classical
  have hret :=
    returnsToStart_stateOfTraj (k := k) (xs := xs)
  -- `returnsToStart` counts the `succ` indices; add 1 for index 0.
  have hcard := returnPositions_card (k := k) xs
  -- Rewrite the RHS using `hret`.
  simpa [hret] using hcard

lemma numExcursions_eq_returnsToStart
    {n : ℕ} (xs : Traj k n) :
    numExcursions (k := k) xs =
      returnsToStart (k := k) (stateOfTraj (k := k) xs) := by
  classical
  have hcard := card_returnPositions_eq_returnsToStart_add_one (k := k) (xs := xs)
  -- Subtract 1 from both sides.
  unfold numExcursions
  -- `a + 1 - 1 = a`
  simpa [Nat.add_sub_cancel] using congrArg (fun t => t - 1) hcard

end MarkovDeFinettiHardExcursions

end Mettapedia.Logic
