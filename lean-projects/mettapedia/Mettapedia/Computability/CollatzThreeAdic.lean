import Std.Data.HashMap
import Std.Data.HashMap.Lemmas

/-!
# Exact 3-adic reverse-Collatz counting

This file implements the exact sparse 3-adic state dynamic program for counting
reverse-Collatz parity strings of fixed bit-length and fixed Hamming weight.

For a reverse parity string with `k` odd steps and zero-gap sequence
`t₀, …, tₖ`, starting from `A₀ = 1`, the odd inverse updates are

`A_{j+1} = (2^(tⱼ+1) Aⱼ - 1) / 3`.

When `r` odd steps remain, the next exact residue only depends on the current
value modulo `3^r`, so a sparse DP over `(usedZeros, residue)` states gives an
exact counting instrument for the underlying reverse-Collatz combinatorics.
-/

namespace CollatzThreeAdic

open scoped Classical

structure GapResidueKey where
  usedZeros : Nat
  residue : Nat
deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable, Inhabited

abbrev GapResidueStage := Std.HashMap GapResidueKey Nat

structure GapTransition where
  gap : Nat
  nextKey : GapResidueKey
deriving Repr, BEq, DecidableEq, Inhabited

def stageMass (stage : GapResidueStage) : Nat :=
  stage.toList.foldl (fun acc entry => acc + entry.2) 0

def stageStateCount (stage : GapResidueStage) : Nat :=
  stage.toList.foldl (fun acc _ => acc + 1) 0

def stageWeightedSum (weight : GapResidueKey → Nat) (stage : GapResidueStage) : Nat :=
  stage.toList.foldl (fun acc entry => acc + entry.2 * weight entry.1) 0

def stageInsertAdd
    (stage : GapResidueStage) (key : GapResidueKey) (count : Nat) : GapResidueStage :=
  stage.insert key (stage.getD key 0 + count)

def residueGapUpper (bitLength oddSteps : Nat) (key : GapResidueKey) : Nat :=
  bitLength - oddSteps - key.usedZeros

def residueGapNextKey? (bitLength oddSteps placed : Nat) (key : GapResidueKey) (gap : Nat) :
    Option GapResidueKey :=
  if placed < oddSteps then
    let remaining := oddSteps - placed
    let modulus := 3 ^ remaining
    let nextModulus := 3 ^ (remaining - 1)
    if gap ≤ residueGapUpper bitLength oddSteps key then
      let scaled := ((2 ^ (gap + 1)) * key.residue) % modulus
      let numeratorMod := (scaled + modulus - 1) % modulus
      if numeratorMod % 3 == 0 then
        if !(placed == 0 && gap == 1) then
          let nextResidue := (numeratorMod / 3) % nextModulus
          if remaining == 1 || nextResidue % 3 != 0 then
            some { usedZeros := key.usedZeros + gap, residue := nextResidue }
          else
            none
        else
          none
      else
        none
    else
      none
  else
    none

def stateTransitionsList (bitLength oddSteps placed : Nat) (key : GapResidueKey) :
    List GapTransition :=
  (List.range (residueGapUpper bitLength oddSteps key + 1)).filterMap fun gap =>
    (residueGapNextKey? bitLength oddSteps placed key gap).map fun nextKey =>
      { gap := gap, nextKey := nextKey }

/-- Exact successor transitions from one residue-state, labeled by the chosen
zero gap before the next odd inverse step. -/
def stateTransitions (bitLength oddSteps placed : Nat) (key : GapResidueKey) :
    Array GapTransition :=
  if placed < oddSteps then
    (stateTransitionsList bitLength oddSteps placed key).toArray
  else
    #[]

/-- One exact 3-adic transition step in the zero-gap DP. -/
def stepStage (bitLength oddSteps placed : Nat) (stage : GapResidueStage) : GapResidueStage :=
  if placed < oddSteps then
    stage.toList.foldl
      (fun next entry =>
        let key := entry.1
        let count := entry.2
        Id.run do
          let mut next := next
          for tr in stateTransitions bitLength oddSteps placed key do
            next := stageInsertAdd next tr.nextKey count
          pure next)
      (Std.HashMap.emptyWithCapacity (stage.size * 2 + 1))
  else
    {}

/-- Recursion-friendly residue-stage chain: stage `0` is the singleton seed at
residue depth `oddSteps`, and stage `κ + 1` applies one residue-side kernel
step at odd placement `κ`. This is the theorem-friendly public timeline that
the mass surfaces `sigmas`, `sigma`, and `totalCount` are intended to expose. -/
private def stageChain (bitLength oddSteps : Nat) : Nat → GapResidueStage
  | 0 => stageInsertAdd {} { usedZeros := 0, residue := 1 % (3 ^ oddSteps) } 1
  | n + 1 => stepStage bitLength oddSteps n (stageChain bitLength oddSteps n)

/-- All DP stages, from `κ = 0` through `κ = oddSteps`. -/
def stages (bitLength oddSteps : Nat) : Array GapResidueStage :=
  Id.run do
    let mut out := Array.replicate (oddSteps + 1) ({} : GapResidueStage)
    let initStage : GapResidueStage :=
      stageInsertAdd {} { usedZeros := 0, residue := 1 } 1
    out := out.set! 0 initStage
    let mut current := initStage
    for placed in [0:oddSteps] do
      let next := stepStage bitLength oddSteps placed current
      out := out.set! (placed + 1) next
      current := next
    pure out

def sigmas (bitLength oddSteps : Nat) : Array Nat :=
  ((List.range (oddSteps + 1)).map fun placed =>
    stageMass (stageChain bitLength oddSteps placed)).toArray

def stateCounts (bitLength oddSteps : Nat) : Array Nat :=
  (stages bitLength oddSteps).map stageStateCount

def sigma (bitLength oddSteps placed : Nat) : Nat :=
  match (sigmas bitLength oddSteps)[placed]? with
  | some count => count
  | none => 0

def totalCount (bitLength oddSteps : Nat) : Nat :=
  sigma bitLength oddSteps oddSteps

private theorem foldl_add_entrySnd_eq_sum_map_snd (l : List (GapResidueKey × Nat)) (init : Nat) :
    l.foldl (fun acc entry => acc + entry.snd) init = init + (l.map Prod.snd).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (init := init + x.snd)

private theorem sum_map_snd_eq_of_perm {l₁ l₂ : List (GapResidueKey × Nat)}
    (h : l₁.Perm l₂) :
    (l₁.map Prod.snd).sum = (l₂.map Prod.snd).sum := by
  simpa using List.Perm.sum_nat (h.map Prod.snd)

private theorem foldl_add_entryWeighted_eq_sum_map
    (weight : GapResidueKey → Nat) (l : List (GapResidueKey × Nat)) (init : Nat) :
    l.foldl (fun acc entry => acc + entry.snd * weight entry.fst) init =
      init + (l.map (fun entry => entry.snd * weight entry.fst)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (init := init + x.snd * weight x.fst)

private theorem sum_weighted_eq_of_perm
    (weight : GapResidueKey → Nat) {l₁ l₂ : List (GapResidueKey × Nat)} (h : l₁.Perm l₂) :
    (l₁.map (fun entry => entry.2 * weight entry.1)).sum =
      (l₂.map (fun entry => entry.2 * weight entry.1)).sum := by
  simpa using List.Perm.sum_nat (h.map (fun entry => entry.2 * weight entry.1))

private theorem insert_same_getD_equiv (stage : GapResidueStage) (key : GapResidueKey)
    (hmem : key ∈ stage) :
    Std.HashMap.Equiv (stage.insert key (stage.getD key 0)) stage := by
  apply Std.HashMap.Equiv.of_forall_getElem?_eq
  intro a
  rw [Std.HashMap.getElem?_insert]
  by_cases hka : key == a
  · have hmema : a ∈ stage := (Std.HashMap.mem_congr (m := stage) hka).1 hmem
    have hs : stage[a]? = some (stage.getD key 0) := by
      rw [Std.HashMap.getElem?_eq_some_getD (a := a) (fallback := 0) hmema]
      simpa using
        (Std.HashMap.getD_congr (m := stage) (a := key) (b := a) (fallback := 0) hka).symm
    simp [hka, hs]
  · simp [hka]

private theorem filter_eq_self_of_not_mem_key_eq (stage : GapResidueStage) (key : GapResidueKey)
    (hmem : ¬ key ∈ stage) :
    stage.toList.filter (fun x => !decide (key = x.1)) = stage.toList := by
  apply List.filter_eq_self.2
  intro x hx
  have hxsome : stage[x.1]? = some x.2 := (Std.HashMap.mem_toList_iff_getElem?_eq_some).1 hx
  have hxmem : x.1 ∈ stage := by
    apply (Std.HashMap.isSome_getElem?_iff_mem (m := stage) (a := x.1)).mp
    simp [hxsome]
  have hneq : key ≠ x.1 := by
    intro hkx
    apply hmem
    simpa [hkx] using hxmem
  simp [hneq]

theorem stageMass_eq_toListFoldl (stage : GapResidueStage) :
    stageMass stage = stage.toList.foldl (fun acc entry => acc + entry.2) 0 := by
  rfl

theorem stageMass_eq_sum_map_snd (stage : GapResidueStage) :
    stageMass stage = (stage.toList.map Prod.snd).sum := by
  simpa [stageMass] using foldl_add_entrySnd_eq_sum_map_snd stage.toList 0

theorem stageWeightedSum_eq_sum_map (weight : GapResidueKey → Nat) (stage : GapResidueStage) :
    stageWeightedSum weight stage =
      (stage.toList.map (fun entry => entry.2 * weight entry.1)).sum := by
  simpa [stageWeightedSum] using foldl_add_entryWeighted_eq_sum_map weight stage.toList 0

theorem stageMass_stageInsertAdd (stage : GapResidueStage) (key : GapResidueKey) (count : Nat) :
    stageMass (stageInsertAdd stage key count) = stageMass stage + count := by
  let old := stage.getD key 0
  by_cases hmem : key ∈ stage
  · have hpermOld : stage.toList.Perm
        ((key, old) :: stage.toList.filter (fun x => decide ¬ (key == x.1) = true)) := by
      exact (Std.HashMap.Equiv.toList_perm (insert_same_getD_equiv stage key hmem)).symm.trans
        (Std.HashMap.toList_insert_perm (m := stage) (k := key) (v := old))
    have hpermNew : (stageInsertAdd stage key count).toList.Perm
        ((key, old + count) :: stage.toList.filter (fun x => decide ¬ (key == x.1) = true)) := by
      unfold stageInsertAdd
      simpa [old] using
        (Std.HashMap.toList_insert_perm (m := stage) (k := key) (v := stage.getD key 0 + count))
    rw [stageMass_eq_sum_map_snd, stageMass_eq_sum_map_snd]
    rw [(sum_map_snd_eq_of_perm hpermNew), (sum_map_snd_eq_of_perm hpermOld)]
    simp [old, Nat.add_assoc, Nat.add_comm]
  · have hpermNew : (stageInsertAdd stage key count).toList.Perm
        ((key, count) :: stage.toList) := by
      unfold stageInsertAdd
      simpa [Std.HashMap.getD_eq_fallback hmem, filter_eq_self_of_not_mem_key_eq stage key hmem] using
        (Std.HashMap.toList_insert_perm (m := stage) (k := key) (v := stage.getD key 0 + count))
    rw [stageMass_eq_sum_map_snd]
    rw [(sum_map_snd_eq_of_perm hpermNew)]
    simp [stageMass_eq_sum_map_snd, Nat.add_comm]

theorem stageWeightedSum_stageInsertAdd
    (weight : GapResidueKey → Nat)
    (stage : GapResidueStage) (key : GapResidueKey) (count : Nat) :
    stageWeightedSum weight (stageInsertAdd stage key count) =
      stageWeightedSum weight stage + count * weight key := by
  let old := stage.getD key 0
  by_cases hmem : key ∈ stage
  · have hpermOld : stage.toList.Perm
        ((key, old) :: stage.toList.filter (fun x => decide ¬ (key == x.1) = true)) := by
      exact (Std.HashMap.Equiv.toList_perm (insert_same_getD_equiv stage key hmem)).symm.trans
        (Std.HashMap.toList_insert_perm (m := stage) (k := key) (v := old))
    have hpermNew : (stageInsertAdd stage key count).toList.Perm
        ((key, old + count) :: stage.toList.filter (fun x => decide ¬ (key == x.1) = true)) := by
      unfold stageInsertAdd
      simpa [old] using
        (Std.HashMap.toList_insert_perm (m := stage) (k := key) (v := stage.getD key 0 + count))
    rw [stageWeightedSum_eq_sum_map, stageWeightedSum_eq_sum_map]
    rw [sum_weighted_eq_of_perm weight hpermNew, sum_weighted_eq_of_perm weight hpermOld]
    simp [old, Nat.add_assoc, Nat.add_comm, Nat.right_distrib]
  · have hpermNew : (stageInsertAdd stage key count).toList.Perm
        ((key, count) :: stage.toList) := by
      unfold stageInsertAdd
      simpa [Std.HashMap.getD_eq_fallback hmem, filter_eq_self_of_not_mem_key_eq stage key hmem] using
        (Std.HashMap.toList_insert_perm (m := stage) (k := key) (v := stage.getD key 0 + count))
    rw [stageWeightedSum_eq_sum_map]
    rw [sum_weighted_eq_of_perm weight hpermNew]
    rw [stageWeightedSum_eq_sum_map]
    simp [Nat.add_comm]

private theorem stageMass_foldl_transitionList_add_eq
    (trs : List GapTransition) (init : GapResidueStage) (count : Nat) :
    stageMass (trs.foldl (fun st tr => stageInsertAdd st tr.nextKey count) init) =
      stageMass init + count * trs.length := by
  induction trs generalizing init with
  | nil => simp
  | cons tr trs ih =>
      simp [List.foldl_cons, stageMass_stageInsertAdd, ih, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm, Nat.left_distrib]

private theorem stageMass_foldl_transitionArray_add_eq
    (trs : Array GapTransition) (init : GapResidueStage) (count : Nat) :
    stageMass (trs.foldl (fun st tr => stageInsertAdd st tr.nextKey count) init) =
      stageMass init + count * trs.size := by
  rw [← Array.foldl_toList
    (xs := trs) (f := fun st tr => stageInsertAdd st tr.nextKey count) (init := init)]
  simpa using
    stageMass_foldl_transitionList_add_eq (trs := trs.toList) (init := init) (count := count)

private theorem foldl_add_transitionSize_eq
    (bitLength oddSteps placed : Nat)
    (entries : List (GapResidueKey × Nat)) (init : Nat) :
    entries.foldl
        (fun acc entry => acc + entry.2 * (stateTransitions bitLength oddSteps placed entry.1).size)
        init =
      init +
        entries.foldl
          (fun acc entry => acc + entry.2 * (stateTransitions bitLength oddSteps placed entry.1).size)
          0 := by
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      rw [List.foldl_cons, List.foldl_cons]
      rw [ih (init + entry.2 * (stateTransitions bitLength oddSteps placed entry.1).size)]
      simp
      rw [ih (entry.2 * (stateTransitions bitLength oddSteps placed entry.1).size)]
      simp [Nat.add_assoc]

private theorem stageMass_foldl_entries_eq
    (bitLength oddSteps placed : Nat)
    (entries : List (GapResidueKey × Nat)) (init : GapResidueStage) :
    stageMass
      (entries.foldl
        (fun next entry =>
          (stateTransitions bitLength oddSteps placed entry.1).foldl
            (fun st tr => stageInsertAdd st tr.nextKey entry.2) next)
        init) =
      stageMass init +
        entries.foldl
          (fun acc entry => acc + entry.2 * (stateTransitions bitLength oddSteps placed entry.1).size)
          0 := by
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      simp [List.foldl_cons]
      rw [ih]
      rw [stageMass_foldl_transitionArray_add_eq]
      have hfold := foldl_add_transitionSize_eq bitLength oddSteps placed entries
        (entry.2 * (stateTransitions bitLength oddSteps placed entry.1).size)
      rw [hfold]
      omega

theorem stageMass_stepStage_eq_transitionSizeSum
    (bitLength oddSteps placed : Nat) (stage : GapResidueStage) :
    stageMass (stepStage bitLength oddSteps placed stage) =
      if placed < oddSteps then
        stage.toList.foldl
          (fun acc entry => acc + entry.2 * (stateTransitions bitLength oddSteps placed entry.1).size)
          0
      else 0 := by
  unfold stepStage
  by_cases hplaced : placed < oddSteps
  · simp [hplaced]
    simpa [stageMass] using
      stageMass_foldl_entries_eq bitLength oddSteps placed stage.toList
        (Std.HashMap.emptyWithCapacity (stage.size * 2 + 1))
  · simp [hplaced, stageMass]

theorem stageWeightedSum_transitionSize_eq_stageMass_stepStage
    (bitLength oddSteps placed : Nat) (stage : GapResidueStage) :
    stageWeightedSum (fun key => (stateTransitions bitLength oddSteps placed key).size) stage =
      stageMass (stepStage bitLength oddSteps placed stage) := by
  rw [stageMass_stepStage_eq_transitionSizeSum]
  by_cases hplaced : placed < oddSteps
  · simp [stageWeightedSum, hplaced]
  · have hzero :
        stageWeightedSum (fun key => (stateTransitions bitLength oddSteps placed key).size) stage = 0 := by
      have hconst :
          ∀ (l : List (GapResidueKey × Nat)) (init : Nat),
            l.foldl (fun acc _ => acc) init = init := by
        intro l init
        induction l generalizing init with
        | nil => simp
        | cons x xs ih => simp [ih]
      unfold stageWeightedSum
      induction stage.toList with
      | nil => simp [hplaced, stateTransitions]
      | cons x xs ih =>
          simp [hplaced, stateTransitions, hconst]
    simp [hplaced, hzero]

theorem stepStage_eq_toListFoldl
    (bitLength oddSteps placed : Nat) (stage : GapResidueStage) :
    stepStage bitLength oddSteps placed stage =
      if placed < oddSteps then
        stage.toList.foldl
          (fun next entry =>
            let key := entry.1
            let count := entry.2
            Id.run do
              let mut next := next
              for tr in stateTransitions bitLength oddSteps placed key do
                next := stageInsertAdd next tr.nextKey count
              pure next)
          (Std.HashMap.emptyWithCapacity (stage.size * 2 + 1))
      else {} := by
  by_cases h : placed < oddSteps <;> simp [stepStage, h]

theorem stateTransitions_eq_toArray_stateTransitionsList
    (bitLength oddSteps placed : Nat) (key : GapResidueKey) :
    stateTransitions bitLength oddSteps placed key =
      if placed < oddSteps then
        (stateTransitionsList bitLength oddSteps placed key).toArray
      else #[] := by
  by_cases h : placed < oddSteps <;> simp [stateTransitions, h]

private theorem sum_weighted_ge_mul_sum_snd
    (weight : GapResidueKey → Nat) (entries : List (GapResidueKey × Nat)) (m : Nat)
    (hbound : ∀ entry, entry ∈ entries → m ≤ weight entry.1) :
    m * (entries.map Prod.snd).sum ≤ (entries.map (fun entry => entry.2 * weight entry.1)).sum := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      have hhead : m ≤ weight entry.1 := hbound entry (by simp)
      have htail : ∀ e, e ∈ entries → m ≤ weight e.1 := by
        intro e he
        exact hbound e (by simp [he])
      have hmulhead : entry.2 * m ≤ entry.2 * weight entry.1 :=
        Nat.mul_le_mul_left _ hhead
      have hmulrest :
          m * (entries.map Prod.snd).sum ≤ (entries.map (fun entry => entry.2 * weight entry.1)).sum :=
        ih htail
      have hadd := Nat.add_le_add hmulhead hmulrest
      simpa [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hadd

theorem mul_stageMass_le_stageWeightedSum_of_lower_bound
    (weight : GapResidueKey → Nat) (stage : GapResidueStage) (m : Nat)
    (hbound : ∀ entry, entry ∈ stage.toList → m ≤ weight entry.1) :
    m * stageMass stage ≤ stageWeightedSum weight stage := by
  rw [stageMass_eq_sum_map_snd, stageWeightedSum_eq_sum_map]
  exact sum_weighted_ge_mul_sum_snd weight stage.toList m hbound

theorem mul_stageMass_le_stageMass_stepStage_of_transitionSize_lower
    (bitLength oddSteps placed : Nat) (stage : GapResidueStage) (m : Nat)
    (hbound : ∀ entry, entry ∈ stage.toList →
      m ≤ (stateTransitions bitLength oddSteps placed entry.1).size) :
    m * stageMass stage ≤ stageMass (stepStage bitLength oddSteps placed stage) := by
  rw [← stageWeightedSum_transitionSize_eq_stageMass_stepStage]
  exact mul_stageMass_le_stageWeightedSum_of_lower_bound
    (fun key => (stateTransitions bitLength oddSteps placed key).size) stage m hbound

def stageCountsPositive (stage : GapResidueStage) : Prop :=
  ∀ key, key ∈ stage → 0 < stage.getD key 0

theorem stageCountsPositive_emptyWithCapacity (c : Nat) :
    stageCountsPositive (Std.HashMap.emptyWithCapacity c : GapResidueStage) := by
  intro key h
  simp at h

theorem stageCountsPositive_empty : stageCountsPositive ({} : GapResidueStage) := by
  intro key h
  simp at h

theorem stageCountsPositive_toList
    {stage : GapResidueStage} (hstage : stageCountsPositive stage) :
    ∀ entry, entry ∈ stage.toList → 0 < entry.2 := by
  intro entry hmem
  have hsome : stage[entry.1]? = some entry.2 :=
    (Std.HashMap.mem_toList_iff_getElem?_eq_some).1 hmem
  have hkey : entry.1 ∈ stage := by
    apply (Std.HashMap.isSome_getElem?_iff_mem (m := stage) (a := entry.1)).mp
    simp [hsome]
  have hgd : stage.getD entry.1 0 = entry.2 := by
    apply Option.some.inj
    exact (Std.HashMap.getElem?_eq_some_getD (a := entry.1) (fallback := 0) hkey).symm.trans hsome
  simpa [hgd] using hstage entry.1 hkey

theorem stageCountsPositive_stageInsertAdd
    {stage : GapResidueStage} {key : GapResidueKey} {count : Nat}
    (hstage : stageCountsPositive stage) (hcount : 0 < count) :
    stageCountsPositive (stageInsertAdd stage key count) := by
  intro a ha
  unfold stageInsertAdd at ha ⊢
  rw [Std.HashMap.mem_insert] at ha
  rw [Std.HashMap.getD_insert]
  by_cases hka : key == a
  · have hkEq : key = a := by simpa using hka
    subst hkEq
    have hsum : 0 < stage.getD key 0 + count :=
      Nat.lt_of_lt_of_le hcount (Nat.le_add_left count (stage.getD key 0))
    simpa [hka] using hsum
  · rcases ha with hEq | hmem
    · simp [hka] at hEq
    · simpa [hka] using hstage a hmem

private theorem stageCountsPositive_foldl_transitionList_of_positive
    (trs : List GapTransition) (count : Nat) (init : GapResidueStage)
    (hcount : 0 < count)
    (hinit : stageCountsPositive init) :
    stageCountsPositive (trs.foldl (fun st tr => stageInsertAdd st tr.nextKey count) init) := by
  induction trs generalizing init with
  | nil => simpa using hinit
  | cons tr trs ih =>
      simpa [List.foldl_cons] using
        (ih (init := stageInsertAdd init tr.nextKey count)
          (stageCountsPositive_stageInsertAdd hinit hcount))

private theorem stageCountsPositive_foldl_transitionArray_of_positive
    (trs : Array GapTransition) (count : Nat) (init : GapResidueStage)
    (hcount : 0 < count)
    (hinit : stageCountsPositive init) :
    stageCountsPositive (trs.foldl (fun st tr => stageInsertAdd st tr.nextKey count) init) := by
  rw [← Array.foldl_toList]
  exact stageCountsPositive_foldl_transitionList_of_positive trs.toList count init hcount hinit

private theorem stageCountsPositive_foldl_entries_of_positive
    (bitLength oddSteps placed : Nat)
    (entries : List (GapResidueKey × Nat)) (init : GapResidueStage)
    (hentries : ∀ entry, entry ∈ entries → 0 < entry.2)
    (hinit : stageCountsPositive init) :
    stageCountsPositive
      (entries.foldl
        (fun next entry =>
          (stateTransitions bitLength oddSteps placed entry.1).foldl
            (fun st tr => stageInsertAdd st tr.nextKey entry.2) next)
        init) := by
  induction entries generalizing init with
  | nil => simpa using hinit
  | cons entry entries ih =>
      have hhead : 0 < entry.2 := hentries entry (by simp)
      have htail : ∀ e, e ∈ entries → 0 < e.2 := by
        intro e he
        exact hentries e (by simp [he])
      apply ih
        (init := (stateTransitions bitLength oddSteps placed entry.1).foldl
          (fun st tr => stageInsertAdd st tr.nextKey entry.2) init)
        htail
      exact stageCountsPositive_foldl_transitionArray_of_positive
        (stateTransitions bitLength oddSteps placed entry.1) entry.2 init hhead hinit

theorem stepStage_countsPositive_of_positive
    (bitLength oddSteps placed : Nat) (stage : GapResidueStage)
    (hstage : stageCountsPositive stage) :
    stageCountsPositive (stepStage bitLength oddSteps placed stage) := by
  unfold stepStage
  by_cases hplaced : placed < oddSteps
  · simp [hplaced]
    apply stageCountsPositive_foldl_entries_of_positive
    · exact stageCountsPositive_toList hstage
    · exact stageCountsPositive_emptyWithCapacity (stage.size * 2 + 1)
  · simp [hplaced, stageCountsPositive]

/-- Recursion-friendly residue-stage companion to `stages`: stage `0` is the
singleton seed at residue depth `oddSteps`, and stage `κ + 1` applies one
residue-side kernel step at odd placement `κ`. This gives a theorem-friendly
public timeline parallel to `exactStageAt`. -/
def stageAt (bitLength oddSteps : Nat) : Nat → GapResidueStage :=
  stageChain bitLength oddSteps

@[simp] theorem stageAt_zero (bitLength oddSteps : Nat) :
    stageAt bitLength oddSteps 0 =
      stageInsertAdd {} { usedZeros := 0, residue := 1 % (3 ^ oddSteps) } 1 := by
  rfl

@[simp] theorem stageAt_succ (bitLength oddSteps placed : Nat) :
    stageAt bitLength oddSteps (placed + 1) =
      stepStage bitLength oddSteps placed (stageAt bitLength oddSteps placed) := by
  rfl

theorem sigma_eq_stageMass_stageAt
    (bitLength oddSteps placed : Nat) (hplaced : placed ≤ oddSteps) :
    sigma bitLength oddSteps placed = stageMass (stageAt bitLength oddSteps placed) := by
  have hget :
      (sigmas bitLength oddSteps)[placed]? = some (stageMass (stageAt bitLength oddSteps placed)) := by
    simp [sigmas, stageAt, hplaced, Nat.lt_succ_iff]
  unfold sigma
  rw [hget]

theorem totalCount_eq_stageMass_stageAt
    (bitLength oddSteps : Nat) :
    totalCount bitLength oddSteps = stageMass (stageAt bitLength oddSteps oddSteps) := by
  exact sigma_eq_stageMass_stageAt bitLength oddSteps oddSteps (Nat.le_refl _)

theorem stageCountsPositive_stageAt
    (bitLength oddSteps : Nat) :
    ∀ placed, stageCountsPositive (stageAt bitLength oddSteps placed)
  | 0 => by
      apply stageCountsPositive_stageInsertAdd
      · exact stageCountsPositive_empty
      · simp
  | n + 1 => by
      exact stepStage_countsPositive_of_positive bitLength oddSteps n
        (stageAt bitLength oddSteps n)
        (stageCountsPositive_stageAt bitLength oddSteps n)

theorem stageWeightedSum_eq_of_equiv
    (weight : GapResidueKey → Nat) {stage₁ stage₂ : GapResidueStage}
    (h : Std.HashMap.Equiv stage₁ stage₂) :
    stageWeightedSum weight stage₁ = stageWeightedSum weight stage₂ := by
  rw [stageWeightedSum_eq_sum_map, stageWeightedSum_eq_sum_map]
  exact sum_weighted_eq_of_perm weight (Std.HashMap.Equiv.toList_perm h)

theorem stageMass_eq_of_equiv {stage₁ stage₂ : GapResidueStage}
    (h : Std.HashMap.Equiv stage₁ stage₂) :
    stageMass stage₁ = stageMass stage₂ := by
  rw [stageMass_eq_sum_map_snd, stageMass_eq_sum_map_snd]
  exact sum_map_snd_eq_of_perm (Std.HashMap.Equiv.toList_perm h)

theorem stageEquiv_of_forall_getD_eq_of_positive
    {stage₁ stage₂ : GapResidueStage}
    (hpos₁ : stageCountsPositive stage₁)
    (hpos₂ : stageCountsPositive stage₂)
    (hgetD : ∀ key, stage₁.getD key 0 = stage₂.getD key 0) :
    Std.HashMap.Equiv stage₁ stage₂ := by
  apply Std.HashMap.Equiv.of_forall_getElem?_eq
  intro key
  by_cases hmem₁ : key ∈ stage₁
  · have hpos : 0 < stage₁.getD key 0 := hpos₁ key hmem₁
    have hmem₂ : key ∈ stage₂ := by
      by_cases hmem₂ : key ∈ stage₂
      · exact hmem₂
      · have hpos₂' : 0 < stage₂.getD key 0 := by simpa [hgetD key] using hpos
        rw [Std.HashMap.getD_eq_fallback hmem₂] at hpos₂'
        simp at hpos₂'
    rw [Std.HashMap.getElem?_eq_some_getD (a := key) (fallback := 0) hmem₁]
    rw [Std.HashMap.getElem?_eq_some_getD (a := key) (fallback := 0) hmem₂]
    simp [hgetD key]
  · have hnot₂ : ¬ key ∈ stage₂ := by
      intro hmem₂
      have hpos₂' : 0 < stage₂.getD key 0 := hpos₂ key hmem₂
      have hzero₂ : stage₂.getD key 0 = 0 := by
        calc
          stage₂.getD key 0 = stage₁.getD key 0 := by symm; exact hgetD key
          _ = 0 := Std.HashMap.getD_eq_fallback hmem₁
      rw [hzero₂] at hpos₂'
      simp at hpos₂'
    rw [Std.HashMap.getElem?_eq_none hmem₁, Std.HashMap.getElem?_eq_none hnot₂]

end CollatzThreeAdic
