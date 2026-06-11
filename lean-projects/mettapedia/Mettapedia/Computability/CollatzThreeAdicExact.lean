import Std.Data.HashMap.Lemmas
import Mathlib.Data.Nat.ModEq
import Mettapedia.Computability.CollatzThreeAdicTransfer

/-!
# Exact-value reverse-Collatz gap recurrence

This file makes the "full-value" reverse-Collatz recurrence explicit before any
3-adic quotienting.  It tracks the exact current value together with the number
of zeros already spent, then provides the quotient map into the residue-state DP
from `CollatzThreeAdic`.

The exact quotient theorem is still future work; for now this file gives the
public exact recurrence object and the quotient surface that the later proof
should compare.
-/

namespace CollatzThreeAdic

structure GapValueKey where
  usedZeros : Nat
  value : Nat
deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Hashable, Inhabited

abbrev GapValueStage := Std.HashMap GapValueKey Nat

structure GapValueTransition where
  gap : Nat
  nextKey : GapValueKey
deriving Repr, BEq, DecidableEq, Inhabited

private theorem foldl_add_entrySnd_eq_sum_map_snd (l : List (GapValueKey × Nat)) (init : Nat) :
    l.foldl (fun acc entry => acc + entry.snd) init = init + (l.map Prod.snd).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (init := init + x.snd)

private theorem exactSum_map_snd_eq_of_perm {l₁ l₂ : List (GapValueKey × Nat)}
    (h : l₁.Perm l₂) :
    (l₁.map Prod.snd).sum = (l₂.map Prod.snd).sum := by
  simpa using List.Perm.sum_nat (h.map Prod.snd)

private theorem exactInsert_same_getD_equiv (stage : GapValueStage) (key : GapValueKey)
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

private theorem exactFilter_eq_self_of_not_mem_key_eq (stage : GapValueStage) (key : GapValueKey)
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

def exactStageMass (stage : GapValueStage) : Nat :=
  stage.toList.foldl (fun acc entry => acc + entry.2) 0

def exactStageInsertAdd
    (stage : GapValueStage) (key : GapValueKey) (count : Nat) : GapValueStage :=
  stage.insert key (stage.getD key 0 + count)

def exactGapUpper (bitLength oddSteps : Nat) (key : GapValueKey) : Nat :=
  bitLength - oddSteps - key.usedZeros

def exactGapNextKey? (bitLength oddSteps placed : Nat) (key : GapValueKey) (gap : Nat) :
    Option GapValueKey :=
  if placed < oddSteps then
    let remaining := oddSteps - placed
    if gap ≤ exactGapUpper bitLength oddSteps key then
      let scaled := 2 ^ (gap + 1) * key.value
      let numerator := scaled - 1
      if numerator % 3 == 0 then
        if !(placed == 0 && gap == 1) then
          let nextValue := numerator / 3
          if remaining == 1 || nextValue % 3 != 0 then
            some { usedZeros := key.usedZeros + gap, value := nextValue }
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

theorem exactGapNextKey?_value_pos
    (bitLength oddSteps placed : Nat) (key nextKey : GapValueKey) (gap : Nat)
    (hvalue : 0 < key.value)
    (hnext : exactGapNextKey? bitLength oddSteps placed key gap = some nextKey) :
    0 < nextKey.value := by
  unfold exactGapNextKey? at hnext
  split at hnext <;> simp at hnext
  rcases hnext with ⟨_hgap, hdiv, _hskip, _hkeep, hEq⟩
  cases hEq
  simp
  let num := 2 ^ (gap + 1) * key.value - 1
  have hpowGeGap : 1 ≤ 2 ^ gap := Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
  have hvalGeOne : 1 ≤ key.value := Nat.succ_le_of_lt hvalue
  have hpowGeTwo : 2 ≤ 2 ^ (gap + 1) := by
    calc
      2 = 1 * 2 := by simp
      _ ≤ 2 ^ gap * 2 := by gcongr
      _ = 2 ^ (gap + 1) := by rw [Nat.pow_succ]
  have hscaledGeTwo : 2 ≤ 2 ^ (gap + 1) * key.value := by
    calc
      2 = 2 * 1 := by simp
      _ ≤ 2 * key.value := by gcongr
      _ ≤ 2 ^ (gap + 1) * key.value := by gcongr
  have hnumPos : 0 < num := by
    dsimp [num]
    omega
  have hdvd : 3 ∣ num := Nat.dvd_of_mod_eq_zero hdiv
  rcases hdvd with ⟨m, hm⟩
  have hmPos : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hm0
    subst hm0
    simp at hm
    exact Nat.ne_of_gt hnumPos hm
  have hnumGeThree : 3 ≤ num := by
    rw [hm]
    exact Nat.mul_le_mul_left 3 (Nat.succ_le_of_lt hmPos)
  have hqPos : 0 < num / 3 := by
    exact Nat.div_pos hnumGeThree (by decide)
  simpa [num] using hqPos

def exactStateTransitionsList (bitLength oddSteps placed : Nat) (key : GapValueKey) :
    List GapValueTransition :=
  (List.range (exactGapUpper bitLength oddSteps key + 1)).filterMap fun gap =>
    (exactGapNextKey? bitLength oddSteps placed key gap).map fun nextKey =>
      { gap := gap, nextKey := nextKey }

/-- Exact successor transitions from one full-value gap state. -/
def exactStateTransitions (bitLength oddSteps placed : Nat) (key : GapValueKey) :
    Array GapValueTransition :=
  if placed < oddSteps then
    (exactStateTransitionsList bitLength oddSteps placed key).toArray
  else
    #[]

/-- One exact full-value transition step. -/
def exactStepStage (bitLength oddSteps placed : Nat) (stage : GapValueStage) : GapValueStage :=
  if placed < oddSteps then
    stage.toList.foldl
      (fun next entry =>
        let key := entry.1
        let count := entry.2
        Id.run do
          let mut next := next
          for tr in exactStateTransitions bitLength oddSteps placed key do
            next := exactStageInsertAdd next tr.nextKey count
          pure next)
      (Std.HashMap.emptyWithCapacity (stage.size * 2 + 1))
  else
    {}

/-- Recursion-friendly exact stage chain: stage `0` is the singleton full-value
seed, and stage `κ + 1` applies one exact full-value step at odd placement
`κ`. This is the theorem-friendly exact timeline that `exactSigmas` and
`exactTotalCount` are intended to expose. -/
private def exactStageChain (bitLength oddSteps : Nat) : Nat → GapValueStage
  | 0 => exactStageInsertAdd {} { usedZeros := 0, value := 1 } 1
  | n + 1 => exactStepStage bitLength oddSteps n (exactStageChain bitLength oddSteps n)

/-- All exact full-value stages, from `κ = 0` through `κ = oddSteps`. -/
def exactStages (bitLength oddSteps : Nat) : Array GapValueStage :=
  Id.run do
    let mut out := Array.replicate (oddSteps + 1) ({} : GapValueStage)
    let initStage : GapValueStage :=
      exactStageInsertAdd {} { usedZeros := 0, value := 1 } 1
    out := out.set! 0 initStage
    let mut current := initStage
    for placed in [0:oddSteps] do
      let next := exactStepStage bitLength oddSteps placed current
      out := out.set! (placed + 1) next
      current := next
    pure out

def exactSigmas (bitLength oddSteps : Nat) : Array Nat :=
  ((List.range (oddSteps + 1)).map fun placed =>
    exactStageMass (exactStageChain bitLength oddSteps placed)).toArray

def exactTotalCount (bitLength oddSteps : Nat) : Nat :=
  match (exactSigmas bitLength oddSteps)[oddSteps]? with
  | some total => total
  | none => 0

/-- Quotient an exact state to the residue information used by the public sparse
3-adic DP, with `remaining` odd steps still to place. -/
def residueKeyOf (remaining : Nat) (key : GapValueKey) : GapResidueKey :=
  { usedZeros := key.usedZeros
    residue := key.value % (3 ^ remaining) }

/-- Fold an exact full-value stage down to the residue-state surface at a fixed
remaining-depth. -/
def quotientStage (remaining : Nat) (stage : GapValueStage) : GapResidueStage :=
  stage.toList.foldl
    (fun next entry =>
      let key := entry.1
      let count := entry.2
      stageInsertAdd next (residueKeyOf remaining key) count)
    {}

/-- Executable comparison surface for residue stages: same key set and same
counts at each key, checked by looking up the first stage inside the second and
comparing sizes. This is used for finite bridge audits before the exact
quotient theorem is proved. -/
def residueStageEquivalent (left right : GapResidueStage) : Bool :=
  left.size == right.size &&
    left.fold (init := true) fun ok key count =>
      ok && right.getD key 0 == count

/-- Quotient the exact full-value stages pointwise to the residue-state surface. -/
def quotientedStages (bitLength oddSteps : Nat) : Array GapResidueStage :=
  let exact := exactStages bitLength oddSteps
  ((List.range (oddSteps + 1)).map fun placed =>
    match exact[placed]? with
    | some stage => quotientStage (oddSteps - placed) stage
    | none => {}).toArray

def quotientedSigmas (bitLength oddSteps : Nat) : Array Nat :=
  (quotientedStages bitLength oddSteps).map stageMass

/-- Stage indices where the quotiented exact full-value DP disagrees with the
public residue DP. An empty list on tested rows is evidence for the intended
bridge; the theorem that this is always empty remains future work. -/
def quotientAgreementFailures (bitLength oddSteps : Nat) : List Nat :=
  (List.range (oddSteps + 1)).filter fun placed =>
    let quotiented? := (quotientedStages bitLength oddSteps)[placed]?
    let residue? := (stages bitLength oddSteps)[placed]?
    match quotiented?, residue? with
    | some quotiented, some residue => !(residueStageEquivalent quotiented residue)
    | none, none => false
    | _, _ => true

def quotientAgreementSmokeChecks : Bool :=
  quotientAgreementFailures 15 6 == [] &&
    quotientAgreementFailures 31 14 == [] &&
    quotientAgreementFailures 47 19 == [] &&
    quotientAgreementFailures 50 25 == []

#guard quotientAgreementSmokeChecks

theorem residueKeyOf_usedZeros (remaining : Nat) (key : GapValueKey) :
    (residueKeyOf remaining key).usedZeros = key.usedZeros := by
  rfl

theorem exactStateTransitions_empty_of_not_lt
    {bitLength oddSteps placed : Nat} (h : ¬ placed < oddSteps) (key : GapValueKey) :
    exactStateTransitions bitLength oddSteps placed key = #[] := by
  simp [exactStateTransitions, h]

theorem exactStepStage_empty_of_not_lt
    {bitLength oddSteps placed : Nat} (h : ¬ placed < oddSteps) (stage : GapValueStage) :
    exactStepStage bitLength oddSteps placed stage = {} := by
  simp [exactStepStage, h]

theorem exactStageMass_eq_toListFoldl (stage : GapValueStage) :
    exactStageMass stage = stage.toList.foldl (fun acc entry => acc + entry.2) 0 := by
  rfl

theorem exactStageMass_eq_sum_map_snd (stage : GapValueStage) :
    exactStageMass stage = (stage.toList.map Prod.snd).sum := by
  simpa [exactStageMass] using foldl_add_entrySnd_eq_sum_map_snd stage.toList 0

theorem exactStageMass_exactStageInsertAdd
    (stage : GapValueStage) (key : GapValueKey) (count : Nat) :
    exactStageMass (exactStageInsertAdd stage key count) = exactStageMass stage + count := by
  let old := stage.getD key 0
  by_cases hmem : key ∈ stage
  · have hpermOld : stage.toList.Perm
        ((key, old) :: stage.toList.filter (fun x => decide ¬ (key == x.1) = true)) := by
      exact
        (Std.HashMap.Equiv.toList_perm (exactInsert_same_getD_equiv stage key hmem)).symm.trans
          (Std.HashMap.toList_insert_perm (m := stage) (k := key) (v := old))
    have hpermNew : (exactStageInsertAdd stage key count).toList.Perm
        ((key, old + count) :: stage.toList.filter (fun x => decide ¬ (key == x.1) = true)) := by
      unfold exactStageInsertAdd
      simpa [old] using
        (Std.HashMap.toList_insert_perm (m := stage) (k := key) (v := stage.getD key 0 + count))
    rw [exactStageMass_eq_sum_map_snd, exactStageMass_eq_sum_map_snd]
    rw [(exactSum_map_snd_eq_of_perm hpermNew), (exactSum_map_snd_eq_of_perm hpermOld)]
    simp [old, Nat.add_assoc, Nat.add_comm]
  · have hpermNew : (exactStageInsertAdd stage key count).toList.Perm
        ((key, count) :: stage.toList) := by
      unfold exactStageInsertAdd
      simpa [Std.HashMap.getD_eq_fallback hmem, exactFilter_eq_self_of_not_mem_key_eq stage key hmem] using
        (Std.HashMap.toList_insert_perm (m := stage) (k := key) (v := stage.getD key 0 + count))
    rw [exactStageMass_eq_sum_map_snd]
    rw [(exactSum_map_snd_eq_of_perm hpermNew)]
    simp [exactStageMass_eq_sum_map_snd, Nat.add_comm]

private theorem exactStageMass_foldl_transitionList_add_eq
    (trs : List GapValueTransition) (init : GapValueStage) (count : Nat) :
    exactStageMass (trs.foldl (fun st tr => exactStageInsertAdd st tr.nextKey count) init) =
      exactStageMass init + count * trs.length := by
  induction trs generalizing init with
  | nil => simp
  | cons tr trs ih =>
      simp [List.foldl_cons, exactStageMass_exactStageInsertAdd, ih, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm, Nat.left_distrib]

private theorem exactStageMass_foldl_transitionArray_add_eq
    (trs : Array GapValueTransition) (init : GapValueStage) (count : Nat) :
    exactStageMass (trs.foldl (fun st tr => exactStageInsertAdd st tr.nextKey count) init) =
      exactStageMass init + count * trs.size := by
  rw [← Array.foldl_toList
    (xs := trs) (f := fun st tr => exactStageInsertAdd st tr.nextKey count) (init := init)]
  simpa using
    exactStageMass_foldl_transitionList_add_eq (trs := trs.toList) (init := init) (count := count)

private theorem foldl_add_exactTransitionSize_eq
    (bitLength oddSteps placed : Nat)
    (entries : List (GapValueKey × Nat)) (init : Nat) :
    entries.foldl
        (fun acc entry => acc + entry.2 * (exactStateTransitions bitLength oddSteps placed entry.1).size)
        init =
      init +
        entries.foldl
          (fun acc entry => acc + entry.2 * (exactStateTransitions bitLength oddSteps placed entry.1).size)
          0 := by
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      rw [List.foldl_cons, List.foldl_cons]
      rw [ih (init + entry.2 * (exactStateTransitions bitLength oddSteps placed entry.1).size)]
      simp
      rw [ih (entry.2 * (exactStateTransitions bitLength oddSteps placed entry.1).size)]
      simp [Nat.add_assoc]

private theorem exactStageMass_foldl_entries_eq
    (bitLength oddSteps placed : Nat)
    (entries : List (GapValueKey × Nat)) (init : GapValueStage) :
    exactStageMass
      (entries.foldl
        (fun next entry =>
          (exactStateTransitions bitLength oddSteps placed entry.1).foldl
            (fun st tr => exactStageInsertAdd st tr.nextKey entry.2) next)
        init) =
      exactStageMass init +
        entries.foldl
          (fun acc entry => acc + entry.2 * (exactStateTransitions bitLength oddSteps placed entry.1).size)
          0 := by
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      simp [List.foldl_cons]
      rw [ih]
      rw [exactStageMass_foldl_transitionArray_add_eq]
      have hfold := foldl_add_exactTransitionSize_eq bitLength oddSteps placed entries
        (entry.2 * (exactStateTransitions bitLength oddSteps placed entry.1).size)
      rw [hfold]
      omega

theorem exactStageMass_exactStepStage_eq_transitionSizeSum
    (bitLength oddSteps placed : Nat) (stage : GapValueStage) :
    exactStageMass (exactStepStage bitLength oddSteps placed stage) =
      if placed < oddSteps then
        stage.toList.foldl
          (fun acc entry => acc + entry.2 * (exactStateTransitions bitLength oddSteps placed entry.1).size)
          0
      else 0 := by
  unfold exactStepStage
  by_cases hplaced : placed < oddSteps
  · simp [hplaced]
    simpa [exactStageMass] using
      exactStageMass_foldl_entries_eq bitLength oddSteps placed stage.toList
        (Std.HashMap.emptyWithCapacity (stage.size * 2 + 1))
  · simp [hplaced, exactStageMass]

theorem exactStepStage_eq_toListFoldl
    (bitLength oddSteps placed : Nat) (stage : GapValueStage) :
    exactStepStage bitLength oddSteps placed stage =
      if placed < oddSteps then
        stage.toList.foldl
          (fun next entry =>
            let key := entry.1
            let count := entry.2
            Id.run do
              let mut next := next
              for tr in exactStateTransitions bitLength oddSteps placed key do
                next := exactStageInsertAdd next tr.nextKey count
              pure next)
          (Std.HashMap.emptyWithCapacity (stage.size * 2 + 1))
      else {} := by
  by_cases h : placed < oddSteps <;> simp [exactStepStage, h]

theorem exactStateTransitions_eq_toArray_exactStateTransitionsList
    (bitLength oddSteps placed : Nat) (key : GapValueKey) :
    exactStateTransitions bitLength oddSteps placed key =
      if placed < oddSteps then
        (exactStateTransitionsList bitLength oddSteps placed key).toArray
      else #[] := by
  by_cases h : placed < oddSteps <;> simp [exactStateTransitions, h]

def exactStagePositive (stage : GapValueStage) : Prop :=
  ∀ key, key ∈ stage → 0 < key.value

theorem exactStagePositive_emptyWithCapacity (c : Nat) :
    exactStagePositive (Std.HashMap.emptyWithCapacity c : GapValueStage) := by
  intro key h
  simp at h

theorem exactStagePositive_empty : exactStagePositive ({} : GapValueStage) := by
  intro key h
  simp at h

theorem exactStagePositive_toList
    {stage : GapValueStage} (hstage : exactStagePositive stage) :
    ∀ entry, entry ∈ stage.toList → 0 < entry.1.value := by
  intro entry hmem
  have hsome : stage[entry.1]? = some entry.2 := (Std.HashMap.mem_toList_iff_getElem?_eq_some).1 hmem
  have hkey : entry.1 ∈ stage := by
    apply (Std.HashMap.isSome_getElem?_iff_mem (m := stage) (a := entry.1)).mp
    simp [hsome]
  exact hstage entry.1 hkey

theorem exactStagePositive_exactStageInsertAdd
    {stage : GapValueStage} {key : GapValueKey} {count : Nat}
    (hstage : exactStagePositive stage) (hkey : 0 < key.value) :
    exactStagePositive (exactStageInsertAdd stage key count) := by
  intro a ha
  unfold exactStageInsertAdd at ha
  rw [Std.HashMap.mem_insert] at ha
  rcases ha with hEq | hmem
  · have hka : key = a := by simpa using hEq
    simpa [hka] using hkey
  · exact hstage a hmem

theorem mem_exactStateTransitionsList_iff
    (bitLength oddSteps placed : Nat) (key : GapValueKey) (tr : GapValueTransition) :
    tr ∈ exactStateTransitionsList bitLength oddSteps placed key ↔
      tr.gap < exactGapUpper bitLength oddSteps key + 1 ∧
        exactGapNextKey? bitLength oddSteps placed key tr.gap = some tr.nextKey := by
  unfold exactStateTransitionsList
  simp
  constructor
  · intro h
    rcases h with ⟨gap, hgap, nextKey, hnext, hEq⟩
    cases hEq
    exact ⟨hgap, hnext⟩
  · intro h
    exact ⟨tr.gap, h.1, tr.nextKey, h.2, rfl⟩

theorem mem_exactStateTransitions_iff
    (bitLength oddSteps placed : Nat) (key : GapValueKey) (tr : GapValueTransition) :
    tr ∈ exactStateTransitions bitLength oddSteps placed key ↔
      placed < oddSteps ∧
      tr.gap < exactGapUpper bitLength oddSteps key + 1 ∧
      exactGapNextKey? bitLength oddSteps placed key tr.gap = some tr.nextKey := by
  rw [exactStateTransitions_eq_toArray_exactStateTransitionsList]
  by_cases hplaced : placed < oddSteps
  · simp [hplaced, mem_exactStateTransitionsList_iff]
  · simp [hplaced]

theorem exactStateTransitions_positive_of_positive
    (bitLength oddSteps placed : Nat) (key : GapValueKey)
    (hkey : 0 < key.value) :
    ∀ tr, tr ∈ exactStateTransitions bitLength oddSteps placed key → 0 < tr.nextKey.value := by
  intro tr hmem
  rcases (mem_exactStateTransitions_iff bitLength oddSteps placed key tr).1 hmem with
    ⟨_hplaced, _hgap, hnext⟩
  exact exactGapNextKey?_value_pos bitLength oddSteps placed key tr.nextKey tr.gap hkey hnext

private theorem exactStagePositive_foldl_transitionList_of_positive
    (trs : List GapValueTransition) (count : Nat) (init : GapValueStage)
    (htrs : ∀ tr, tr ∈ trs → 0 < tr.nextKey.value)
    (hinit : exactStagePositive init) :
    exactStagePositive (trs.foldl (fun st tr => exactStageInsertAdd st tr.nextKey count) init) := by
  induction trs generalizing init with
  | nil => simpa using hinit
  | cons tr trs ih =>
      apply ih
      · intro tr' hmem
        exact htrs tr' (by simp [hmem])
      · exact exactStagePositive_exactStageInsertAdd hinit (htrs tr (by simp))

private theorem exactStagePositive_foldl_transitionArray_of_positive
    (trs : Array GapValueTransition) (count : Nat) (init : GapValueStage)
    (htrs : ∀ tr, tr ∈ trs → 0 < tr.nextKey.value)
    (hinit : exactStagePositive init) :
    exactStagePositive (trs.foldl (fun st tr => exactStageInsertAdd st tr.nextKey count) init) := by
  rw [← Array.foldl_toList]
  apply exactStagePositive_foldl_transitionList_of_positive
  · intro tr hmem
    exact htrs tr (by simpa using hmem)
  · exact hinit

private theorem exactStagePositive_foldl_entries_of_positive
    (bitLength oddSteps placed : Nat)
    (entries : List (GapValueKey × Nat)) (init : GapValueStage)
    (hentries : ∀ entry, entry ∈ entries → 0 < entry.1.value)
    (hinit : exactStagePositive init) :
    exactStagePositive
      (entries.foldl
        (fun next entry =>
          (exactStateTransitions bitLength oddSteps placed entry.1).foldl
            (fun st tr => exactStageInsertAdd st tr.nextKey entry.2) next)
        init) := by
  induction entries generalizing init with
  | nil => simpa using hinit
  | cons entry entries ih =>
      have hhead : 0 < entry.1.value := hentries entry (by simp)
      have htail : ∀ e, e ∈ entries → 0 < e.1.value := by
        intro e he
        exact hentries e (by simp [he])
      apply ih
        (init := (exactStateTransitions bitLength oddSteps placed entry.1).foldl
          (fun st tr => exactStageInsertAdd st tr.nextKey entry.2) init)
        htail
      apply exactStagePositive_foldl_transitionArray_of_positive
      · intro tr hmem
        exact exactStateTransitions_positive_of_positive bitLength oddSteps placed entry.1 hhead tr hmem
      · exact hinit

theorem exactStepStage_positive_of_positive
    (bitLength oddSteps placed : Nat) (stage : GapValueStage)
    (hstage : exactStagePositive stage) :
    exactStagePositive (exactStepStage bitLength oddSteps placed stage) := by
  unfold exactStepStage
  by_cases hplaced : placed < oddSteps
  · simp [hplaced]
    apply exactStagePositive_foldl_entries_of_positive
    · exact exactStagePositive_toList hstage
    · exact exactStagePositive_emptyWithCapacity (stage.size * 2 + 1)
  · simp [hplaced, exactStagePositive]

/-- Recursion-friendly exact stage companion to `exactStages`: stage `0` is the
singleton seed, and stage `κ + 1` is obtained by applying one exact step at odd
placement `κ`. This is theorem-friendly even before we prove its full equality
to the imperative array package `exactStages`. -/
def exactStageAt (bitLength oddSteps : Nat) : Nat → GapValueStage :=
  exactStageChain bitLength oddSteps

@[simp] theorem exactStageAt_zero (bitLength oddSteps : Nat) :
    exactStageAt bitLength oddSteps 0 =
      exactStageInsertAdd {} { usedZeros := 0, value := 1 } 1 := by
  rfl

@[simp] theorem exactStageAt_succ (bitLength oddSteps placed : Nat) :
    exactStageAt bitLength oddSteps (placed + 1) =
      exactStepStage bitLength oddSteps placed (exactStageAt bitLength oddSteps placed) := by
  rfl

theorem exactTotalCount_eq_exactStageMass_exactStageAt
    (bitLength oddSteps : Nat) :
    exactTotalCount bitLength oddSteps =
      exactStageMass (exactStageAt bitLength oddSteps oddSteps) := by
  simp [exactTotalCount, exactSigmas, exactStageAt]

theorem exactStagePositive_exactStageAt
    (bitLength oddSteps : Nat) :
    ∀ placed, exactStagePositive (exactStageAt bitLength oddSteps placed)
  | 0 => by
      apply exactStagePositive_exactStageInsertAdd
      · exact exactStagePositive_empty
      · simp
  | n + 1 => by
      exact exactStepStage_positive_of_positive bitLength oddSteps n
        (exactStageAt bitLength oddSteps n)
        (exactStagePositive_exactStageAt bitLength oddSteps n)

theorem quotientStage_eq_toListFoldl
    (remaining : Nat) (stage : GapValueStage) :
    quotientStage remaining stage =
      stage.toList.foldl
        (fun next entry =>
          let key := entry.1
          let count := entry.2
          stageInsertAdd next (residueKeyOf remaining key) count)
        {} := by
  rfl

def exactStageCountsPositive (stage : GapValueStage) : Prop :=
  ∀ key, key ∈ stage → 0 < stage.getD key 0

theorem exactStageCountsPositive_emptyWithCapacity (c : Nat) :
    exactStageCountsPositive (Std.HashMap.emptyWithCapacity c : GapValueStage) := by
  intro key h
  simp at h

theorem exactStageCountsPositive_empty : exactStageCountsPositive ({} : GapValueStage) := by
  intro key h
  simp at h

theorem exactStageCountsPositive_toList
    {stage : GapValueStage} (hstage : exactStageCountsPositive stage) :
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

theorem exactStageCountsPositive_exactStageInsertAdd
    {stage : GapValueStage} {key : GapValueKey} {count : Nat}
    (hstage : exactStageCountsPositive stage) (hcount : 0 < count) :
    exactStageCountsPositive (exactStageInsertAdd stage key count) := by
  intro a ha
  unfold exactStageInsertAdd at ha ⊢
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

private theorem exactStageCountsPositive_foldl_transitionList_of_positive
    (trs : List GapValueTransition) (count : Nat) (init : GapValueStage)
    (hcount : 0 < count)
    (hinit : exactStageCountsPositive init) :
    exactStageCountsPositive (trs.foldl (fun st tr => exactStageInsertAdd st tr.nextKey count) init) := by
  induction trs generalizing init with
  | nil => simpa using hinit
  | cons tr trs ih =>
      simpa [List.foldl_cons] using
        (ih (init := exactStageInsertAdd init tr.nextKey count)
          (exactStageCountsPositive_exactStageInsertAdd hinit hcount))

private theorem exactStageCountsPositive_foldl_transitionArray_of_positive
    (trs : Array GapValueTransition) (count : Nat) (init : GapValueStage)
    (hcount : 0 < count)
    (hinit : exactStageCountsPositive init) :
    exactStageCountsPositive (trs.foldl (fun st tr => exactStageInsertAdd st tr.nextKey count) init) := by
  rw [← Array.foldl_toList]
  exact exactStageCountsPositive_foldl_transitionList_of_positive trs.toList count init hcount hinit

private theorem exactStageCountsPositive_foldl_entries_of_positive
    (bitLength oddSteps placed : Nat)
    (entries : List (GapValueKey × Nat)) (init : GapValueStage)
    (hentries : ∀ entry, entry ∈ entries → 0 < entry.2)
    (hinit : exactStageCountsPositive init) :
    exactStageCountsPositive
      (entries.foldl
        (fun next entry =>
          (exactStateTransitions bitLength oddSteps placed entry.1).foldl
            (fun st tr => exactStageInsertAdd st tr.nextKey entry.2) next)
        init) := by
  induction entries generalizing init with
  | nil => simpa using hinit
  | cons entry entries ih =>
      have hhead : 0 < entry.2 := hentries entry (by simp)
      have htail : ∀ e, e ∈ entries → 0 < e.2 := by
        intro e he
        exact hentries e (by simp [he])
      apply ih
        (init := (exactStateTransitions bitLength oddSteps placed entry.1).foldl
          (fun st tr => exactStageInsertAdd st tr.nextKey entry.2) init)
        htail
      exact exactStageCountsPositive_foldl_transitionArray_of_positive
        (exactStateTransitions bitLength oddSteps placed entry.1) entry.2 init hhead hinit

theorem exactStepStage_countsPositive_of_positive
    (bitLength oddSteps placed : Nat) (stage : GapValueStage)
    (hstage : exactStageCountsPositive stage) :
    exactStageCountsPositive (exactStepStage bitLength oddSteps placed stage) := by
  unfold exactStepStage
  by_cases hplaced : placed < oddSteps
  · simp [hplaced]
    apply exactStageCountsPositive_foldl_entries_of_positive
    · exact exactStageCountsPositive_toList hstage
    · exact exactStageCountsPositive_emptyWithCapacity (stage.size * 2 + 1)
  · simp [hplaced, exactStageCountsPositive]

theorem exactStageCountsPositive_exactStageAt
    (bitLength oddSteps : Nat) :
    ∀ placed, exactStageCountsPositive (exactStageAt bitLength oddSteps placed)
  | 0 => by
      apply exactStageCountsPositive_exactStageInsertAdd
      · exact exactStageCountsPositive_empty
      · simp
  | n + 1 => by
      exact exactStepStage_countsPositive_of_positive bitLength oddSteps n
        (exactStageAt bitLength oddSteps n)
        (exactStageCountsPositive_exactStageAt bitLength oddSteps n)

private theorem stageCountsPositive_quotientStage_fold
    (remaining : Nat) (entries : List (GapValueKey × Nat)) (init : GapResidueStage)
    (hentries : ∀ entry, entry ∈ entries → 0 < entry.2)
    (hinit : stageCountsPositive init) :
    stageCountsPositive
      (entries.foldl
        (fun next entry => stageInsertAdd next (residueKeyOf remaining entry.1) entry.2)
        init) := by
  induction entries generalizing init with
  | nil => simpa using hinit
  | cons entry entries ih =>
      have hhead : 0 < entry.2 := hentries entry (by simp)
      have htail : ∀ e, e ∈ entries → 0 < e.2 := by
        intro e he
        exact hentries e (by simp [he])
      apply ih
        (init := stageInsertAdd init (residueKeyOf remaining entry.1) entry.2)
        htail
      exact stageCountsPositive_stageInsertAdd hinit hhead

theorem stageCountsPositive_quotientStage_of_exactCountsPositive
    (remaining : Nat) (stage : GapValueStage)
    (hstage : exactStageCountsPositive stage) :
    stageCountsPositive (quotientStage remaining stage) := by
  rw [quotientStage_eq_toListFoldl]
  apply stageCountsPositive_quotientStage_fold
  · exact exactStageCountsPositive_toList hstage
  · exact stageCountsPositive_empty

private theorem stageMass_foldl_stageInsertAdd_eq
    (remaining : Nat) (entries : List (GapValueKey × Nat)) (init : GapResidueStage) :
    stageMass
        (entries.foldl
          (fun next entry => stageInsertAdd next (residueKeyOf remaining entry.1) entry.2)
          init) =
      stageMass init + (entries.map Prod.snd).sum := by
  induction entries generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldl_cons, stageMass_stageInsertAdd, ih, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm]

theorem stageMass_quotientStage_eq_exactStageMass
    (remaining : Nat) (stage : GapValueStage) :
    stageMass (quotientStage remaining stage) = exactStageMass stage := by
  rw [quotientStage_eq_toListFoldl]
  rw [stageMass_foldl_stageInsertAdd_eq]
  simp [stageMass, exactStageMass_eq_sum_map_snd]

private theorem sum_indicator_eq_of_perm
    (remaining : Nat) (dst : GapResidueKey)
    {l₁ l₂ : List (GapValueKey × Nat)} (h : l₁.Perm l₂) :
    (l₁.map (fun entry => if residueKeyOf remaining entry.1 = dst then entry.2 else 0)).sum =
      (l₂.map (fun entry => if residueKeyOf remaining entry.1 = dst then entry.2 else 0)).sum := by
  simpa using
    List.Perm.sum_nat
      (h.map (fun entry => if residueKeyOf remaining entry.1 = dst then entry.2 else 0))

private theorem foldl_add_indicator_eq_sum_map
    (remaining : Nat) (dst : GapResidueKey)
    (l : List (GapValueKey × Nat)) (init : Nat) :
    l.foldl (fun acc entry => acc + if residueKeyOf remaining entry.1 = dst then entry.2 else 0) init =
      init + (l.map (fun entry => if residueKeyOf remaining entry.1 = dst then entry.2 else 0)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (init := init + if residueKeyOf remaining x.1 = dst then x.2 else 0)

private theorem getD_foldl_stageInsertAdd_eq
    (remaining : Nat) (entries : List (GapValueKey × Nat)) (init : GapResidueStage)
    (dst : GapResidueKey) :
    (entries.foldl
        (fun next entry => stageInsertAdd next (residueKeyOf remaining entry.1) entry.2)
        init).getD dst 0 =
      entries.foldl
        (fun acc entry => acc + if residueKeyOf remaining entry.1 = dst then entry.2 else 0)
        (init.getD dst 0) := by
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      simp [List.foldl_cons, ih]
      by_cases h : residueKeyOf remaining entry.1 = dst
      · subst h
        simp [stageInsertAdd, Nat.add_comm]
      · have hget :
            (stageInsertAdd init (residueKeyOf remaining entry.1) entry.2).getD dst 0 =
              init.getD dst 0 := by
          simp [stageInsertAdd, Std.HashMap.getD_insert, h]
        rw [hget]
        simp [h]

theorem quotientStage_getD_eq_indicatorFold
    (remaining : Nat) (stage : GapValueStage) (dst : GapResidueKey) :
    (quotientStage remaining stage).getD dst 0 =
      stage.toList.foldl
        (fun acc entry => acc + if residueKeyOf remaining entry.1 = dst then entry.2 else 0)
        0 := by
  rw [quotientStage_eq_toListFoldl]
  simpa using getD_foldl_stageInsertAdd_eq remaining stage.toList ({} : GapResidueStage) dst

theorem quotientStage_exactStageInsertAdd_getD
    (remaining : Nat) (stage : GapValueStage) (key : GapValueKey) (count : Nat)
    (dst : GapResidueKey) :
    (quotientStage remaining (exactStageInsertAdd stage key count)).getD dst 0 =
      (stageInsertAdd (quotientStage remaining stage) (residueKeyOf remaining key) count).getD dst 0 := by
  let old := stage.getD key 0
  by_cases hmem : key ∈ stage
  · have hpermOld : stage.toList.Perm
        ((key, old) :: stage.toList.filter (fun x => decide ¬ (key == x.1) = true)) := by
      exact
        (Std.HashMap.Equiv.toList_perm (exactInsert_same_getD_equiv stage key hmem)).symm.trans
          (Std.HashMap.toList_insert_perm (m := stage) (k := key) (v := old))
    have hpermNew : (exactStageInsertAdd stage key count).toList.Perm
        ((key, old + count) :: stage.toList.filter (fun x => decide ¬ (key == x.1) = true)) := by
      unfold exactStageInsertAdd
      simpa [old] using
        (Std.HashMap.toList_insert_perm (m := stage) (k := key) (v := stage.getD key 0 + count))
    rw [quotientStage_getD_eq_indicatorFold]
    rw [foldl_add_indicator_eq_sum_map]
    by_cases hdst : residueKeyOf remaining key = dst
    · subst hdst
      simp [stageInsertAdd]
      rw [quotientStage_getD_eq_indicatorFold]
      rw [foldl_add_indicator_eq_sum_map]
      rw [sum_indicator_eq_of_perm remaining (residueKeyOf remaining key) hpermNew,
        sum_indicator_eq_of_perm remaining (residueKeyOf remaining key) hpermOld]
      simp [old, Nat.add_assoc, Nat.add_comm]
    · have hget :
            (stageInsertAdd (quotientStage remaining stage) (residueKeyOf remaining key) count).getD dst 0 =
              (quotientStage remaining stage).getD dst 0 := by
          have hbeq : (residueKeyOf remaining key == dst) = false := by simp [hdst]
          rw [stageInsertAdd, Std.HashMap.getD_insert]
          simp [hbeq]
      rw [hget, quotientStage_getD_eq_indicatorFold, foldl_add_indicator_eq_sum_map]
      rw [sum_indicator_eq_of_perm remaining dst hpermNew, sum_indicator_eq_of_perm remaining dst hpermOld]
      simp [old, hdst]
  · have hpermNew : (exactStageInsertAdd stage key count).toList.Perm
        ((key, count) :: stage.toList) := by
      unfold exactStageInsertAdd
      simpa [Std.HashMap.getD_eq_fallback hmem, exactFilter_eq_self_of_not_mem_key_eq stage key hmem] using
        (Std.HashMap.toList_insert_perm (m := stage) (k := key) (v := stage.getD key 0 + count))
    rw [quotientStage_getD_eq_indicatorFold]
    rw [foldl_add_indicator_eq_sum_map]
    rw [sum_indicator_eq_of_perm remaining dst hpermNew]
    by_cases hdst : residueKeyOf remaining key = dst
    · subst hdst
      simp [stageInsertAdd]
      rw [quotientStage_getD_eq_indicatorFold]
      rw [foldl_add_indicator_eq_sum_map]
      omega
    · have hget :
            (stageInsertAdd (quotientStage remaining stage) (residueKeyOf remaining key) count).getD dst 0 =
              (quotientStage remaining stage).getD dst 0 := by
          have hbeq : (residueKeyOf remaining key == dst) = false := by simp [hdst]
          rw [stageInsertAdd, Std.HashMap.getD_insert]
          simp [hbeq]
      rw [hget, quotientStage_getD_eq_indicatorFold, foldl_add_indicator_eq_sum_map]
      simp [hdst]

private theorem foldl_add_residueWeight_eq
    (weight : GapResidueKey → Nat) (remaining : Nat)
    (entries : List (GapValueKey × Nat)) (init : Nat) :
    entries.foldl
        (fun acc entry => acc + entry.2 * weight (residueKeyOf remaining entry.1))
        init =
      init +
        entries.foldl
          (fun acc entry => acc + entry.2 * weight (residueKeyOf remaining entry.1))
          0 := by
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      rw [List.foldl_cons, List.foldl_cons]
      rw [ih (init + entry.2 * weight (residueKeyOf remaining entry.1))]
      simp
      rw [ih (entry.2 * weight (residueKeyOf remaining entry.1))]
      simp [Nat.add_assoc]

private theorem stageWeightedSum_foldl_stageInsertAdd_eq
    (weight : GapResidueKey → Nat) (remaining : Nat)
    (entries : List (GapValueKey × Nat)) (init : GapResidueStage) :
    stageWeightedSum weight
        (entries.foldl
          (fun next entry => stageInsertAdd next (residueKeyOf remaining entry.1) entry.2)
          init) =
      stageWeightedSum weight init +
        entries.foldl
          (fun acc entry => acc + entry.2 * weight (residueKeyOf remaining entry.1))
          0 := by
  induction entries generalizing init with
  | nil => simp [stageWeightedSum]
  | cons entry entries ih =>
      simp [List.foldl_cons]
      rw [ih]
      rw [stageWeightedSum_stageInsertAdd]
      have hfold := foldl_add_residueWeight_eq weight remaining entries
        (entry.2 * weight (residueKeyOf remaining entry.1))
      rw [hfold]
      omega

theorem stageWeightedSum_quotientStage_eq
    (weight : GapResidueKey → Nat) (remaining : Nat) (stage : GapValueStage) :
    stageWeightedSum weight (quotientStage remaining stage) =
      stage.toList.foldl (fun acc entry => acc + entry.2 * weight (residueKeyOf remaining entry.1)) 0 := by
  rw [quotientStage_eq_toListFoldl]
  rw [stageWeightedSum_foldl_stageInsertAdd_eq]
  simp [stageWeightedSum]

theorem div3_mod_pow_pred_eq_of_mod_pow
    {r num numMod : Nat} (hr : 0 < r) (hmod : numMod = num % (3 ^ r)) (hdiv : num % 3 = 0) :
    num / 3 % (3 ^ (r - 1)) = numMod / 3 % (3 ^ (r - 1)) := by
  have hmpos : 0 < 3 ^ r := by
    exact Nat.pow_pos (show 0 < 3 from by decide)
  have hmeq : Nat.ModEq (3 ^ r) num numMod := by
    rw [hmod]
    exact (Nat.mod_modEq _ _).symm
  have hmoddiv : numMod % 3 = 0 := by
    rw [hmod]
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr) with ⟨s, rfl⟩
    rw [show 3 ^ Nat.succ s = 3 ^ s * 3 by simp [Nat.pow_succ, Nat.mul_comm]]
    rw [Nat.mod_mul_left_mod]
    exact hdiv
  have hmul : Nat.ModEq (3 ^ r) (3 * (num / 3)) (3 * (numMod / 3)) := by
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdiv)]
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmoddiv)]
    exact hmeq
  have hcancel : Nat.ModEq (3 ^ r / Nat.gcd (3 ^ r) 3) (num / 3) (numMod / 3) :=
    Nat.ModEq.cancel_left_div_gcd hmpos hmul
  have hgcd : Nat.gcd (3 ^ r) 3 = 3 := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr) with ⟨s, rfl⟩
    simp [Nat.pow_succ, Nat.mul_comm]
  have hdivpow : 3 ^ r / 3 = 3 ^ (r - 1) := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr) with ⟨s, rfl⟩
    simp [Nat.pow_succ, Nat.mul_comm]
  simpa [Nat.ModEq, hgcd, hdivpow] using hcancel

theorem residueNumeratorMod_eq_exactNumerator_mod
    (gap remaining value : Nat)
    (hvalue : 0 < value) :
    ((((2 ^ (gap + 1)) * (value % (3 ^ remaining))) % (3 ^ remaining) + 3 ^ remaining - 1) %
        (3 ^ remaining)) =
      ((2 ^ (gap + 1) * value - 1) % (3 ^ remaining)) := by
  have hscaledPos : 0 < 2 ^ (gap + 1) * value := by
    exact Nat.mul_pos (show 0 < 2 ^ (gap + 1) from Nat.pow_pos (show 0 < 2 from by decide))
      hvalue
  rw [Nat.mul_mod]
  simp
  have hleft : 2 ^ (gap + 1) * value % 3 ^ remaining + 3 ^ remaining - 1 =
      2 ^ (gap + 1) * value % 3 ^ remaining + (3 ^ remaining - 1) := by
    omega
  rw [hleft]
  calc
    (2 ^ (gap + 1) * value % 3 ^ remaining + (3 ^ remaining - 1)) % 3 ^ remaining
        = (2 ^ (gap + 1) * value + (3 ^ remaining - 1)) % 3 ^ remaining := by
            rw [Nat.add_mod]
            have hlt : 3 ^ remaining - 1 < 3 ^ remaining := by
              have hpowPos : 0 < 3 ^ remaining := by
                exact Nat.pow_pos (show 0 < 3 from by decide)
              omega
            rw [Nat.mod_eq_of_lt hlt]
            simp
    _ = (2 ^ (gap + 1) * value + 3 ^ remaining - 1) % 3 ^ remaining := by
          have hright : 2 ^ (gap + 1) * value + 3 ^ remaining - 1 =
              2 ^ (gap + 1) * value + (3 ^ remaining - 1) := by
            omega
          rw [hright]
    _ = (2 ^ (gap + 1) * value - 1) % 3 ^ remaining := by
          have hge : 3 ^ remaining ≤ 2 ^ (gap + 1) * value + 3 ^ remaining - 1 := by
            have hone : 1 ≤ 2 ^ (gap + 1) * value := Nat.succ_le_of_lt hscaledPos
            omega
          have hsub : 2 ^ (gap + 1) * value + 3 ^ remaining - 1 - 3 ^ remaining =
              2 ^ (gap + 1) * value - 1 := by
            omega
          rw [Nat.mod_eq_sub_mod hge, hsub]

theorem mod_mod_pow_eq_mod_three {r x : Nat} (hr : 0 < r) :
    x % (3 ^ r) % 3 = x % 3 := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr) with ⟨s, hs⟩
  rw [hs, show 3 ^ Nat.succ s = 3 ^ s * 3 by simp [Nat.pow_succ, Nat.mul_comm]]
  exact Nat.mod_mul_left_mod x (3 ^ s) 3

theorem mod_mod_pow_pred_eq_mod_three {r x : Nat} (hr : 1 < r) :
    x % (3 ^ (r - 1)) % 3 = x % 3 := by
  have hr' : 0 < r - 1 := by
    omega
  simpa using (mod_mod_pow_eq_mod_three (r := r - 1) (x := x) hr')

theorem exactGapNextKey?_map_residueKeyOf_eq_residueGapNextKey?
    (bitLength oddSteps placed : Nat)
    (key : GapValueKey) (gap : Nat)
    (hvalue : 0 < key.value) :
    (exactGapNextKey? bitLength oddSteps placed key gap).map
        (residueKeyOf (oddSteps - placed - 1)) =
      residueGapNextKey? bitLength oddSteps placed
        (residueKeyOf (oddSteps - placed) key) gap := by
  by_cases hplaced : placed < oddSteps
  · by_cases hgap1 : gap ≤ bitLength - oddSteps - key.usedZeros
    · have hrem : 0 < oddSteps - placed := by
        omega
      have hnumMod :
          (((2 ^ (gap + 1) * key.value % 3 ^ (oddSteps - placed) + 3 ^ (oddSteps - placed) - 1) %
                3 ^ (oddSteps - placed))) =
            ((2 ^ (gap + 1) * key.value - 1) % (3 ^ (oddSteps - placed))) := by
        simpa using residueNumeratorMod_eq_exactNumerator_mod gap (oddSteps - placed) key.value
          hvalue
      have hmod3 :
          (((2 ^ (gap + 1) * key.value % 3 ^ (oddSteps - placed) + 3 ^ (oddSteps - placed) - 1) %
                3 ^ (oddSteps - placed))) % 3 =
            ((2 ^ (gap + 1) * key.value - 1) % 3) := by
        rw [hnumMod]
        exact mod_mod_pow_eq_mod_three hrem
      by_cases hdiv : (2 ^ (gap + 1) * key.value - 1) % 3 = 0
      · have hdivMod :
            (((2 ^ (gap + 1) * key.value % 3 ^ (oddSteps - placed) + 3 ^ (oddSteps - placed) - 1) %
                  3 ^ (oddSteps - placed))) % 3 = 0 := by
          simpa [hmod3] using hdiv
        by_cases hskip : ¬ placed = 0 ∨ ¬ gap = 1
        · have hnextResidue :
              (((2 ^ (gap + 1) * key.value % 3 ^ (oddSteps - placed) + 3 ^ (oddSteps - placed) - 1) %
                    3 ^ (oddSteps - placed)) /
                  3 %
                3 ^ (oddSteps - placed - 1)) =
                ((2 ^ (gap + 1) * key.value - 1) / 3) % (3 ^ (oddSteps - placed - 1)) := by
            exact (div3_mod_pow_pred_eq_of_mod_pow
              (r := oddSteps - placed)
              (num := 2 ^ (gap + 1) * key.value - 1)
              (numMod := ((2 ^ (gap + 1) * key.value % 3 ^ (oddSteps - placed) +
                3 ^ (oddSteps - placed) - 1) % 3 ^ (oddSteps - placed)))
              hrem hnumMod hdiv).symm
          by_cases hkeep : oddSteps - placed = 1 ∨ ¬ ((2 ^ (gap + 1) * key.value - 1) / 3) % 3 = 0
          · have hkeepRes :
                oddSteps - placed = 1 ∨
                  ¬((((2 ^ (gap + 1) * key.value % 3 ^ (oddSteps - placed) +
                          3 ^ (oddSteps - placed) - 1) % 3 ^ (oddSteps - placed)) /
                        3 %
                      3 ^ (oddSteps - placed - 1)) %
                    3 = 0) := by
              rcases hkeep with hkeep | hkeep
              · exact Or.inl hkeep
              · by_cases hr1 : oddSteps - placed = 1
                · exact Or.inl hr1
                · right
                  rw [hnextResidue, mod_mod_pow_pred_eq_mod_three (by omega)]
                  exact hkeep
            rw [exactGapNextKey?, residueGapNextKey?]
            rw [if_pos hplaced, if_pos hplaced]
            simp [exactGapUpper, residueGapUpper, residueKeyOf, hgap1]
            rw [if_pos hdiv, if_pos hdivMod]
            rw [if_pos hskip, if_pos hskip]
            rw [if_pos hkeep, if_pos hkeepRes]
            simp [residueKeyOf, hnextResidue]
          · have hkeepRes :
                ¬(oddSteps - placed = 1 ∨
                    ¬((((2 ^ (gap + 1) * key.value % 3 ^ (oddSteps - placed) +
                            3 ^ (oddSteps - placed) - 1) % 3 ^ (oddSteps - placed)) /
                          3 %
                        3 ^ (oddSteps - placed - 1)) %
                      3 = 0)) := by
              intro hkeep'
              apply hkeep
              rcases hkeep' with hkeep' | hkeep'
              · exact Or.inl hkeep'
              · by_cases hr1 : oddSteps - placed = 1
                · exact Or.inl hr1
                · right
                  rw [hnextResidue, mod_mod_pow_pred_eq_mod_three (by omega)] at hkeep'
                  exact hkeep'
            rw [exactGapNextKey?, residueGapNextKey?]
            rw [if_pos hplaced, if_pos hplaced]
            simp [exactGapUpper, residueGapUpper, residueKeyOf, hgap1]
            rw [if_pos hdiv, if_pos hdivMod]
            rw [if_pos hskip, if_pos hskip]
            rw [if_neg hkeep, if_neg hkeepRes]
            simp
        · rw [exactGapNextKey?, residueGapNextKey?]
          rw [if_pos hplaced, if_pos hplaced]
          simp [exactGapUpper, residueGapUpper, residueKeyOf, hgap1]
          rw [if_pos hdiv, if_pos hdivMod]
          rw [if_neg hskip, if_neg hskip]
          simp
      · have hdivMod :
            ¬((((2 ^ (gap + 1) * key.value % 3 ^ (oddSteps - placed) + 3 ^ (oddSteps - placed) - 1) %
                    3 ^ (oddSteps - placed))) %
                  3 = 0) := by
          simpa [hmod3] using hdiv
        rw [exactGapNextKey?, residueGapNextKey?]
        rw [if_pos hplaced, if_pos hplaced]
        simp [exactGapUpper, residueGapUpper, residueKeyOf, hgap1]
        rw [if_neg hdiv, if_neg hdivMod]
        simp
    · rw [exactGapNextKey?, residueGapNextKey?]
      rw [if_pos hplaced, if_pos hplaced]
      simp [exactGapUpper, residueGapUpper, residueKeyOf, hgap1]
  · simp [exactGapNextKey?, residueGapNextKey?, hplaced]

theorem exactStateTransitionsList_map_residueKeyOf_eq_stateTransitionsList
    (bitLength oddSteps placed : Nat) (key : GapValueKey) (hvalue : 0 < key.value) :
    (exactStateTransitionsList bitLength oddSteps placed key).map
      (fun tr : GapValueTransition =>
        ({ gap := tr.gap
           nextKey := residueKeyOf (oddSteps - placed - 1) tr.nextKey } : GapTransition)) =
      stateTransitionsList bitLength oddSteps placed (residueKeyOf (oddSteps - placed) key) := by
  unfold exactStateTransitionsList stateTransitionsList
  rw [List.map_filterMap]
  have hu : exactGapUpper bitLength oddSteps key =
      residueGapUpper bitLength oddSteps (residueKeyOf (oddSteps - placed) key) := by
    simp [exactGapUpper, residueGapUpper, residueKeyOf]
  rw [hu]
  have hpointComp : ∀ x,
      Option.map
          ((fun tr => { gap := tr.gap, nextKey := residueKeyOf (oddSteps - placed - 1) tr.nextKey }) ∘
            fun nextKey => ({ gap := x, nextKey := nextKey } : GapValueTransition))
          (exactGapNextKey? bitLength oddSteps placed key x) =
      Option.map (fun nextKey => ({ gap := x, nextKey := nextKey } : GapTransition))
          (residueGapNextKey? bitLength oddSteps placed (residueKeyOf (oddSteps - placed) key) x) := by
    intro x
    simpa [Option.map_map, Function.comp] using
      (congrArg (Option.map (fun nextKey => ({ gap := x, nextKey := nextKey } : GapTransition)))
        (exactGapNextKey?_map_residueKeyOf_eq_residueGapNextKey?
          bitLength oddSteps placed key x hvalue))
  simp [Option.map_map, hpointComp]

theorem exactStateTransitions_map_residueKeyOf_eq_stateTransitions
    (bitLength oddSteps placed : Nat) (key : GapValueKey) (hvalue : 0 < key.value) :
    (exactStateTransitions bitLength oddSteps placed key).map
      (fun tr : GapValueTransition =>
        ({ gap := tr.gap
           nextKey := residueKeyOf (oddSteps - placed - 1) tr.nextKey } : GapTransition)) =
      stateTransitions bitLength oddSteps placed (residueKeyOf (oddSteps - placed) key) := by
  rw [exactStateTransitions_eq_toArray_exactStateTransitionsList]
  rw [stateTransitions_eq_toArray_stateTransitionsList]
  by_cases hplaced : placed < oddSteps
  · simp [hplaced, exactStateTransitionsList_map_residueKeyOf_eq_stateTransitionsList, hvalue]
  · simp [hplaced]

/-- One-step exact transition multiplicity viewed after quotienting the exact
next values down to residue states. -/
def exactTransitionMultiplicity
    (bitLength oddSteps placed : Nat) (key : GapValueKey) (dst : GapResidueKey) : Nat :=
  (exactStateTransitions bitLength oddSteps placed key).foldl
    (fun total tr =>
      total + if residueKeyOf (oddSteps - placed - 1) tr.nextKey = dst then 1 else 0)
    0

theorem exactTransitionMultiplicity_eq_transitionMultiplicity
    (bitLength oddSteps placed : Nat)
    (key : GapValueKey) (dst : GapResidueKey) (hvalue : 0 < key.value) :
    exactTransitionMultiplicity bitLength oddSteps placed key dst =
      transitionMultiplicity bitLength oddSteps placed
        (residueKeyOf (oddSteps - placed) key) dst := by
  unfold exactTransitionMultiplicity transitionMultiplicity
  rw [exactStateTransitions_eq_toArray_exactStateTransitionsList]
  rw [stateTransitions_eq_toArray_stateTransitionsList]
  by_cases hplaced : placed < oddSteps
  · simp [hplaced]
    rw [← exactStateTransitionsList_map_residueKeyOf_eq_stateTransitionsList
      bitLength oddSteps placed key hvalue]
    rw [List.foldl_map]
  · simp [hplaced]

theorem exactStateTransitions_size_eq_stateTransitions_size
    (bitLength oddSteps placed : Nat) (key : GapValueKey) (hvalue : 0 < key.value) :
    (exactStateTransitions bitLength oddSteps placed key).size =
      (stateTransitions bitLength oddSteps placed (residueKeyOf (oddSteps - placed) key)).size := by
  simpa [Array.size_map] using
    congrArg Array.size
      (exactStateTransitions_map_residueKeyOf_eq_stateTransitions bitLength oddSteps placed key hvalue)

private theorem getD_foldl_exactTransitionList_eq
    (remaining : Nat) (trs : List GapValueTransition) (init : GapValueStage)
    (count : Nat) (dst : GapResidueKey) :
    (quotientStage remaining (trs.foldl (fun st tr => exactStageInsertAdd st tr.nextKey count) init)).getD dst 0 =
      (quotientStage remaining init).getD dst 0 +
        count *
          (trs.foldl
            (fun total tr => total + if residueKeyOf remaining tr.nextKey = dst then 1 else 0)
            0) := by
  have hfoldIndicator :
      ∀ (trs : List GapValueTransition) (dst : GapResidueKey) (init : Nat),
        trs.foldl (fun total tr => total + if residueKeyOf remaining tr.nextKey = dst then 1 else 0) init =
          init + trs.foldl
            (fun total tr => total + if residueKeyOf remaining tr.nextKey = dst then 1 else 0)
            0 := by
    intro trs dst init
    induction trs generalizing init with
    | nil => simp
    | cons tr trs ih =>
        rw [List.foldl_cons, List.foldl_cons]
        rw [ih (init + if residueKeyOf remaining tr.nextKey = dst then 1 else 0)]
        simp
        rw [ih (if residueKeyOf remaining tr.nextKey = dst then 1 else 0)]
        simp [Nat.add_assoc]
  induction trs generalizing init with
  | nil => simp [quotientStage]
  | cons tr trs ih =>
      simp [List.foldl_cons, ih]
      by_cases h : residueKeyOf remaining tr.nextKey = dst
      · subst h
        rw [quotientStage_exactStageInsertAdd_getD]
        simp [stageInsertAdd, Nat.add_assoc, Nat.add_comm]
        rw [hfoldIndicator trs (residueKeyOf remaining tr.nextKey) 1]
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · have hget :
            (stageInsertAdd (quotientStage remaining init) (residueKeyOf remaining tr.nextKey) count).getD dst 0 =
              (quotientStage remaining init).getD dst 0 := by
          have hbeq : (residueKeyOf remaining tr.nextKey == dst) = false := by simp [h]
          rw [stageInsertAdd, Std.HashMap.getD_insert]
          simp [hbeq]
        rw [quotientStage_exactStageInsertAdd_getD, hget]
        simp [h]

private theorem getD_foldl_exactTransitionArray_eq
    (remaining : Nat) (trs : Array GapValueTransition) (init : GapValueStage)
    (count : Nat) (dst : GapResidueKey) :
    (quotientStage remaining (trs.foldl (fun st tr => exactStageInsertAdd st tr.nextKey count) init)).getD dst 0 =
      (quotientStage remaining init).getD dst 0 +
        count *
          (trs.foldl
            (fun total tr => total + if residueKeyOf remaining tr.nextKey = dst then 1 else 0)
            0) := by
  rw [← Array.foldl_toList
    (xs := trs) (f := fun st tr => exactStageInsertAdd st tr.nextKey count) (init := init)]
  rw [← Array.foldl_toList
    (xs := trs)
    (f := fun total tr => total + if residueKeyOf remaining tr.nextKey = dst then 1 else 0)
    (init := 0)]
  simpa using getD_foldl_exactTransitionList_eq remaining trs.toList init count dst

theorem quotientStage_exactTransitionFold_getD_eq_exactTransitionMultiplicity
    (bitLength oddSteps placed : Nat) (key : GapValueKey)
    (init : GapValueStage) (count : Nat) (dst : GapResidueKey) :
    (quotientStage (oddSteps - placed - 1)
        ((exactStateTransitions bitLength oddSteps placed key).foldl
          (fun st tr => exactStageInsertAdd st tr.nextKey count) init)).getD dst 0 =
      (quotientStage (oddSteps - placed - 1) init).getD dst 0 +
        count * exactTransitionMultiplicity bitLength oddSteps placed key dst := by
  unfold exactTransitionMultiplicity
  simpa using
    getD_foldl_exactTransitionArray_eq
      (remaining := oddSteps - placed - 1)
      (trs := exactStateTransitions bitLength oddSteps placed key)
      (init := init) (count := count) (dst := dst)

private theorem foldl_add_exactTransitionMultiplicity_eq
    (bitLength oddSteps placed : Nat)
    (entries : List (GapValueKey × Nat)) (dst : GapResidueKey) (init : Nat) :
    entries.foldl
        (fun acc entry => acc + entry.2 * exactTransitionMultiplicity bitLength oddSteps placed entry.1 dst)
        init =
      init +
        entries.foldl
          (fun acc entry => acc + entry.2 * exactTransitionMultiplicity bitLength oddSteps placed entry.1 dst)
          0 := by
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      rw [List.foldl_cons, List.foldl_cons]
      rw [ih (init + entry.2 * exactTransitionMultiplicity bitLength oddSteps placed entry.1 dst)]
      simp
      rw [ih (entry.2 * exactTransitionMultiplicity bitLength oddSteps placed entry.1 dst)]
      simp [Nat.add_assoc]

private theorem quotientStage_getD_exactEntries_eq
    (bitLength oddSteps placed : Nat)
    (entries : List (GapValueKey × Nat)) (init : GapValueStage) (dst : GapResidueKey) :
    (quotientStage (oddSteps - placed - 1)
        (entries.foldl
          (fun next entry =>
            (exactStateTransitions bitLength oddSteps placed entry.1).foldl
              (fun st tr => exactStageInsertAdd st tr.nextKey entry.2) next)
          init)).getD dst 0 =
      (quotientStage (oddSteps - placed - 1) init).getD dst 0 +
        entries.foldl
          (fun acc entry => acc + entry.2 * exactTransitionMultiplicity bitLength oddSteps placed entry.1 dst)
          0 := by
  induction entries generalizing init with
  | nil => simp [quotientStage]
  | cons entry entries ih =>
      simp [List.foldl_cons]
      rw [ih]
      rw [quotientStage_exactTransitionFold_getD_eq_exactTransitionMultiplicity]
      have hfold := foldl_add_exactTransitionMultiplicity_eq bitLength oddSteps placed entries dst
        (entry.2 * exactTransitionMultiplicity bitLength oddSteps placed entry.1 dst)
      rw [hfold]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem quotientStage_exactStepStage_getD_eq_exactTransitionMultiplicityWeighted
    (bitLength oddSteps placed : Nat) (stage : GapValueStage) (dst : GapResidueKey) :
    (quotientStage (oddSteps - placed - 1) (exactStepStage bitLength oddSteps placed stage)).getD dst 0 =
      if placed < oddSteps then
        stage.toList.foldl
          (fun acc entry => acc + entry.2 * exactTransitionMultiplicity bitLength oddSteps placed entry.1 dst)
          0
      else 0 := by
  rw [exactStepStage_eq_toListFoldl]
  by_cases hplaced : placed < oddSteps
  · simp [hplaced]
    rw [quotientStage_getD_exactEntries_eq]
    have hempty :
        (quotientStage (oddSteps - placed - 1)
          (Std.HashMap.emptyWithCapacity (stage.size * 2 + 1) : GapValueStage)).getD dst 0 = 0 := by
      simp [quotientStage]
    rw [hempty]
    simp
  · simp [hplaced, quotientStage]

private theorem foldl_exactTransitionMultiplicity_eq_residueTransitionMultiplicity_of_pos
    (bitLength oddSteps placed : Nat)
    (entries : List (GapValueKey × Nat))
    (hpos : ∀ entry, entry ∈ entries → 0 < entry.1.value)
    (dst : GapResidueKey) (init : Nat) :
    entries.foldl
        (fun acc entry => acc + entry.2 * exactTransitionMultiplicity bitLength oddSteps placed entry.1 dst)
        init =
      entries.foldl
        (fun acc entry =>
          acc + entry.2 * transitionMultiplicity bitLength oddSteps placed
            (residueKeyOf (oddSteps - placed) entry.1) dst)
        init := by
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      have hhead : 0 < entry.1.value := hpos entry (by simp)
      have htail : ∀ e, e ∈ entries → 0 < e.1.value := by
        intro e he
        exact hpos e (by simp [he])
      rw [List.foldl_cons, List.foldl_cons]
      rw [exactTransitionMultiplicity_eq_transitionMultiplicity bitLength oddSteps placed entry.1 dst hhead]
      exact ih htail _ 

theorem quotientStage_exactStepStage_getD_eq_transitionMultiplicityWeighted_of_pos
    (bitLength oddSteps placed : Nat) (stage : GapValueStage) (dst : GapResidueKey)
    (hpos : ∀ entry, entry ∈ stage.toList → 0 < entry.1.value) :
    (quotientStage (oddSteps - placed - 1) (exactStepStage bitLength oddSteps placed stage)).getD dst 0 =
      if placed < oddSteps then
        stageWeightedSum (fun key => transitionMultiplicity bitLength oddSteps placed key dst)
          (quotientStage (oddSteps - placed) stage)
      else 0 := by
  by_cases hplaced : placed < oddSteps
  · rw [quotientStage_exactStepStage_getD_eq_exactTransitionMultiplicityWeighted]
    simp [hplaced]
    rw [foldl_exactTransitionMultiplicity_eq_residueTransitionMultiplicity_of_pos
      bitLength oddSteps placed stage.toList hpos dst 0]
    rw [stageWeightedSum_quotientStage_eq]
  · rw [quotientStage_exactStepStage_getD_eq_exactTransitionMultiplicityWeighted]
    simp [hplaced]

theorem quotientStage_exactStepStage_getD_eq_transitionMultiplicityWeighted_exactStageAt
    (bitLength oddSteps placed : Nat) (dst : GapResidueKey) :
    (quotientStage (oddSteps - placed - 1)
        (exactStepStage bitLength oddSteps placed (exactStageAt bitLength oddSteps placed))).getD dst 0 =
      if placed < oddSteps then
        stageWeightedSum (fun key => transitionMultiplicity bitLength oddSteps placed key dst)
          (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed))
      else 0 := by
  exact quotientStage_exactStepStage_getD_eq_transitionMultiplicityWeighted_of_pos
    bitLength oddSteps placed (exactStageAt bitLength oddSteps placed) dst
    (exactStagePositive_toList (exactStagePositive_exactStageAt bitLength oddSteps placed))

theorem quotientStage_exactStageAt_succ_getD_eq_transitionMultiplicityWeighted
    (bitLength oddSteps placed : Nat) (dst : GapResidueKey) :
    (quotientStage (oddSteps - (placed + 1))
        (exactStageAt bitLength oddSteps (placed + 1))).getD dst 0 =
      if placed < oddSteps then
        stageWeightedSum (fun key => transitionMultiplicity bitLength oddSteps placed key dst)
          (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed))
      else 0 := by
  simpa [exactStageAt, Nat.sub_eq] using
    quotientStage_exactStepStage_getD_eq_transitionMultiplicityWeighted_exactStageAt
      bitLength oddSteps placed dst

theorem quotientStage_exactStageAt_succ_getD_eq_kernelStep_quotient
    (bitLength oddSteps placed : Nat) (dst : GapResidueKey) :
    (quotientStage (oddSteps - (placed + 1))
        (exactStageAt bitLength oddSteps (placed + 1))).getD dst 0 =
      (kernelStep bitLength oddSteps placed
        (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed))).getD dst 0 := by
  rw [quotientStage_exactStageAt_succ_getD_eq_transitionMultiplicityWeighted]
  rw [kernelStep_getD_eq_transitionMultiplicityWeighted]

theorem quotientStage_exactStageAt_zero_getD_eq_stageAt_zero_getD
    (bitLength oddSteps : Nat) (dst : GapResidueKey) :
    (quotientStage oddSteps (exactStageAt bitLength oddSteps 0)).getD dst 0 =
      (stageAt bitLength oddSteps 0).getD dst 0 := by
  calc
    (quotientStage oddSteps (exactStageAt bitLength oddSteps 0)).getD dst 0
        = (stageInsertAdd (quotientStage oddSteps ({} : GapValueStage))
            (residueKeyOf oddSteps { usedZeros := 0, value := 1 }) 1).getD dst 0 := by
              simpa [exactStageAt] using
                quotientStage_exactStageInsertAdd_getD oddSteps ({} : GapValueStage)
                  { usedZeros := 0, value := 1 } 1 dst
    _ = (stageInsertAdd {} { usedZeros := 0, residue := 1 % (3 ^ oddSteps) } 1).getD dst 0 := by
          simp [quotientStage, residueKeyOf]
    _ = (stageAt bitLength oddSteps 0).getD dst 0 := by
          rw [stageAt_zero]

theorem quotientStage_exactStageAt_getD_eq_stageAt_getD
    (bitLength oddSteps : Nat) :
    ∀ placed, ∀ dst,
      (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed)).getD dst 0 =
        (stageAt bitLength oddSteps placed).getD dst 0
  | 0, dst => quotientStage_exactStageAt_zero_getD_eq_stageAt_zero_getD bitLength oddSteps dst
  | n + 1, dst => by
      have hprev : ∀ dst,
          (quotientStage (oddSteps - n) (exactStageAt bitLength oddSteps n)).getD dst 0 =
            (stageAt bitLength oddSteps n).getD dst 0 :=
        quotientStage_exactStageAt_getD_eq_stageAt_getD bitLength oddSteps n
      have hposQ : stageCountsPositive (quotientStage (oddSteps - n) (exactStageAt bitLength oddSteps n)) :=
        stageCountsPositive_quotientStage_of_exactCountsPositive (oddSteps - n)
          (exactStageAt bitLength oddSteps n)
          (exactStageCountsPositive_exactStageAt bitLength oddSteps n)
      have hposS : stageCountsPositive (stageAt bitLength oddSteps n) :=
        stageCountsPositive_stageAt bitLength oddSteps n
      have hEq : Std.HashMap.Equiv
          (quotientStage (oddSteps - n) (exactStageAt bitLength oddSteps n))
          (stageAt bitLength oddSteps n) :=
        stageEquiv_of_forall_getD_eq_of_positive hposQ hposS hprev
      calc
        (quotientStage (oddSteps - (n + 1)) (exactStageAt bitLength oddSteps (n + 1))).getD dst 0
            = (kernelStep bitLength oddSteps n
                (quotientStage (oddSteps - n) (exactStageAt bitLength oddSteps n))).getD dst 0 :=
              quotientStage_exactStageAt_succ_getD_eq_kernelStep_quotient bitLength oddSteps n dst
        _ = (kernelStep bitLength oddSteps n (stageAt bitLength oddSteps n)).getD dst 0 :=
              kernelStep_getD_eq_of_equiv bitLength oddSteps n hEq dst
        _ = (stageAt bitLength oddSteps (n + 1)).getD dst 0 := by rw [stageAt_succ]

theorem quotientStage_exactStageAt_equiv_stageAt
    (bitLength oddSteps placed : Nat) :
    Std.HashMap.Equiv
      (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed))
      (stageAt bitLength oddSteps placed) := by
  apply stageEquiv_of_forall_getD_eq_of_positive
  · exact stageCountsPositive_quotientStage_of_exactCountsPositive (oddSteps - placed)
      (exactStageAt bitLength oddSteps placed)
      (exactStageCountsPositive_exactStageAt bitLength oddSteps placed)
  · exact stageCountsPositive_stageAt bitLength oddSteps placed
  · exact quotientStage_exactStageAt_getD_eq_stageAt_getD bitLength oddSteps placed

theorem stageMass_quotientStage_exactStageAt_eq_stageMass_stageAt
    (bitLength oddSteps placed : Nat) :
    stageMass (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed)) =
      stageMass (stageAt bitLength oddSteps placed) := by
  exact stageMass_eq_of_equiv (quotientStage_exactStageAt_equiv_stageAt bitLength oddSteps placed)

theorem exactStageMass_exactStageAt_eq_stageMass_stageAt
    (bitLength oddSteps placed : Nat) :
    exactStageMass (exactStageAt bitLength oddSteps placed) =
      stageMass (stageAt bitLength oddSteps placed) := by
  rw [← stageMass_quotientStage_eq_exactStageMass]
  exact stageMass_quotientStage_exactStageAt_eq_stageMass_stageAt bitLength oddSteps placed

theorem exactTotalCount_eq_totalCount
    (bitLength oddSteps : Nat) :
    exactTotalCount bitLength oddSteps = totalCount bitLength oddSteps := by
  rw [exactTotalCount_eq_exactStageMass_exactStageAt,
    exactStageMass_exactStageAt_eq_stageMass_stageAt,
    totalCount_eq_stageMass_stageAt]

private theorem foldl_exactTransitionSize_eq_residueTransitionSize_of_pos
    (bitLength oddSteps placed remaining : Nat)
    (entries : List (GapValueKey × Nat))
    (hpos : ∀ entry, entry ∈ entries → 0 < entry.1.value)
    (init : Nat)
    (hrem : remaining = oddSteps - placed) :
    entries.foldl
        (fun acc entry => acc + entry.2 * (exactStateTransitions bitLength oddSteps placed entry.1).size)
        init =
      entries.foldl
        (fun acc entry =>
          acc + entry.2 * (stateTransitions bitLength oddSteps placed (residueKeyOf remaining entry.1)).size)
        init := by
  subst hrem
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      have hhead : 0 < entry.1.value := hpos entry (by simp)
      have htail : ∀ e, e ∈ entries → 0 < e.1.value := by
        intro e he
        exact hpos e (by simp [he])
      rw [List.foldl_cons, List.foldl_cons]
      rw [exactStateTransitions_size_eq_stateTransitions_size bitLength oddSteps placed entry.1 hhead]
      exact ih htail _

/-- If every exact state in a full-value stage has positive current value, then
its one-step exact mass growth matches the residue-side weighted growth of the
quotiented stage, where each residue state is weighted by its number of
admissible gap transitions. This is the first honest sigma-level bridge between
the exact and residue DPs without assuming full stage equality. -/
theorem exactStageMass_exactStepStage_eq_weightedQuotientTransitionSize_of_pos
    (bitLength oddSteps placed : Nat) (stage : GapValueStage)
    (hpos : ∀ entry, entry ∈ stage.toList → 0 < entry.1.value) :
    exactStageMass (exactStepStage bitLength oddSteps placed stage) =
      stageWeightedSum (fun key => (stateTransitions bitLength oddSteps placed key).size)
        (quotientStage (oddSteps - placed) stage) := by
  by_cases hplaced : placed < oddSteps
  · rw [exactStageMass_exactStepStage_eq_transitionSizeSum]
    simp [hplaced]
    rw [stageWeightedSum_quotientStage_eq]
    exact foldl_exactTransitionSize_eq_residueTransitionSize_of_pos
      bitLength oddSteps placed (oddSteps - placed) stage.toList hpos 0 rfl
  · have hstep := stageMass_stepStage_eq_transitionSizeSum bitLength oddSteps placed
      (quotientStage (oddSteps - placed) stage)
    rw [exactStageMass_exactStepStage_eq_transitionSizeSum]
    simp [hplaced]
    rw [stageWeightedSum_transitionSize_eq_stageMass_stepStage]
    simpa [hplaced] using hstep.symm

theorem exactStageMass_exactStepStage_eq_weightedQuotientTransitionSize_exactStageAt
    (bitLength oddSteps placed : Nat) :
    exactStageMass (exactStepStage bitLength oddSteps placed (exactStageAt bitLength oddSteps placed)) =
      stageWeightedSum (fun key => (stateTransitions bitLength oddSteps placed key).size)
        (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed)) := by
  exact exactStageMass_exactStepStage_eq_weightedQuotientTransitionSize_of_pos
    bitLength oddSteps placed (exactStageAt bitLength oddSteps placed)
    (exactStagePositive_toList (exactStagePositive_exactStageAt bitLength oddSteps placed))

theorem stageMass_quotientStage_exactStepStage_eq_stageMass_kernelStep_quotient_of_pos
    (bitLength oddSteps placed : Nat) (stage : GapValueStage)
    (hpos : ∀ entry, entry ∈ stage.toList → 0 < entry.1.value) :
    stageMass (quotientStage (oddSteps - placed - 1)
        (exactStepStage bitLength oddSteps placed stage)) =
      stageMass (kernelStep bitLength oddSteps placed
        (quotientStage (oddSteps - placed) stage)) := by
  rw [stageMass_quotientStage_eq_exactStageMass]
  rw [exactStageMass_exactStepStage_eq_weightedQuotientTransitionSize_of_pos _ _ _ _ hpos]
  rw [stageWeightedSum_transitionSize_eq_stageMass_stepStage]

theorem stageMass_quotientStage_exactStageAt_succ_eq_stageMass_kernelStep_quotient
    (bitLength oddSteps placed : Nat) :
    stageMass (quotientStage (oddSteps - (placed + 1))
        (exactStageAt bitLength oddSteps (placed + 1))) =
      stageMass (kernelStep bitLength oddSteps placed
        (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed))) := by
  simpa [exactStageAt, Nat.sub_eq] using
    stageMass_quotientStage_exactStepStage_eq_stageMass_kernelStep_quotient_of_pos
      bitLength oddSteps placed (exactStageAt bitLength oddSteps placed)
      (exactStagePositive_toList (exactStagePositive_exactStageAt bitLength oddSteps placed))

theorem mul_stageMass_quotientStage_exactStageAt_le_stageMass_quotientStage_exactStageAt_succ_of_transitionSize_lower
    (bitLength oddSteps placed : Nat) (m : Nat)
    (hbound : ∀ entry,
      entry ∈ (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed)).toList →
        m ≤ (stateTransitions bitLength oddSteps placed entry.1).size) :
    m * stageMass (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed)) ≤
      stageMass (quotientStage (oddSteps - (placed + 1)) (exactStageAt bitLength oddSteps (placed + 1))) := by
  have hstep :
      m * stageMass (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed)) ≤
        stageMass (kernelStep bitLength oddSteps placed
          (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed))) := by
    exact mul_stageMass_le_stageMass_stepStage_of_transitionSize_lower
      bitLength oddSteps placed
      (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed))
      m hbound
  rw [stageMass_quotientStage_exactStageAt_succ_eq_stageMass_kernelStep_quotient]
  exact hstep

theorem pow_le_exactStageMass_exactStageAt_of_transitionSize_lower
    (bitLength oddSteps m : Nat)
    (hbound : ∀ placed entry,
      placed < oddSteps →
      entry ∈ (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed)).toList →
        m ≤ (stateTransitions bitLength oddSteps placed entry.1).size) :
    ∀ placed, placed ≤ oddSteps → m ^ placed ≤ exactStageMass (exactStageAt bitLength oddSteps placed) := by
  intro placed
  induction placed with
  | zero =>
      intro _h
      rw [exactStageAt_zero]
      simp [exactStageMass_exactStageInsertAdd]
  | succ placed ih =>
      intro hle
      have hlt : placed < oddSteps := Nat.lt_of_succ_le hle
      have hrec : m ^ placed ≤ exactStageMass (exactStageAt bitLength oddSteps placed) :=
        ih (Nat.le_of_succ_le hle)
      have hstep :
          m * exactStageMass (exactStageAt bitLength oddSteps placed) ≤
            exactStageMass (exactStageAt bitLength oddSteps (placed + 1)) := by
        have hq :
            m * stageMass (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed)) ≤
              stageMass (quotientStage (oddSteps - (placed + 1))
                (exactStageAt bitLength oddSteps (placed + 1))) := by
          exact mul_stageMass_quotientStage_exactStageAt_le_stageMass_quotientStage_exactStageAt_succ_of_transitionSize_lower
            bitLength oddSteps placed m (fun entry hmem => hbound placed entry hlt hmem)
        simpa [stageMass_quotientStage_eq_exactStageMass] using hq
      have hmul :
          m * (m ^ placed) ≤ m * exactStageMass (exactStageAt bitLength oddSteps placed) :=
        Nat.mul_le_mul_left _ hrec
      have hfinal := le_trans hmul hstep
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hfinal

theorem pow_oddSteps_le_exactStageMass_exactStageAt_of_transitionSize_lower
    (bitLength oddSteps m : Nat)
    (hbound : ∀ placed entry,
      placed < oddSteps →
      entry ∈ (quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed)).toList →
        m ≤ (stateTransitions bitLength oddSteps placed entry.1).size) :
    m ^ oddSteps ≤ exactStageMass (exactStageAt bitLength oddSteps oddSteps) := by
  exact pow_le_exactStageMass_exactStageAt_of_transitionSize_lower bitLength oddSteps m hbound
    oddSteps (Nat.le_refl _)

/-- Stagewise product of lower growth factors along the theorem-friendly exact
stage chain. This is the right abstraction when the arithmetic input controls
average mass growth rather than a uniform per-state branching floor. -/
def growthProduct (lower : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => growthProduct lower n * lower n

theorem growthProduct_le_exactStageMass_exactStageAt_of_stageMass_growth
    (bitLength oddSteps : Nat) (lower : Nat → Nat)
    (hgrowth : ∀ placed, placed < oddSteps →
      lower placed * exactStageMass (exactStageAt bitLength oddSteps placed) ≤
        exactStageMass (exactStageAt bitLength oddSteps (placed + 1))) :
    ∀ placed, placed ≤ oddSteps →
      growthProduct lower placed ≤ exactStageMass (exactStageAt bitLength oddSteps placed) := by
  intro placed
  induction placed with
  | zero =>
      intro _h
      rw [exactStageAt_zero]
      simp [growthProduct, exactStageMass_exactStageInsertAdd]
  | succ placed ih =>
      intro hle
      have hlt : placed < oddSteps := Nat.lt_of_succ_le hle
      have hprev : growthProduct lower placed ≤ exactStageMass (exactStageAt bitLength oddSteps placed) :=
        ih (Nat.le_of_succ_le hle)
      have hmul :
          growthProduct lower placed * lower placed ≤
            exactStageMass (exactStageAt bitLength oddSteps placed) * lower placed :=
        Nat.mul_le_mul_right _ hprev
      have hstep :
          exactStageMass (exactStageAt bitLength oddSteps placed) * lower placed ≤
            exactStageMass (exactStageAt bitLength oddSteps (placed + 1)) := by
        simpa [Nat.mul_comm] using hgrowth placed hlt
      exact le_trans
        (by simpa [growthProduct, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul)
        hstep

theorem growthProduct_num_le_growthProduct_den_mul_exactStageMass_prefix_of_stageMass_ratio
    (bitLength oddSteps : Nat) (num den : Nat → Nat)
    (hratio : ∀ placed, placed < oddSteps →
      num placed * exactStageMass (exactStageAt bitLength oddSteps placed) ≤
        den placed * exactStageMass (exactStageAt bitLength oddSteps (placed + 1))) :
    ∀ placed, placed ≤ oddSteps →
      growthProduct num placed ≤
        growthProduct den placed * exactStageMass (exactStageAt bitLength oddSteps placed) := by
  intro placed
  induction placed with
  | zero =>
      intro _h
      rw [exactStageAt_zero]
      simp [growthProduct, exactStageMass_exactStageInsertAdd]
  | succ placed ih =>
      intro hle
      have hlt : placed < oddSteps := Nat.lt_of_succ_le hle
      have hprev :
          growthProduct num placed ≤
            growthProduct den placed * exactStageMass (exactStageAt bitLength oddSteps placed) :=
        ih (Nat.le_of_succ_le hle)
      have hmul1 :
          growthProduct num placed * num placed ≤
            (growthProduct den placed * exactStageMass (exactStageAt bitLength oddSteps placed)) * num placed :=
        Nat.mul_le_mul_right _ hprev
      have hstep' :
          exactStageMass (exactStageAt bitLength oddSteps placed) * num placed ≤
            den placed * exactStageMass (exactStageAt bitLength oddSteps (placed + 1)) := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hratio placed hlt
      have hmul2 :
          (growthProduct den placed * exactStageMass (exactStageAt bitLength oddSteps placed)) * num placed ≤
            (growthProduct den placed * den placed) * exactStageMass (exactStageAt bitLength oddSteps (placed + 1)) := by
        have := Nat.mul_le_mul_left (growthProduct den placed) hstep'
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
      have hfinal := le_trans hmul1 hmul2
      simpa [growthProduct, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hfinal

theorem growthProduct_num_le_growthProduct_den_mul_exactStageMass_of_stageMass_ratio
    (bitLength oddSteps : Nat) (num den : Nat → Nat)
    (hratio : ∀ placed, placed < oddSteps →
      num placed * exactStageMass (exactStageAt bitLength oddSteps placed) ≤
        den placed * exactStageMass (exactStageAt bitLength oddSteps (placed + 1))) :
    growthProduct num oddSteps ≤
      growthProduct den oddSteps * exactStageMass (exactStageAt bitLength oddSteps oddSteps) := by
  exact growthProduct_num_le_growthProduct_den_mul_exactStageMass_prefix_of_stageMass_ratio
    bitLength oddSteps num den hratio oddSteps (Nat.le_refl _)

/-- The exact stagewise floor growth factor extracted from the theorem-friendly
exact chain itself: next-stage mass divided by current-stage mass after
quotienting to the residue surface and applying one residue step. If these
factors can be controlled from below in the balanced regime, the cumulative
product gives a direct exact-count lower bound. -/
def exactStageGrowthLower (bitLength oddSteps placed : Nat) : Nat :=
  let stage := quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed)
  stageMass (kernelStep bitLength oddSteps placed stage) / stageMass stage

/-- Intrinsic cumulative lower-bound product extracted from the exact
stage-growth floor sequence. This packages the remaining lower-bound problem
into one concrete exact counting object. -/
def exactGrowthLowerProduct (bitLength oddSteps : Nat) : Nat :=
  growthProduct (exactStageGrowthLower bitLength oddSteps) oddSteps

theorem exactStageGrowthLower_mul_exactStageMass_exactStageAt_le_succ
    (bitLength oddSteps placed : Nat) :
    exactStageGrowthLower bitLength oddSteps placed * exactStageMass (exactStageAt bitLength oddSteps placed) ≤
      exactStageMass (exactStageAt bitLength oddSteps (placed + 1)) := by
  let stage := quotientStage (oddSteps - placed) (exactStageAt bitLength oddSteps placed)
  have hmass : stageMass stage = exactStageMass (exactStageAt bitLength oddSteps placed) := by
    exact stageMass_quotientStage_eq_exactStageMass (oddSteps - placed)
      (exactStageAt bitLength oddSteps placed)
  have hnext :
      stageMass (kernelStep bitLength oddSteps placed stage) =
        exactStageMass (exactStageAt bitLength oddSteps (placed + 1)) := by
    rw [← stageMass_quotientStage_exactStageAt_succ_eq_stageMass_kernelStep_quotient]
    simp [stageMass_quotientStage_eq_exactStageMass]
  have hdiv :
      (stageMass (kernelStep bitLength oddSteps placed stage) / stageMass stage) * stageMass stage ≤
        stageMass (kernelStep bitLength oddSteps placed stage) :=
    Nat.div_mul_le_self _ _
  have hdiv' :
      (stageMass (kernelStep bitLength oddSteps placed stage) / stageMass stage) *
          exactStageMass (exactStageAt bitLength oddSteps placed) ≤
        stageMass (kernelStep bitLength oddSteps placed stage) := by
    simpa [hmass] using hdiv
  have hnext' :
      stageMass (kernelStep bitLength oddSteps placed stage) ≤
        exactStageMass (exactStageAt bitLength oddSteps (placed + 1)) := by
    simpa using hnext.le
  exact le_trans (by simpa [exactStageGrowthLower, stage] using hdiv') hnext'

theorem growthProduct_exactStageGrowthLower_le_exactStageMass_exactStageAt
    (bitLength oddSteps : Nat) :
    growthProduct (exactStageGrowthLower bitLength oddSteps) oddSteps ≤
      exactStageMass (exactStageAt bitLength oddSteps oddSteps) := by
  exact growthProduct_le_exactStageMass_exactStageAt_of_stageMass_growth bitLength oddSteps
    (exactStageGrowthLower bitLength oddSteps)
    (fun placed _ =>
      exactStageGrowthLower_mul_exactStageMass_exactStageAt_le_succ bitLength oddSteps placed)
    oddSteps (Nat.le_refl _)

theorem exactGrowthLowerProduct_le_exactStageMass_exactStageAt
    (bitLength oddSteps : Nat) :
    exactGrowthLowerProduct bitLength oddSteps ≤
      exactStageMass (exactStageAt bitLength oddSteps oddSteps) := by
  exact growthProduct_exactStageGrowthLower_le_exactStageMass_exactStageAt bitLength oddSteps

theorem exactGrowthLowerProduct_le_stageMass_stageAt
    (bitLength oddSteps : Nat) :
    exactGrowthLowerProduct bitLength oddSteps ≤
      stageMass (stageAt bitLength oddSteps oddSteps) := by
  rw [← exactStageMass_exactStageAt_eq_stageMass_stageAt]
  exact exactGrowthLowerProduct_le_exactStageMass_exactStageAt bitLength oddSteps

end CollatzThreeAdic
