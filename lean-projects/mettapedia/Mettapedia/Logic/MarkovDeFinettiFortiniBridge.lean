import Mettapedia.Logic.MarkovDeFinettiAnchorAdapter
import Mathlib.Data.Nat.Nth

/-!
# Markov de Finetti: Fortini-Style Parallel Bridge

This file pre-formalizes a Fortini successor-matrix route as a parallel track.
It does not touch the quantitative HardBEST route.
-/

noncomputable section

namespace Mettapedia.Logic

open MeasureTheory
open scoped BigOperators

namespace MarkovDeFinettiHard

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence

variable {k : ℕ}

/-- Successor state one step after time `t`. -/
def successorAt (ω : ℕ → Fin k) (t : ℕ) : Fin k := ω (t + 1)

/-- Visit-time set for state `i`. -/
def visitSet (ω : ℕ → Fin k) (i : Fin k) : Set ℕ := {t : ℕ | ω t = i}

/-- Number of visits to state `i` strictly before time `t`. -/
def visitCountBefore (ω : ℕ → Fin k) (i : Fin k) (t : ℕ) : ℕ :=
  Finset.sum (Finset.range t) (fun s => if ω s = i then (1 : ℕ) else (0 : ℕ))

/-- Measurable row-successor process at anchor `i` and time index `n`.
At times not visiting `i`, this process returns `i` itself. -/
def rowSuccessorProcess (i : Fin k) (n : ℕ) (ω : ℕ → Fin k) : Fin k :=
  if ω n = i then successorAt (k := k) ω n else i

/-- `t` is the time of the `(n+1)`-st visit to anchor `i`
(0-indexed by `n`). -/
def isNthVisitTime (ω : ℕ → Fin k) (i : Fin k) (n t : ℕ) : Prop :=
  ω t = i ∧ visitCountBefore (k := k) ω i t = n

/-- Existence of a `(n+1)`-st visit time to anchor `i`. -/
def nthVisitTimeExists (ω : ℕ → Fin k) (i : Fin k) (n : ℕ) : Prop :=
  ∃ t : ℕ, isNthVisitTime (k := k) ω i n t

/-- Optional `(n+1)`-st visit time to anchor `i`. -/
noncomputable def nthVisitTime (ω : ℕ → Fin k) (i : Fin k) (n : ℕ) : Option ℕ :=
  by
    classical
    exact if h : nthVisitTimeExists (k := k) ω i n then some (Nat.find h) else none

/-- Visit-indexed row successor (Fortini-style object, totalized at `i` when
the `(n+1)`-st visit does not exist). -/
noncomputable def rowSuccessorAtNthVisit (i : Fin k) (n : ℕ) (ω : ℕ → Fin k) : Fin k :=
  match nthVisitTime (k := k) ω i n with
  | some t => successorAt (k := k) ω t
  | none => i

/-- Full row process indexed by visit number. -/
noncomputable def rowSuccessorVisitProcess (i : Fin k) (ω : ℕ → Fin k) : ℕ → Fin k :=
  fun n => rowSuccessorAtNthVisit (k := k) i n ω

/-- Finite-cylinder event on row-process trajectories. -/
def rowFiniteCylinder (S : Finset ℕ) (v : ℕ → Fin k) : Set (ℕ → Fin k) :=
  {r | ∀ n ∈ S, r n = v n}

/-- Finite-cylinder event pulled back along the visit-indexed row process. -/
def rowVisitCylinderEvent (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) : Set (ℕ → Fin k) :=
  {ω | ∀ n ∈ S, rowSuccessorAtNthVisit (k := k) i n ω = v n}

/-- Pushforward law of the visit-indexed row process under an extension measure `P`. -/
noncomputable def rowProcessLaw (P : Measure (ℕ → Fin k)) (i : Fin k) : Measure (ℕ → Fin k) :=
  Measure.map (rowSuccessorVisitProcess (k := k) i) P

/-- State-conditioned successor event at time `t`. -/
def successorEventAt (ω : ℕ → Fin k) (i a : Fin k) (t : ℕ) : Prop :=
  ω t = i ∧ successorAt (k := k) ω t = a

/-- Row-successor count vector for a finite trajectory summary. -/
def rowSuccessorCountVec {n : ℕ} (xs : Fin (n + 1) → Fin k) (i : Fin k) : Fin k → ℕ :=
  fun a => MarkovExchangeability.transCount (n := n) xs i a

/-- Strong row recurrence at anchor `i`: infinitely many visits to `i`. -/
def strongRowRecurrentAt (ω : ℕ → Fin k) (i : Fin k) : Prop :=
  Set.Infinite (visitSet (k := k) ω i)

@[simp] lemma successorAt_eq (ω : ℕ → Fin k) (t : ℕ) :
    successorAt (k := k) ω t = ω (t + 1) := rfl

@[simp] lemma successorEventAt_iff (ω : ℕ → Fin k) (i a : Fin k) (t : ℕ) :
    successorEventAt (k := k) ω i a t ↔ ω t = i ∧ ω (t + 1) = a := by
  rfl

lemma measurable_visitCountBefore (i : Fin k) (t : ℕ) :
    Measurable (fun ω : ℕ → Fin k => visitCountBefore (k := k) ω i t) := by
  classical
  change Measurable
    (fun ω : ℕ → Fin k =>
      Finset.sum (Finset.range t) (fun s => if ω s = i then (1 : ℕ) else (0 : ℕ)))
  refine Finset.measurable_sum (s := Finset.range t)
    (f := fun s => fun ω : ℕ → Fin k => if ω s = i then (1 : ℕ) else (0 : ℕ)) ?_
  intro s hs
  have hpred : MeasurableSet {ω : ℕ → Fin k | ω s = i} := by
    have hcoord : Measurable (fun ω : ℕ → Fin k => ω s) := measurable_pi_apply s
    simpa [Set.preimage] using hcoord (MeasurableSet.singleton i)
  exact
    ((measurable_const : Measurable (fun _ : ℕ → Fin k => (1 : ℕ))).piecewise
      hpred
      (measurable_const : Measurable (fun _ : ℕ → Fin k => (0 : ℕ)))
    )

lemma measurableSet_isNthVisitTime (i : Fin k) (n t : ℕ) :
    MeasurableSet {ω : ℕ → Fin k | isNthVisitTime (k := k) ω i n t} := by
  have hvisit : MeasurableSet {ω : ℕ → Fin k | ω t = i} := by
    have hcoord : Measurable (fun ω : ℕ → Fin k => ω t) := measurable_pi_apply t
    simpa [Set.preimage] using hcoord (MeasurableSet.singleton i)
  have hcount : MeasurableSet
      {ω : ℕ → Fin k | visitCountBefore (k := k) ω i t = n} := by
    have hmeas := measurable_visitCountBefore (k := k) i t
    simpa [Set.preimage] using hmeas (MeasurableSet.singleton n)
  simpa [isNthVisitTime, Set.setOf_and] using hvisit.inter hcount

lemma measurableSet_nthVisitTimeExists (i : Fin k) (n : ℕ) :
    MeasurableSet {ω : ℕ → Fin k | nthVisitTimeExists (k := k) ω i n} := by
  unfold nthVisitTimeExists
  simpa [Set.setOf_exists] using
    (MeasurableSet.iUnion (fun t => measurableSet_isNthVisitTime (k := k) i n t))

lemma visitCountBefore_eq_natCount
    (ω : ℕ → Fin k) (i : Fin k) :
    ∀ t : ℕ, visitCountBefore (k := k) ω i t = Nat.count (fun s => ω s = i) t := by
  intro t
  unfold visitCountBefore
  simp [Nat.count_eq_card_filter_range]

lemma visitCountBefore_strict_mono_of_visit
    (ω : ℕ → Fin k) (i : Fin k) {t u : ℕ}
    (ht : ω t = i) (htu : t < u) :
    visitCountBefore (k := k) ω i t < visitCountBefore (k := k) ω i u := by
  have hcount :
      Nat.count (fun s => ω s = i) t <
        Nat.count (fun s => ω s = i) u :=
    Nat.count_strict_mono (p := fun s => ω s = i) (m := t) (n := u) ht htu
  simpa [visitCountBefore_eq_natCount (k := k) ω i t,
    visitCountBefore_eq_natCount (k := k) ω i u] using hcount

lemma isNthVisitTime_unique
    (ω : ℕ → Fin k) (i : Fin k) (n t u : ℕ)
    (ht : isNthVisitTime (k := k) ω i n t)
    (hu : isNthVisitTime (k := k) ω i n u) :
    t = u := by
  rcases lt_trichotomy t u with hlt | heq | hgt
  · exfalso
    rcases ht with ⟨ht_visit, ht_count⟩
    rcases hu with ⟨_, hu_count⟩
    have hcount_lt :
        visitCountBefore (k := k) ω i t < visitCountBefore (k := k) ω i u :=
      visitCountBefore_strict_mono_of_visit (k := k) ω i ht_visit hlt
    rw [ht_count, hu_count] at hcount_lt
    have : n < n := hcount_lt
    exact Nat.lt_irrefl _ this
  · exact heq
  · exfalso
    rcases ht with ⟨_, ht_count⟩
    rcases hu with ⟨hu_visit, hu_count⟩
    have hcount_lt :
        visitCountBefore (k := k) ω i u < visitCountBefore (k := k) ω i t :=
      visitCountBefore_strict_mono_of_visit (k := k) ω i hu_visit hgt
    rw [ht_count, hu_count] at hcount_lt
    have : n < n := hcount_lt
    exact Nat.lt_irrefl _ this

lemma nthVisitTime_eq_some_iff
    (ω : ℕ → Fin k) (i : Fin k) (n t : ℕ) :
    nthVisitTime (k := k) ω i n = some t ↔
      isNthVisitTime (k := k) ω i n t := by
  constructor
  · intro hsome
    classical
    unfold nthVisitTime at hsome
    by_cases hex : nthVisitTimeExists (k := k) ω i n
    · simp [hex] at hsome
      simpa [hsome] using (Nat.find_spec hex)
    · simp [hex] at hsome
  · intro ht
    classical
    have hex : nthVisitTimeExists (k := k) ω i n := ⟨t, ht⟩
    unfold nthVisitTime
    simp [hex]
    exact isNthVisitTime_unique (k := k) ω i n (Nat.find hex) t (Nat.find_spec hex) ht

lemma nthVisitTime_eq_none_iff
    (ω : ℕ → Fin k) (i : Fin k) (n : ℕ) :
    nthVisitTime (k := k) ω i n = none ↔
      ¬ nthVisitTimeExists (k := k) ω i n := by
  classical
  unfold nthVisitTime
  by_cases hex : nthVisitTimeExists (k := k) ω i n
  · simp [hex]
  · simp [hex]

lemma measurableSet_nthVisitTime_eq_some (i : Fin k) (n t : ℕ) :
    MeasurableSet {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = some t} := by
  have hEq :
      {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = some t} =
        {ω : ℕ → Fin k | isNthVisitTime (k := k) ω i n t} := by
    ext ω
    exact nthVisitTime_eq_some_iff (k := k) ω i n t
  simpa [hEq] using measurableSet_isNthVisitTime (k := k) i n t

lemma measurableSet_nthVisitTime_eq_none (i : Fin k) (n : ℕ) :
    MeasurableSet {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none} := by
  have hEq :
      {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none} =
        {ω : ℕ → Fin k | ¬ nthVisitTimeExists (k := k) ω i n} := by
    ext ω
    exact nthVisitTime_eq_none_iff (k := k) ω i n
  simpa [hEq, Set.compl_setOf] using
    (measurableSet_nthVisitTimeExists (k := k) i n).compl

lemma measurableSet_successorAt_eq (a : Fin k) (t : ℕ) :
    MeasurableSet {ω : ℕ → Fin k | successorAt (k := k) ω t = a} := by
  have hcoord : Measurable (fun ω : ℕ → Fin k => ω (t + 1)) := measurable_pi_apply (t + 1)
  simpa [successorAt, Set.preimage] using hcoord (MeasurableSet.singleton a)

lemma measurableSet_rowSuccessorAtNthVisit_eq
    (i : Fin k) (n : ℕ) (a : Fin k) :
    MeasurableSet {ω : ℕ → Fin k | rowSuccessorAtNthVisit (k := k) i n ω = a} := by
  have hdecomp :
      {ω : ℕ → Fin k | rowSuccessorAtNthVisit (k := k) i n ω = a} =
        ({ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none} ∩
          {ω : ℕ → Fin k | i = a}) ∪
          ⋃ t : ℕ,
            ({ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = some t} ∩
              {ω : ℕ → Fin k | successorAt (k := k) ω t = a}) := by
    ext ω
    constructor
    · intro hω
      unfold rowSuccessorAtNthVisit at hω
      cases hnt : nthVisitTime (k := k) ω i n with
      | none =>
          left
          refine ⟨hnt, ?_⟩
          simpa [hnt] using hω
      | some t =>
          right
          refine Set.mem_iUnion.mpr ⟨t, ?_⟩
          refine ⟨hnt, ?_⟩
          simpa [hnt] using hω
    · intro hω
      rcases hω with hnone | hsome
      · rcases hnone with ⟨hnt, hia⟩
        have hia' : i = a := by simpa using hia
        change rowSuccessorAtNthVisit (k := k) i n ω = a
        have hnt' : nthVisitTime (k := k) ω i n = none := by simpa using hnt
        unfold rowSuccessorAtNthVisit
        rw [hnt']
        exact hia'
      · rcases Set.mem_iUnion.mp hsome with ⟨t, ht⟩
        rcases ht with ⟨hnt, hsucc⟩
        have hsucc' : successorAt (k := k) ω t = a := by simpa using hsucc
        change rowSuccessorAtNthVisit (k := k) i n ω = a
        have hnt' : nthVisitTime (k := k) ω i n = some t := by simpa using hnt
        unfold rowSuccessorAtNthVisit
        rw [hnt']
        exact hsucc'
  have hnone : MeasurableSet {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none} :=
    measurableSet_nthVisitTime_eq_none (k := k) i n
  have hiEqA : MeasurableSet {ω : ℕ → Fin k | i = a} := by
    by_cases hia : i = a
    · simp [hia]
    · simp [hia]
  have hleft :
      MeasurableSet
        ({ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none} ∩
          {ω : ℕ → Fin k | i = a}) := hnone.inter hiEqA
  have hright :
      MeasurableSet
        (⋃ t : ℕ,
          ({ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = some t} ∩
            {ω : ℕ → Fin k | successorAt (k := k) ω t = a})) :=
    MeasurableSet.iUnion (fun t =>
      (measurableSet_nthVisitTime_eq_some (k := k) i n t).inter
        (measurableSet_successorAt_eq (k := k) a t))
  simpa [hdecomp] using hleft.union hright

lemma measurableSet_preimage_rowSuccessorAtNthVisit_singleton
    (i : Fin k) (n : ℕ) (a : Fin k) :
    MeasurableSet ((rowSuccessorAtNthVisit (k := k) i n) ⁻¹' ({a} : Set (Fin k))) := by
  simpa [Set.preimage] using
    measurableSet_rowSuccessorAtNthVisit_eq (k := k) i n a

lemma measurable_rowSuccessorAtNthVisit
    (i : Fin k) (n : ℕ) :
    Measurable (fun ω : ℕ → Fin k => rowSuccessorAtNthVisit (k := k) i n ω) := by
  refine measurable_to_countable' (f := fun ω : ℕ → Fin k => rowSuccessorAtNthVisit (k := k) i n ω) ?_
  intro a
  simpa using measurableSet_preimage_rowSuccessorAtNthVisit_singleton (k := k) i n a

lemma measurable_rowSuccessorVisitProcess
    (i : Fin k) :
    Measurable (rowSuccessorVisitProcess (k := k) i) := by
  rw [measurable_pi_iff]
  intro n
  simpa [rowSuccessorVisitProcess] using
    measurable_rowSuccessorAtNthVisit (k := k) i n

lemma measurableSet_rowFiniteCylinder
    (S : Finset ℕ) (v : ℕ → Fin k) :
    MeasurableSet (rowFiniteCylinder (k := k) S v) := by
  have hEq :
      rowFiniteCylinder (k := k) S v =
        ⋂ n ∈ S, {r : ℕ → Fin k | r n = v n} := by
    ext r
    simp [rowFiniteCylinder]
  rw [hEq]
  refine Finset.measurableSet_biInter S ?_
  intro n hnS
  have hcoord : Measurable (fun r : ℕ → Fin k => r n) := measurable_pi_apply n
  simpa [Set.preimage] using hcoord (MeasurableSet.singleton (v n))

lemma measurableSet_rowVisitCylinderEvent
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) :
    MeasurableSet (rowVisitCylinderEvent (k := k) i S v) := by
  have hEq :
      rowVisitCylinderEvent (k := k) i S v =
        ⋂ n ∈ S, {ω : ℕ → Fin k | rowSuccessorAtNthVisit (k := k) i n ω = v n} := by
    ext ω
    simp [rowVisitCylinderEvent]
  rw [hEq]
  refine Finset.measurableSet_biInter S ?_
  intro n hnS
  exact measurableSet_rowSuccessorAtNthVisit_eq (k := k) i n (v n)

lemma preimage_rowFiniteCylinder_eq_rowVisitCylinderEvent
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) :
    (rowSuccessorVisitProcess (k := k) i) ⁻¹' rowFiniteCylinder (k := k) S v =
      rowVisitCylinderEvent (k := k) i S v := by
  ext ω
  rfl

lemma rowProcessLaw_apply
    (P : Measure (ℕ → Fin k)) (i : Fin k) {A : Set (ℕ → Fin k)}
    (hA : MeasurableSet A) :
    rowProcessLaw (k := k) P i A =
      P ((rowSuccessorVisitProcess (k := k) i) ⁻¹' A) := by
  simpa [rowProcessLaw] using
    (Measure.map_apply (measurable_rowSuccessorVisitProcess (k := k) i) hA)

lemma rowProcessLaw_rowFiniteCylinder_apply
    (P : Measure (ℕ → Fin k)) (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) :
    rowProcessLaw (k := k) P i (rowFiniteCylinder (k := k) S v) =
      P (rowVisitCylinderEvent (k := k) i S v) := by
  rw [rowProcessLaw_apply (k := k) P i (hA := measurableSet_rowFiniteCylinder (k := k) S v)]
  simp [preimage_rowFiniteCylinder_eq_rowVisitCylinderEvent]

/-- Row recurrence gives existence of each `(n+1)`-st visit time. -/
lemma nthVisitTimeExists_of_strongRowRecurrentAt
    (ω : ℕ → Fin k) (i : Fin k) (n : ℕ)
    (hrow : strongRowRecurrentAt (k := k) ω i) :
    nthVisitTimeExists (k := k) ω i n := by
  refine ⟨Nat.nth (fun t => ω t = i) n, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [visitSet] using
      (Nat.nth_mem_of_infinite (p := fun t => ω t = i) hrow n)
  ·
    have hcount :
        Nat.count (fun t => ω t = i) (Nat.nth (fun t => ω t = i) n) = n :=
      Nat.count_nth_of_infinite (p := fun t => ω t = i) (by simpa [visitSet] using hrow) n
    simpa [visitCountBefore_eq_natCount] using hcount

/-- Finite-coordinate permutation event equivalence for row-successor process. -/
lemma rowSuccessorVisit_perm_event_iff
    (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ)
    (v : ℕ → Fin k) (ω : ℕ → Fin k) :
    (∀ n ∈ S, rowSuccessorAtNthVisit (k := k) i (σ n) ω = v n) ↔
      (∀ m ∈ S.image σ, rowSuccessorAtNthVisit (k := k) i m ω = v (σ.symm m)) := by
  constructor
  · intro h m hm
    rcases Finset.mem_image.mp hm with ⟨n, hnS, hmn⟩
    subst hmn
    simpa using h n hnS
  · intro h n hnS
    have hm : σ n ∈ S.image σ := Finset.mem_image.mpr ⟨n, hnS, rfl⟩
    have := h (σ n) hm
    simpa using this

/-- Set-level version of finite-coordinate permutation equivalence for row events. -/
lemma rowSuccessorVisit_perm_event_set_eq
    (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ)
    (v : ℕ → Fin k) :
    {ω : ℕ → Fin k | ∀ n ∈ S, rowSuccessorAtNthVisit (k := k) i (σ n) ω = v n} =
      {ω : ℕ → Fin k | ∀ m ∈ S.image σ, rowSuccessorAtNthVisit (k := k) i m ω = v (σ.symm m)} := by
  ext ω
  exact rowSuccessorVisit_perm_event_iff (k := k) i σ S v ω

lemma measure_rowSuccessorVisit_perm_event
    (P : Measure (ℕ → Fin k))
    (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) :
    P {ω : ℕ → Fin k | ∀ n ∈ S, rowSuccessorAtNthVisit (k := k) i (σ n) ω = v n} =
      P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) := by
  rw [rowVisitCylinderEvent]
  exact congrArg P (rowSuccessorVisit_perm_event_set_eq (k := k) i σ S v)

lemma measurableSet_rowSuccessorVisit_perm_event
    (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) :
    MeasurableSet {ω : ℕ → Fin k |
      ∀ n ∈ S, rowSuccessorAtNthVisit (k := k) i (σ n) ω = v n} := by
  rw [rowSuccessorVisit_perm_event_set_eq (k := k) i σ S v]
  exact measurableSet_rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))

lemma rowFiniteCylinder_perm_set_eq
    (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) :
    {r : ℕ → Fin k | ∀ n ∈ S, r (σ n) = v n} =
      rowFiniteCylinder (k := k) (S.image σ) (fun m => v (σ.symm m)) := by
  ext r
  constructor
  · intro h m hm
    rcases Finset.mem_image.mp hm with ⟨n, hnS, hmn⟩
    subst hmn
    simpa using h n hnS
  · intro h n hnS
    have hm : σ n ∈ S.image σ := Finset.mem_image.mpr ⟨n, hnS, rfl⟩
    have := h (σ n) hm
    simpa [rowFiniteCylinder] using this

lemma rowProcessLaw_perm_cylinder_apply
    (P : Measure (ℕ → Fin k))
    (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) :
    rowProcessLaw (k := k) P i
      {r : ℕ → Fin k | ∀ n ∈ S, r (σ n) = v n} =
    rowProcessLaw (k := k) P i
      (rowFiniteCylinder (k := k) (S.image σ) (fun m => v (σ.symm m))) := by
  exact congrArg (rowProcessLaw (k := k) P i) (rowFiniteCylinder_perm_set_eq (k := k) σ S v)

@[simp] lemma rowSuccessorCountVec_apply {n : ℕ}
    (xs : Fin (n + 1) → Fin k) (i a : Fin k) :
    rowSuccessorCountVec (k := k) xs i a =
      MarkovExchangeability.transCount (n := n) xs i a := rfl

lemma measurableSet_successorEventAt (i a : Fin k) (t : ℕ) :
    MeasurableSet {ω : ℕ → Fin k | successorEventAt (k := k) ω i a t} := by
  have ht : Measurable fun ω : ℕ → Fin k => ω t := measurable_pi_apply t
  have htp1 : Measurable fun ω : ℕ → Fin k => ω (t + 1) := measurable_pi_apply (t + 1)
  have hi : MeasurableSet {x : Fin k | x = i} := measurableSet_singleton i
  have ha : MeasurableSet {x : Fin k | x = a} := measurableSet_singleton a
  have h1 : MeasurableSet {ω : ℕ → Fin k | ω t = i} := by
    simpa [Set.preimage] using ht hi
  have h2 : MeasurableSet {ω : ℕ → Fin k | ω (t + 1) = a} := by
    simpa [Set.preimage] using htp1 ha
  simpa [successorEventAt, successorAt, Set.setOf_and] using h1.inter h2

lemma measurable_rowSuccessorProcess (i : Fin k) (n : ℕ) :
    Measurable (rowSuccessorProcess (k := k) i n) := by
  have hpred :
      MeasurableSet {ω : ℕ → Fin k | ω n = i} := by
    have hcoord : Measurable (fun ω : ℕ → Fin k => ω n) := measurable_pi_apply n
    simpa [Set.preimage] using hcoord (MeasurableSet.singleton i)
  have hsucc : Measurable (successorAt (k := k) · n) := by
    simpa [successorAt] using (measurable_pi_apply (n + 1))
  have hconst : Measurable (fun _ : ℕ → Fin k => i) := measurable_const
  simpa [rowSuccessorProcess] using hsucc.piecewise hpred hconst

@[simp] lemma rowSuccessorAtNthVisit_eq_anchor_of_nthVisitTime_none
    (i : Fin k) (n : ℕ) (ω : ℕ → Fin k)
    (hnone : nthVisitTime (k := k) ω i n = none) :
    rowSuccessorAtNthVisit (k := k) i n ω = i := by
  simp [rowSuccessorAtNthVisit, hnone]

@[simp] lemma rowSuccessorAtNthVisit_eq_successorAt_of_nthVisitTime_some
    (i : Fin k) (n : ℕ) (ω : ℕ → Fin k) (t : ℕ)
    (hsome : nthVisitTime (k := k) ω i n = some t) :
    rowSuccessorAtNthVisit (k := k) i n ω = successorAt (k := k) ω t := by
  simp [rowSuccessorAtNthVisit, hsome]

/-- If an infinite trajectory starts at `i` and belongs to `recurrentEvent`,
then `i` is visited infinitely many times. -/
lemma strongRowRecurrentAt_of_recurrentEvent_start_eq
    (ω : ℕ → Fin k) (i : Fin k)
    (hstart : ω 0 = i)
    (hrec : ω ∈ recurrentEvent (k := k)) :
    strongRowRecurrentAt (k := k) ω i := by
  have hlarge : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ω n = i := by
    intro N
    have hN : ω ∈ ⋃ n ≥ N, returnEvent (k := k) n :=
      Set.mem_iInter.mp hrec N
    rcases Set.mem_iUnion.mp hN with ⟨n, hn⟩
    rcases Set.mem_iUnion.mp hn with ⟨hge, hret⟩
    exact ⟨n, hge, by simpa [returnEvent, hstart] using hret⟩
  by_contra hnotInf
  have hfinite : (visitSet (k := k) ω i).Finite := Set.not_infinite.mp hnotInf
  rcases hfinite.bddAbove with ⟨B, hB⟩
  rcases hlarge (B + 1) with ⟨n, hnge, hni⟩
  have hmem : n ∈ visitSet (k := k) ω i := hni
  have hnle : n ≤ B := hB hmem
  exact (Nat.not_succ_le_self B) (le_trans hnge hnle)

/-- If a path starts at `i` and is recurrent, every `(n+1)`-st return time to `i` exists. -/
lemma nthVisitTimeExists_of_recurrentEvent_start_eq
    (ω : ℕ → Fin k) (i : Fin k) (n : ℕ)
    (hstart : ω 0 = i)
    (hrec : ω ∈ recurrentEvent (k := k)) :
    nthVisitTimeExists (k := k) ω i n := by
  exact nthVisitTimeExists_of_strongRowRecurrentAt (k := k) ω i n
    (strongRowRecurrentAt_of_recurrentEvent_start_eq (k := k) ω i hstart hrec)

/-- Markov exchangeability implies row-successor event invariance on
evidence-equivalent trajectories: both probability and row transition-count
event totals agree. -/
lemma markovExchangeable_rowSuccessor_events_invariant
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    {n : ℕ} (xs ys : Fin (n + 1) → Fin k)
    (he :
      MarkovExchangeability.evidenceOf (α := Fin k) (n := n) xs =
        MarkovExchangeability.evidenceOf (α := Fin k) (n := n) ys)
    (i a : Fin k) :
    μ (List.ofFn xs) = μ (List.ofFn ys) ∧
      MarkovExchangeability.transCount (n := n) xs i a =
        MarkovExchangeability.transCount (n := n) ys i a := by
  refine ⟨hμ n xs ys he, ?_⟩
  simpa [MarkovExchangeability.evidenceOf] using
    congrArg (fun e => e.trans i a) he

lemma rowSuccessorCountVec_eq_of_evidence_eq
    {n : ℕ} (xs ys : Fin (n + 1) → Fin k)
    (he :
      MarkovExchangeability.evidenceOf (α := Fin k) (n := n) xs =
        MarkovExchangeability.evidenceOf (α := Fin k) (n := n) ys)
    (i : Fin k) :
    rowSuccessorCountVec (k := k) xs i = rowSuccessorCountVec (k := k) ys i := by
  funext a
  simpa [rowSuccessorCountVec, MarkovExchangeability.evidenceOf] using
    congrArg (fun e => e.trans i a) he

/-- Dynamic-anchor row recurrence set:
for each trajectory, the anchor is `ω 0`. -/
def strongRowRecurrentAtStartSet : Set (ℕ → Fin k) :=
  {ω | strongRowRecurrentAt (k := k) ω (ω 0)}

lemma recurrentEvent_subset_strongRowRecurrentAtStartSet :
    recurrentEvent (k := k) ⊆ strongRowRecurrentAtStartSet (k := k) := by
  intro ω hrec
  exact strongRowRecurrentAt_of_recurrentEvent_start_eq
    (k := k) (ω := ω) (i := ω 0) rfl hrec

/-- Any recurrent extension measure is almost surely strongly row recurrent at
the dynamic anchor `ω 0`. -/
theorem strongRowRecurrentAtStartSet_of_markovRecurrentPrefixMeasure
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      P (strongRowRecurrentAtStartSet (k := k)) = 1 := by
  rcases hrec with ⟨P, hP, hproj, hrecP⟩
  refine ⟨P, hP, hproj, ?_⟩
  have hmono :
      P (recurrentEvent (k := k)) ≤ P (strongRowRecurrentAtStartSet (k := k)) :=
    measure_mono (recurrentEvent_subset_strongRowRecurrentAtStartSet (k := k))
  have hupper :
      P (strongRowRecurrentAtStartSet (k := k)) ≤ 1 := by
    calc
      P (strongRowRecurrentAtStartSet (k := k)) ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := hP.measure_univ
  have hlower : 1 ≤ P (strongRowRecurrentAtStartSet (k := k)) := by
    calc
      1 = P (recurrentEvent (k := k)) := by simp [hrecP]
      _ ≤ P (strongRowRecurrentAtStartSet (k := k)) := hmono
  exact le_antisymm hupper hlower

/-- Concrete Fortini-row exchangeability placeholder aligned with current
Markov-exchangeability interface. -/
def FortiniRowExchangeableConcrete (μ : FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  MarkovExchangeablePrefixMeasure (k := k) μ

/-- Concrete Fortini strong-row-recurrence placeholder aligned with current
recurrence interface. -/
def FortiniStrongRowRecurrentConcrete (μ : FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  MarkovRecurrentPrefixMeasure (k := k) μ

/-- Abstract Fortini-style package:
row-level hypotheses plus a theorem from those row hypotheses to Markov-mixture
representation, and embeddings from our existing Markov exchangeability/recurrence
assumptions into those row hypotheses. -/
structure FortiniSuccessorMatrixPackage (k : ℕ) where
  RowExchangeable : FiniteAlphabet.PrefixMeasure (Fin k) → Prop
  StrongRowRecurrent : FiniteAlphabet.PrefixMeasure (Fin k) → Prop
  theorem_of_rows :
    ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
      RowExchangeable μ →
      StrongRowRecurrent μ →
        ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
          ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi
  from_markovExchangeable :
    ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
      MarkovExchangeablePrefixMeasure (k := k) μ → RowExchangeable μ
  from_markovRecurrent :
    ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
      MarkovRecurrentPrefixMeasure (k := k) μ → StrongRowRecurrent μ

/-- Build a Fortini package from a single concrete theorem over the current
Markov-exchangeability/recurrence predicates. -/
def fortiniPackage_of_concreteTheorem
    (hTheorem :
      ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
        FortiniRowExchangeableConcrete (k := k) μ →
        FortiniStrongRowRecurrentConcrete (k := k) μ →
          ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
            ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi) :
    FortiniSuccessorMatrixPackage k where
  RowExchangeable := FortiniRowExchangeableConcrete (k := k)
  StrongRowRecurrent := FortiniStrongRowRecurrentConcrete (k := k)
  theorem_of_rows := hTheorem
  from_markovExchangeable := by
    intro μ hμ
    exact hμ
  from_markovRecurrent := by
    intro μ hrec
    exact hrec

/-- Any Fortini-style package yields the anchor-invariance theorem interface. -/
theorem anchorInvariant_of_fortiniPackage
    (pkg : FortiniSuccessorMatrixPackage k) :
    AnchorInvariantSuccessorMatrixTheorem k := by
  intro μ hμ hrec
  exact pkg.theorem_of_rows μ
    (pkg.from_markovExchangeable μ hμ)
    (pkg.from_markovRecurrent μ hrec)

/-- Parallel hard-direction endpoint from a Fortini-style package. -/
theorem markovDeFinetti_hard_of_fortiniPackage
    (pkg : FortiniSuccessorMatrixPackage k)
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi :=
  markovDeFinetti_hard_of_anchorInvariantSuccessorMatrix
    (k := k) (hAnchor := anchorInvariant_of_fortiniPackage (k := k) pkg)
    μ hμ hrec

/-- Convenience endpoint from a concrete Fortini-style theorem statement. -/
theorem markovDeFinetti_hard_of_fortiniConcreteTheorem
    (hTheorem :
      ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
        FortiniRowExchangeableConcrete (k := k) μ →
        FortiniStrongRowRecurrentConcrete (k := k) μ →
          ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
            ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi)
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  exact markovDeFinetti_hard_of_fortiniPackage
    (k := k)
    (pkg := fortiniPackage_of_concreteTheorem (k := k) hTheorem)
    (μ := μ) hμ hrec

end MarkovDeFinettiHard
end Mettapedia.Logic
