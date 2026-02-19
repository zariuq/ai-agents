import Mettapedia.Logic.MarkovDeFinettiAnchorAdapter
import Mathlib.Data.Nat.Nth

/-!
# Markov de Finetti: Fortini-Style Bridge (Active Minimal Surface)

Minimal Fortini-facing abstractions and adapters, with no archive imports.
-/

noncomputable section

namespace Mettapedia.Logic

open MeasureTheory
open scoped BigOperators

namespace MarkovDeFinettiHard

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovExchangeability
open Mettapedia.Logic.MarkovDeFinettiRecurrence

variable {k : ℕ}

def successorAt (ω : ℕ → Fin k) (t : ℕ) : Fin k := ω (t + 1)

def visitSet (ω : ℕ → Fin k) (i : Fin k) : Set ℕ := {t : ℕ | ω t = i}

def visitCountBefore (ω : ℕ → Fin k) (i : Fin k) (t : ℕ) : ℕ :=
  Finset.sum (Finset.range t) (fun s => if ω s = i then (1 : ℕ) else (0 : ℕ))

def isNthVisitTime (ω : ℕ → Fin k) (i : Fin k) (n t : ℕ) : Prop :=
  ω t = i ∧ visitCountBefore (k := k) ω i t = n

def nthVisitTimeExists (ω : ℕ → Fin k) (i : Fin k) (n : ℕ) : Prop :=
  ∃ t : ℕ, isNthVisitTime (k := k) ω i n t

noncomputable def nthVisitTime (ω : ℕ → Fin k) (i : Fin k) (n : ℕ) : Option ℕ :=
  by
    classical
    exact if h : nthVisitTimeExists (k := k) ω i n then some (Nat.find h) else none

noncomputable def rowSuccessorAtNthVisit (i : Fin k) (n : ℕ) (ω : ℕ → Fin k) : Fin k :=
  match nthVisitTime (k := k) ω i n with
  | some t => successorAt (k := k) ω t
  | none => i

noncomputable def rowSuccessorVisitProcess (i : Fin k) (ω : ℕ → Fin k) : ℕ → Fin k :=
  fun n => rowSuccessorAtNthVisit (k := k) i n ω

def strongRowRecurrentAt (ω : ℕ → Fin k) (i : Fin k) : Prop :=
  Set.Infinite (visitSet (k := k) ω i)

@[simp] lemma successorAt_eq (ω : ℕ → Fin k) (t : ℕ) :
    successorAt (k := k) ω t = ω (t + 1) := rfl

/-- Measurable row-successor process at anchor `i` and time index `n`.
At times not visiting `i`, this process returns `i` itself. -/
def rowSuccessorProcess (i : Fin k) (n : ℕ) (ω : ℕ → Fin k) : Fin k :=
  if ω n = i then successorAt (k := k) ω n else i

/-- Finite-cylinder event on row-process trajectories. -/
def rowFiniteCylinder (S : Finset ℕ) (v : ℕ → Fin k) : Set (ℕ → Fin k) :=
  {r | ∀ n ∈ S, r n = v n}

/-- Finite-cylinder event pulled back along the visit-indexed row process. -/
def rowVisitCylinderEvent (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) : Set (ℕ → Fin k) :=
  {ω | ∀ n ∈ S, rowSuccessorAtNthVisit (k := k) i n ω = v n}

/-- Truncated row-visit cylinder event:
all required visit-index constraints are witnessed by times `< N`. -/
def rowVisitCylinderEventUpTo
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) : Set (ℕ → Fin k) :=
  {ω | ∀ n ∈ S, ∃ t : ℕ, t < N ∧
      nthVisitTime (k := k) ω i n = some t ∧ successorAt (k := k) ω t = v n}

/-- Extend a finite prefix trajectory to an infinite path by keeping the first
`N+1` coordinates and then defaulting to the first symbol. -/
def prefixExtend (N : ℕ) (xs : Fin (N + 1) → Fin k) : ℕ → Fin k :=
  fun m =>
    if h : m ≤ N then xs ⟨m, Nat.lt_succ_of_le h⟩ else xs 0

/-- Single-coordinate row-successor value event. -/
def rowSuccessorValueEvent (i : Fin k) (n : ℕ) (a : Fin k) : Set (ℕ → Fin k) :=
  {ω | rowSuccessorAtNthVisit (k := k) i n ω = a}

/-- Time-indexed piece for row-successor value decomposition. -/
def rowSuccessorValueEventAtTime
    (i : Fin k) (n : ℕ) (a : Fin k) (t : ℕ) : Set (ℕ → Fin k) :=
  {ω | nthVisitTime (k := k) ω i n = some t ∧ successorAt (k := k) ω t = a}

/-- Finite-cylinder row event decomposes as finite intersection of single-coordinate
row-successor events. -/
lemma rowVisitCylinderEvent_eq_iInter_rowSuccessorValueEvent
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) :
    rowVisitCylinderEvent (k := k) i S v =
      ⋂ n ∈ S, rowSuccessorValueEvent (k := k) i n (v n) := by
  ext ω
  simp [rowVisitCylinderEvent, rowSuccessorValueEvent]

lemma rowVisitCylinderEventUpTo_eq_iInter_iUnion_time
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) :
    rowVisitCylinderEventUpTo (k := k) i S v N =
      ⋂ n ∈ S, ⋃ t ∈ Finset.range N,
        rowSuccessorValueEventAtTime (k := k) i n (v n) t := by
  ext ω
  simp [rowVisitCylinderEventUpTo, rowSuccessorValueEventAtTime, and_left_comm]

/-- Single-coordinate row-successor event decomposition into `none`-case plus a
countable union over exact visit times. -/
lemma rowSuccessorValueEvent_eq_none_or_iUnion_time
    (i : Fin k) (n : ℕ) (a : Fin k) :
    rowSuccessorValueEvent (k := k) i n a =
      ({ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none ∧ i = a} ∪
        ⋃ t : ℕ, rowSuccessorValueEventAtTime (k := k) i n a t) := by
  ext ω
  constructor
  · intro hω
    by_cases hnone : nthVisitTime (k := k) ω i n = none
    · left
      refine ⟨hnone, ?_⟩
      have hrow : rowSuccessorAtNthVisit (k := k) i n ω = i := by
        simp [rowSuccessorAtNthVisit, hnone]
      have hval : rowSuccessorAtNthVisit (k := k) i n ω = a := hω
      exact hrow.symm.trans hval
    · right
      rcases hsome : nthVisitTime (k := k) ω i n with _ | t
      · contradiction
      · refine Set.mem_iUnion.mpr ⟨t, ?_⟩
        refine ⟨hsome, ?_⟩
        have hrow : rowSuccessorAtNthVisit (k := k) i n ω = successorAt (k := k) ω t := by
          simp [rowSuccessorAtNthVisit, hsome]
        have hval : rowSuccessorAtNthVisit (k := k) i n ω = a := hω
        exact hrow.symm.trans hval
  · intro hω
    rcases hω with hnone | hsome
    · rcases hnone with ⟨hnone, hia⟩
      have : rowSuccessorAtNthVisit (k := k) i n ω = i := by
        simp [rowSuccessorAtNthVisit, hnone]
      simpa [rowSuccessorValueEvent, hia] using this
    · rcases Set.mem_iUnion.mp hsome with ⟨t, ht⟩
      rcases ht with ⟨hvisit, hsucc⟩
      have hrow : rowSuccessorAtNthVisit (k := k) i n ω = successorAt (k := k) ω t := by
        simp [rowSuccessorAtNthVisit, hvisit]
      exact hrow.trans hsucc

/-- Pushforward law of the visit-indexed row process under an extension measure `P`. -/
noncomputable def rowProcessLaw (P : Measure (ℕ → Fin k)) (i : Fin k) : Measure (ℕ → Fin k) :=
  Measure.map (rowSuccessorVisitProcess (k := k) i) P

/-- State-conditioned successor event at time `t`. -/
def successorEventAt (ω : ℕ → Fin k) (i a : Fin k) (t : ℕ) : Prop :=
  ω t = i ∧ successorAt (k := k) ω t = a

/-- Row-successor count vector for a finite trajectory summary. -/
def rowSuccessorCountVec {n : ℕ} (xs : Fin (n + 1) → Fin k) (i : Fin k) : Fin k → ℕ :=
  fun a => MarkovExchangeability.transCount (n := n) xs i a

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
      (measurable_const : Measurable (fun _ : ℕ → Fin k => (0 : ℕ))))

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
    exact (Nat.lt_irrefl n) hcount_lt
  · exact heq
  · exfalso
    rcases ht with ⟨_, ht_count⟩
    rcases hu with ⟨hu_visit, hu_count⟩
    have hcount_lt :
        visitCountBefore (k := k) ω i u < visitCountBefore (k := k) ω i t :=
      visitCountBefore_strict_mono_of_visit (k := k) ω i hu_visit hgt
    rw [ht_count, hu_count] at hcount_lt
    exact (Nat.lt_irrefl n) hcount_lt

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

lemma visitCountBefore_eq_of_prefixEq_upTo
    (ω ω' : ℕ → Fin k) (i : Fin k) {N t : ℕ}
    (ht : t ≤ N)
    (hprefix : ∀ m ≤ N, ω m = ω' m) :
    visitCountBefore (k := k) ω i t = visitCountBefore (k := k) ω' i t := by
  unfold visitCountBefore
  refine Finset.sum_congr rfl ?_
  intro s hs
  have hslt : s < t := Finset.mem_range.mp hs
  have hsleN : s ≤ N := Nat.le_trans (Nat.le_of_lt hslt) ht
  simp [hprefix s hsleN]

lemma isNthVisitTime_iff_of_prefixEq_upTo
    (ω ω' : ℕ → Fin k) (i : Fin k) (n t : ℕ) {N : ℕ}
    (ht : t ≤ N)
    (hprefix : ∀ m ≤ N, ω m = ω' m) :
    isNthVisitTime (k := k) ω i n t ↔ isNthVisitTime (k := k) ω' i n t := by
  constructor
  · intro h
    rcases h with ⟨hvisit, hcount⟩
    refine ⟨?_, ?_⟩
    · calc
        ω' t = ω t := by simpa using (hprefix t ht).symm
        _ = i := hvisit
    · calc
        visitCountBefore (k := k) ω' i t = visitCountBefore (k := k) ω i t := by
          simpa using
            (visitCountBefore_eq_of_prefixEq_upTo (k := k) ω' ω i ht
              (fun m hm => (hprefix m hm).symm))
        _ = n := hcount
  · intro h
    rcases h with ⟨hvisit, hcount⟩
    refine ⟨?_, ?_⟩
    · calc
        ω t = ω' t := by simpa using hprefix t ht
        _ = i := hvisit
    · calc
        visitCountBefore (k := k) ω i t = visitCountBefore (k := k) ω' i t := by
          simpa using visitCountBefore_eq_of_prefixEq_upTo (k := k) ω ω' i ht hprefix
        _ = n := hcount

lemma nthVisitTime_eq_some_iff_of_prefixEq_upTo
    (ω ω' : ℕ → Fin k) (i : Fin k) (n t : ℕ) {N : ℕ}
    (ht : t ≤ N)
    (hprefix : ∀ m ≤ N, ω m = ω' m) :
    nthVisitTime (k := k) ω i n = some t ↔
      nthVisitTime (k := k) ω' i n = some t := by
  rw [nthVisitTime_eq_some_iff (k := k) ω i n t, nthVisitTime_eq_some_iff (k := k) ω' i n t]
  exact isNthVisitTime_iff_of_prefixEq_upTo (k := k) ω ω' i n t ht hprefix

lemma successorAt_eq_of_prefixEq_upTo_lt
    (ω ω' : ℕ → Fin k) {N t : ℕ}
    (ht : t < N)
    (hprefix : ∀ m ≤ N, ω m = ω' m) :
    successorAt (k := k) ω t = successorAt (k := k) ω' t := by
  have ht1 : t + 1 ≤ N := Nat.succ_le_of_lt ht
  calc
    successorAt (k := k) ω t = ω (t + 1) := by rfl
    _ = ω' (t + 1) := hprefix (t + 1) ht1
    _ = successorAt (k := k) ω' t := by rfl

lemma rowVisitCylinderEventUpTo_mem_iff_of_prefixEq
    (ω ω' : ℕ → Fin k) (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ)
    (hprefix : ∀ m ≤ N, ω m = ω' m) :
    ω ∈ rowVisitCylinderEventUpTo (k := k) i S v N ↔
      ω' ∈ rowVisitCylinderEventUpTo (k := k) i S v N := by
  constructor
  · intro h n hnS
    rcases h n hnS with ⟨t, htN, htime, hsucc⟩
    refine ⟨t, htN, ?_, ?_⟩
    · exact (nthVisitTime_eq_some_iff_of_prefixEq_upTo (k := k) ω ω' i n t
        (Nat.le_of_lt htN) hprefix).1 htime
    · calc
        successorAt (k := k) ω' t = successorAt (k := k) ω t := by
          simpa using
            (successorAt_eq_of_prefixEq_upTo_lt (k := k) ω' ω htN
              (fun m hm => (hprefix m hm).symm))
        _ = v n := hsucc
  · intro h n hnS
    rcases h n hnS with ⟨t, htN, htime, hsucc⟩
    refine ⟨t, htN, ?_, ?_⟩
    · exact (nthVisitTime_eq_some_iff_of_prefixEq_upTo (k := k) ω ω' i n t
        (Nat.le_of_lt htN) hprefix).2 htime
    · calc
        successorAt (k := k) ω t = successorAt (k := k) ω' t := by
          exact successorAt_eq_of_prefixEq_upTo_lt (k := k) ω ω' htN hprefix
        _ = v n := hsucc

lemma rowVisitCylinderEventUpTo_congr
    (i : Fin k) {S T : Finset ℕ} {v w : ℕ → Fin k} (N : ℕ)
    (hS : S = T) (hv : ∀ n ∈ S, v n = w n) :
    rowVisitCylinderEventUpTo (k := k) i S v N =
      rowVisitCylinderEventUpTo (k := k) i T w N := by
  subst hS
  ext ω
  constructor
  · intro h n hn
    rcases h n hn with ⟨t, htN, htime, hsucc⟩
    refine ⟨t, htN, htime, ?_⟩
    simpa [hv n hn] using hsucc
  · intro h n hn
    rcases h n hn with ⟨t, htN, htime, hsucc⟩
    refine ⟨t, htN, htime, ?_⟩
    have hv' : w n = v n := (hv n hn).symm
    simpa [hv'] using hsucc

lemma rowVisitCylinderEvent_congr
    (i : Fin k) {S T : Finset ℕ} {v w : ℕ → Fin k}
    (hS : S = T) (hv : ∀ n ∈ S, v n = w n) :
    rowVisitCylinderEvent (k := k) i S v =
      rowVisitCylinderEvent (k := k) i T w := by
  subst hS
  ext ω
  constructor
  · intro h n hn
    simpa [hv n hn] using h n hn
  · intro h n hn
    have hv' : w n = v n := (hv n hn).symm
    simpa [hv'] using h n hn

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

lemma measurableSet_rowSuccessorValueEventAtTime
    (i : Fin k) (n : ℕ) (a : Fin k) (t : ℕ) :
    MeasurableSet (rowSuccessorValueEventAtTime (k := k) i n a t) := by
  have hvisit : MeasurableSet {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = some t} :=
    measurableSet_nthVisitTime_eq_some (k := k) i n t
  have hsucc : MeasurableSet {ω : ℕ → Fin k | successorAt (k := k) ω t = a} :=
    measurableSet_successorAt_eq (k := k) a t
  simpa [rowSuccessorValueEventAtTime, Set.setOf_and] using hvisit.inter hsucc

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
        change rowSuccessorAtNthVisit (k := k) i n ω = a
        have hnt' : nthVisitTime (k := k) ω i n = none := by simpa using hnt
        unfold rowSuccessorAtNthVisit
        rw [hnt']
        simpa using hia
      · rcases Set.mem_iUnion.mp hsome with ⟨t, ht⟩
        rcases ht with ⟨hnt, hsucc⟩
        change rowSuccessorAtNthVisit (k := k) i n ω = a
        have hnt' : nthVisitTime (k := k) ω i n = some t := by simpa using hnt
        unfold rowSuccessorAtNthVisit
        rw [hnt']
        simpa using hsucc
  have hnone : MeasurableSet {ω : ℕ → Fin k | nthVisitTime (k := k) ω i n = none} :=
    measurableSet_nthVisitTime_eq_none (k := k) i n
  have hiEqA : MeasurableSet {ω : ℕ → Fin k | i = a} := by
    by_cases hia : i = a <;> simp [hia]
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

lemma measurableSet_cylinder (xs : List (Fin k)) :
    MeasurableSet (cylinder (k := k) xs) := by
  unfold MarkovDeFinettiRecurrence.cylinder
  refine MeasurableSet.iInter ?_
  intro i
  have hcoord : Measurable (fun ω : ℕ → Fin k => ω i.1) := measurable_pi_apply i.1
  simpa [Set.preimage] using hcoord (MeasurableSet.singleton xs[i.1])

lemma measurableSet_rowVisitCylinderEventUpTo
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) :
    MeasurableSet (rowVisitCylinderEventUpTo (k := k) i S v N) := by
  rw [rowVisitCylinderEventUpTo_eq_iInter_iUnion_time (k := k) i S v N]
  refine Finset.measurableSet_biInter S ?_
  intro n hnS
  refine Finset.measurableSet_biUnion (Finset.range N) ?_
  intro t ht
  exact measurableSet_rowSuccessorValueEventAtTime (k := k) i n (v n) t

lemma preimage_rowFiniteCylinder_eq_rowVisitCylinderEvent
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) :
    (rowSuccessorVisitProcess (k := k) i) ⁻¹' rowFiniteCylinder (k := k) S v =
      rowVisitCylinderEvent (k := k) i S v := by
  ext ω
  rfl

lemma mem_cylinder_of_prefix
    (ω : ℕ → Fin k) (N : ℕ) :
    ω ∈ cylinder (k := k) (List.ofFn (fun j : Fin (N + 1) => ω j)) := by
  refine Set.mem_iInter.mpr ?_
  intro i
  change ω i.1 = (List.ofFn (fun j : Fin (N + 1) => ω j))[i.1]
  let j : Fin (N + 1) := ⟨i.1, by simpa [List.length_ofFn] using i.2⟩
  have hiLt : i.1 < (List.ofFn (fun t : Fin (N + 1) => ω t)).length := by
    simpa [List.length_ofFn] using i.2
  have hget : (List.ofFn (fun t : Fin (N + 1) => ω t))[i.1] = ω j := by
    simpa [j] using
      (List.getElem_ofFn (f := fun t : Fin (N + 1) => ω t) (i := i.1) (h := hiLt))
  simpa [j] using hget.symm

lemma mem_cylinder_ofFn_iff
    (ω : ℕ → Fin k) (N : ℕ) (xs : Fin (N + 1) → Fin k) :
    ω ∈ cylinder (k := k) (List.ofFn xs) ↔
      ∀ j : Fin (N + 1), ω j = xs j := by
  constructor
  · intro hω j
    have hω' :
        ∀ i : Fin (List.ofFn xs).length, ω i.1 = (List.ofFn xs)[i.1] := by
      simpa [MarkovDeFinettiRecurrence.cylinder] using hω
    have hj' : j.1 < (List.ofFn xs).length := by
      simpa [List.length_ofFn] using j.2
    have hmain : ω j.1 = (List.ofFn xs)[j.1] := hω' ⟨j.1, hj'⟩
    have hget : (List.ofFn xs)[j.1] = xs j := by
      simpa [List.length_ofFn] using (List.getElem_ofFn (f := xs) (i := j.1) (h := hj'))
    simpa using hmain.trans hget
  · intro hω
    refine Set.mem_iInter.mpr ?_
    intro i
    let j : Fin (N + 1) := ⟨i.1, by simpa [List.length_ofFn] using i.2⟩
    have hpoint : ω j = xs j := hω j
    have hj' : i.1 < (List.ofFn xs).length := by
      simpa [List.length_ofFn] using i.2
    have hget : (List.ofFn xs)[i.1] = xs j := by
      simpa [j, List.length_ofFn] using
        (List.getElem_ofFn (f := xs) (i := i.1) (h := hj'))
    have : ω i.1 = (List.ofFn xs)[i.1] := by
      calc
        ω i.1 = ω j := by rfl
        _ = xs j := hpoint
        _ = (List.ofFn xs)[i.1] := hget.symm
    simpa using this

lemma eq_prefixExtend_of_mem_cylinder
    (ω : ℕ → Fin k) (N : ℕ) (xs : Fin (N + 1) → Fin k)
    (hω : ω ∈ cylinder (k := k) (List.ofFn xs)) :
    ∀ m ≤ N, ω m = prefixExtend (k := k) N xs m := by
  intro m hm
  have hω' :
      ∀ j : Fin (List.ofFn xs).length, ω j.1 = (List.ofFn xs)[j.1] := by
    simpa [MarkovDeFinettiRecurrence.cylinder] using hω
  have hmval : ω m = xs ⟨m, Nat.lt_succ_of_le hm⟩ := by
    have hm' : m < (List.ofFn xs).length := by
      simpa [List.length_ofFn] using Nat.lt_succ_of_le hm
    have hwm : ω m = (List.ofFn xs)[m] := hω' ⟨m, hm'⟩
    let jm : Fin (N + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
    have hget : (List.ofFn xs)[m] = xs jm := by
      simpa [jm, List.length_ofFn] using (List.getElem_ofFn (f := xs) (i := m) (h := hm'))
    exact hwm.trans hget
  simpa [prefixExtend, hm] using hmval

/-- Prefix trajectories whose `prefixExtend` satisfies a truncated row-visit
cylinder event. -/
noncomputable def rowVisitCylinderEventUpToPrefixCarrier
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) :
    Finset (Fin (N + 1) → Fin k) := by
  classical
  exact (Finset.univ : Finset (Fin (N + 1) → Fin k)).filter
    (fun xs => rowVisitCylinderEventUpTo (k := k) i S v N (prefixExtend (k := k) N xs))

lemma rowVisitCylinderEventUpToPrefixCarrier_congr
    (i : Fin k) {S T : Finset ℕ} {v w : ℕ → Fin k} (N : ℕ)
    (hS : S = T) (hv : ∀ n ∈ S, v n = w n) :
    rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N =
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i T w N := by
  classical
  have hSet :
      rowVisitCylinderEventUpTo (k := k) i S v N =
        rowVisitCylinderEventUpTo (k := k) i T w N :=
    rowVisitCylinderEventUpTo_congr (k := k) i N hS hv
  ext xs
  constructor
  · intro hxs
    have hmem := (Finset.mem_filter.mp hxs).2
    have hmem' :
        rowVisitCylinderEventUpTo (k := k) i T w N (prefixExtend (k := k) N xs) := by
      simpa [hSet] using hmem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ xs, hmem'⟩
  · intro hxs
    have hmem := (Finset.mem_filter.mp hxs).2
    have hmem' :
        rowVisitCylinderEventUpTo (k := k) i S v N (prefixExtend (k := k) N xs) := by
      simpa [hSet] using hmem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ xs, hmem'⟩

lemma rowVisitCylinderEventUpTo_eq_iUnion_cylinder
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) :
    rowVisitCylinderEventUpTo (k := k) i S v N =
      ⋃ xs ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N,
        cylinder (k := k) (List.ofFn xs) := by
  classical
  ext ω
  constructor
  · intro hω
    let xsω : Fin (N + 1) → Fin k := fun j => ω j
    have hcarrier : xsω ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ xsω, ?_⟩
      have hprefix : ∀ m ≤ N, ω m = prefixExtend (k := k) N xsω m := by
        intro m hm
        simp [prefixExtend, hm, xsω]
      exact (rowVisitCylinderEventUpTo_mem_iff_of_prefixEq (k := k)
        ω (prefixExtend (k := k) N xsω) i S v N hprefix).1 hω
    refine Set.mem_iUnion.mpr ⟨xsω, Set.mem_iUnion.mpr ?_⟩
    refine ⟨hcarrier, ?_⟩
    exact mem_cylinder_of_prefix (k := k) ω N
  · intro hω
    rcases Set.mem_iUnion.mp hω with ⟨xs, hω⟩
    rcases Set.mem_iUnion.mp hω with ⟨hxs, hmem⟩
    have hxs' :
        rowVisitCylinderEventUpTo (k := k) i S v N (prefixExtend (k := k) N xs) := by
      simpa [rowVisitCylinderEventUpToPrefixCarrier] using (Finset.mem_filter.mp hxs).2
    have hprefix : ∀ m ≤ N, ω m = prefixExtend (k := k) N xs m :=
      eq_prefixExtend_of_mem_cylinder (k := k) ω N xs hmem
    exact (rowVisitCylinderEventUpTo_mem_iff_of_prefixEq (k := k)
      ω (prefixExtend (k := k) N xs) i S v N hprefix).2 hxs'

lemma pairwiseDisjoint_cylinder_ofFn_on_prefixCarrier
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) :
    ((↑(rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N) :
      Set (Fin (N + 1) → Fin k))).PairwiseDisjoint
      (fun xs => cylinder (k := k) (List.ofFn xs)) := by
  intro xs hxs ys hys hne
  refine Set.disjoint_left.2 ?_
  intro ω hωx hωy
  have hx : ∀ j : Fin (N + 1), ω j = xs j :=
    (mem_cylinder_ofFn_iff (k := k) ω N xs).1 hωx
  have hy : ∀ j : Fin (N + 1), ω j = ys j :=
    (mem_cylinder_ofFn_iff (k := k) ω N ys).1 hωy
  have hEq : xs = ys := by
    funext j
    calc
      xs j = ω j := (hx j).symm
      _ = ys j := hy j
  exact hne hEq

lemma measure_rowVisitCylinderEventUpTo_eq_sum_prefixCylinders
    (P : Measure (ℕ → Fin k)) (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ) :
    P (rowVisitCylinderEventUpTo (k := k) i S v N) =
      Finset.sum (rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N)
        (fun xs => P (cylinder (k := k) (List.ofFn xs))) := by
  rw [rowVisitCylinderEventUpTo_eq_iUnion_cylinder (k := k) i S v N]
  exact measure_biUnion_finset
    (μ := P)
    (s := rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N)
    (f := fun xs => cylinder (k := k) (List.ofFn xs))
    (pairwiseDisjoint_cylinder_ofFn_on_prefixCarrier (k := k) i S v N)
    (fun xs hxs => measurableSet_cylinder (k := k) (List.ofFn xs))

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

theorem nthVisitTimeExists_of_infinite_visits
    (ω : ℕ → Fin k) (i : Fin k) :
    Set.Infinite {t : ℕ | ω t = i} →
      ∀ n : ℕ, nthVisitTimeExists (k := k) ω i n := by
  intro hinf n
  exact nthVisitTimeExists_of_strongRowRecurrentAt (k := k) ω i n (by
    simpa [strongRowRecurrentAt, visitSet] using hinf)

theorem nthVisitTimeExists_start_of_mem_recurrentEvent
    (ω : ℕ → Fin k) :
    ω ∈ recurrentEvent (k := k) →
      ∀ n : ℕ, nthVisitTimeExists (k := k) ω (ω 0) n := by
  intro hrec n
  apply nthVisitTimeExists_of_infinite_visits (k := k) ω (ω 0)
  exact
    (Mettapedia.Logic.MarkovDeFinettiRecurrence.mem_recurrentEvent_iff_infinite_returns_to_start
      (k := k) ω).1 hrec

lemma ae_nthVisitTime_ne_none_of_ae_infinite_visits
    (P : Measure (ℕ → Fin k)) (i : Fin k) (n : ℕ)
    (hinf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none := by
  filter_upwards [hinf] with ω hω
  have hex : nthVisitTimeExists (k := k) ω i n :=
    nthVisitTimeExists_of_infinite_visits (k := k) ω i hω n
  intro hnone
  exact ((nthVisitTime_eq_none_iff (k := k) ω i n).1 hnone) hex

lemma ae_nthVisitTime_ne_none_all_of_ae_infinite_visits
    (P : Measure (ℕ → Fin k)) (i : Fin k)
    (hinf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    ∀ n : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none := by
  intro n
  exact ae_nthVisitTime_ne_none_of_ae_infinite_visits (k := k) P i n hinf

lemma ae_nthVisitTime_ne_none_of_markovRowRecurrentPrefixMeasure
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hrec : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ i : Fin k, ∀ n : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) := by
  rcases MarkovRowRecurrentPrefixMeasure.ae_infinite_visits (k := k) μ hrec with
    ⟨P, hPprob, hrep, hrowInf⟩
  refine ⟨P, hPprob, hrep, ?_⟩
  intro i n
  exact ae_nthVisitTime_ne_none_of_ae_infinite_visits (k := k) P i n (hrowInf i)

lemma ae_nthVisitTime_ne_none_all_of_rowInfiniteVisits
    (P : Measure (ℕ → Fin k))
    (hrowInf : ∀ i : Fin k, ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    ∀ i : Fin k, ∀ n : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none := by
  intro i n
  exact ae_nthVisitTime_ne_none_of_ae_infinite_visits (k := k) P i n (hrowInf i)

/-- Finite-coordinate permutation event equivalence for visit-indexed row cylinders. -/
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

/-- Set-level finite-permutation equality for row visit-cylinder events. -/
lemma rowSuccessorVisit_perm_event_set_eq
    (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ)
    (v : ℕ → Fin k) :
    {ω : ℕ → Fin k | ∀ n ∈ S, rowSuccessorAtNthVisit (k := k) i (σ n) ω = v n} =
      rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m)) := by
  ext ω
  change
    (∀ n ∈ S, rowSuccessorAtNthVisit (k := k) i (σ n) ω = v n) ↔
      (∀ m ∈ S.image σ, rowSuccessorAtNthVisit (k := k) i m ω = v (σ.symm m))
  exact rowSuccessorVisit_perm_event_iff (k := k) i σ S v ω


/-- Row-sequence cylinder set equality under finite permutation of coordinates. -/
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

/-- Lift finite-permutation cylinder equality to row-process pushforward laws. -/
lemma rowProcessLaw_perm_cylinder_apply
    (P : Measure (ℕ → Fin k))
    (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) :
    rowProcessLaw (k := k) P i
      {r : ℕ → Fin k | ∀ n ∈ S, r (σ n) = v n} =
    rowProcessLaw (k := k) P i
      (rowFiniteCylinder (k := k) (S.image σ) (fun m => v (σ.symm m))) := by
  exact congrArg (rowProcessLaw (k := k) P i) (rowFiniteCylinder_perm_set_eq (k := k) σ S v)

/-- Core Fortini bridge target on the trajectory measure `P`: invariance of
row-visit cylinder event probabilities under finite visit-index permutations. -/
def RowVisitCylinderInvariantAt
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ) : Prop :=
  ∀ (S : Finset ℕ) (v : ℕ → Fin k),
    P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) =
      P (rowVisitCylinderEvent (k := k) i S v)

/-- All-anchors/all-permutations row-visit cylinder invariance under `P`. -/
def RowVisitCylinderInvariantAll (P : Measure (ℕ → Fin k)) : Prop :=
  ∀ (i : Fin k) (σ : Equiv.Perm ℕ), RowVisitCylinderInvariantAt (k := k) P i σ

lemma rowVisitCylinderInvariantAt_refl
    (P : Measure (ℕ → Fin k)) (i : Fin k) :
    RowVisitCylinderInvariantAt (k := k) P i (Equiv.refl ℕ) := by
  intro S v
  simp [rowVisitCylinderEvent]

lemma rowVisitCylinderInvariantAt_symm
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (hσ : RowVisitCylinderInvariantAt (k := k) P i σ) :
    RowVisitCylinderInvariantAt (k := k) P i σ.symm := by
  intro S v
  have hS : (S.image σ.symm).image σ = S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
      simpa using hz
    · intro hx
      refine Finset.mem_image.mpr ?_
      refine ⟨σ.symm x, ?_, by simp⟩
      exact Finset.mem_image.mpr ⟨x, hx, by simp⟩
  have hmain :=
    hσ (S.image σ.symm) (fun m => v (σ m))
  have hmain' :
      P (rowVisitCylinderEvent (k := k) i S v) =
        P (rowVisitCylinderEvent (k := k) i (S.image σ.symm) (fun m => v (σ m))) := by
    simpa [hS] using hmain
  exact hmain'.symm

lemma rowVisitCylinderInvariantAt_trans
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ τ : Equiv.Perm ℕ)
    (hσ : RowVisitCylinderInvariantAt (k := k) P i σ)
    (hτ : RowVisitCylinderInvariantAt (k := k) P i τ) :
    RowVisitCylinderInvariantAt (k := k) P i (σ.trans τ) := by
  intro S v
  have hS :
      S.image (σ.trans τ) = (S.image σ).image τ := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, haS, hax⟩
      refine Finset.mem_image.mpr ?_
      refine ⟨σ a, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨a, haS, rfl⟩
      · simpa [Equiv.trans_apply] using hax
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨b, hb, hbx⟩
      rcases Finset.mem_image.mp hb with ⟨a, haS, hab⟩
      refine Finset.mem_image.mpr ?_
      refine ⟨a, haS, ?_⟩
      subst hab
      simpa [Equiv.trans_apply] using hbx
  have hτ' :=
    hτ (S.image σ) (fun m => v (σ.symm m))
  have hv :
      ∀ n ∈ (S.image σ).image τ,
        (fun m => v (σ.symm (τ.symm m))) n = (fun m => v ((σ.trans τ).symm m)) n := by
    intro n hn
    simp [Equiv.symm_trans_apply]
  have hleftSet :
      rowVisitCylinderEvent (k := k) i ((S.image σ).image τ) (fun m => v (σ.symm (τ.symm m))) =
        rowVisitCylinderEvent (k := k) i (S.image (σ.trans τ))
          (fun m => v ((σ.trans τ).symm m)) :=
    rowVisitCylinderEvent_congr (k := k) i hS.symm hv
  have hleftProb :
      P
          (rowVisitCylinderEvent (k := k) i (S.image (σ.trans τ))
            (fun m => v ((σ.trans τ).symm m))) =
        P (rowVisitCylinderEvent (k := k) i ((S.image σ).image τ)
          (fun m => v (σ.symm (τ.symm m)))) := by
    exact (congrArg (fun A => P A) hleftSet).symm
  have hτ'' :
      P
          (rowVisitCylinderEvent (k := k) i (S.image (σ.trans τ))
            (fun m => v ((σ.trans τ).symm m))) =
        P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) := by
    calc
      P
          (rowVisitCylinderEvent (k := k) i (S.image (σ.trans τ))
            (fun m => v ((σ.trans τ).symm m)))
          =
        P (rowVisitCylinderEvent (k := k) i ((S.image σ).image τ)
          (fun m => v (σ.symm (τ.symm m)))) := hleftProb
      _ =
        P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) := hτ'
  calc
    P
        (rowVisitCylinderEvent (k := k) i (S.image (σ.trans τ))
          (fun m => v ((σ.trans τ).symm m)))
        =
      P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) :=
      hτ''
    _ = P (rowVisitCylinderEvent (k := k) i S v) := hσ S v

lemma rowVisitCylinderInvariantAll_refl
    (P : Measure (ℕ → Fin k)) :
    ∀ i : Fin k, RowVisitCylinderInvariantAt (k := k) P i (Equiv.refl ℕ) := by
  intro i
  exact rowVisitCylinderInvariantAt_refl (k := k) P i

lemma rowVisitCylinderInvariantAll_symm
    (P : Measure (ℕ → Fin k))
    (hAll : RowVisitCylinderInvariantAll (k := k) P) :
    ∀ (i : Fin k) (σ : Equiv.Perm ℕ),
      RowVisitCylinderInvariantAt (k := k) P i σ.symm := by
  intro i σ
  exact rowVisitCylinderInvariantAt_symm (k := k) P i σ (hAll i σ)

lemma rowVisitCylinderInvariantAll_trans
    (P : Measure (ℕ → Fin k))
    (hAll : RowVisitCylinderInvariantAll (k := k) P) :
    ∀ (i : Fin k) (σ τ : Equiv.Perm ℕ),
      RowVisitCylinderInvariantAt (k := k) P i (σ.trans τ) := by
  intro i σ τ
  exact rowVisitCylinderInvariantAt_trans (k := k) P i σ τ (hAll i σ) (hAll i τ)

/-- Fixed-`P` row-visit transport assumption:
each row-visit cylinder pair (permuted vs original) can be represented at the
prefix level by two trajectories with equal Markov evidence. -/
def RowVisitCylinderPrefixTransportAt
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ) : Prop :=
  ∀ (S : Finset ℕ) (v : ℕ → Fin k),
    ∃ (N : ℕ) (xsσ xs : Fin (N + 1) → Fin k),
      evidenceOf (n := N) xsσ = evidenceOf (n := N) xs ∧
      P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) =
        P (cylinder (k := k) (List.ofFn xsσ)) ∧
      P (rowVisitCylinderEvent (k := k) i S v) =
        P (cylinder (k := k) (List.ofFn xs))

theorem rowVisitCylinderInvariantAt_of_markovExchangeable_prefixTransport
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (htransport : RowVisitCylinderPrefixTransportAt (k := k) P i σ) :
    RowVisitCylinderInvariantAt (k := k) P i σ := by
  intro S v
  rcases htransport S v with ⟨N, xsσ, xs, heq, hperm, horig⟩
  calc
    P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m)))
        = P (cylinder (k := k) (List.ofFn xsσ)) := hperm
    _ = μ (List.ofFn xsσ) := (hExt (List.ofFn xsσ)).symm
    _ = μ (List.ofFn xs) := hμ N xsσ xs heq
    _ = P (cylinder (k := k) (List.ofFn xs)) := hExt (List.ofFn xs)
    _ = P (rowVisitCylinderEvent (k := k) i S v) := horig.symm

/-- Finite-horizon sum equality from an evidence-preserving bijection between
two finite trajectory sets. -/
lemma sum_prefixProb_eq_of_evidencePreservingEquiv
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    {N : ℕ}
    (A B : Finset (Fin (N + 1) → Fin k))
    (e : A ≃ B)
    (he :
      ∀ xs : A,
        evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    (∑ xs : A, (μ (List.ofFn xs.1) : ENNReal)) =
      (∑ ys : B, (μ (List.ofFn ys.1) : ENNReal)) := by
  simpa using
    (Fintype.sum_equiv
      (e := e)
      (f := fun xs : A => (μ (List.ofFn xs.1) : ENNReal))
      (g := fun ys : B => (μ (List.ofFn ys.1) : ENNReal))
      (by
        intro xs
        exact hμ N xs.1 (e xs).1 (he xs)))

lemma sum_cylinderProb_eq_of_extension_and_evidencePreservingEquiv
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    {N : ℕ}
    (A B : Finset (Fin (N + 1) → Fin k))
    (e : A ≃ B)
    (he :
      ∀ xs : A,
        evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    Finset.sum A (fun xs => P (cylinder (k := k) (List.ofFn xs))) =
      Finset.sum B (fun ys => P (cylinder (k := k) (List.ofFn ys))) := by
  have hA :
      Finset.sum A (fun xs => P (cylinder (k := k) (List.ofFn xs))) =
        (∑ xs : A, (μ (List.ofFn xs.1) : ENNReal)) := by
    have hAattach :
        Finset.sum A (fun xs => P (cylinder (k := k) (List.ofFn xs))) =
          ∑ xs : A, P (cylinder (k := k) (List.ofFn xs.1)) := by
      simpa using (Finset.sum_attach (s := A)
        (f := fun xs => P (cylinder (k := k) (List.ofFn xs)))).symm
    rw [hAattach]
    simp [hExt]
  have hB :
      Finset.sum B (fun ys => P (cylinder (k := k) (List.ofFn ys))) =
        (∑ ys : B, (μ (List.ofFn ys.1) : ENNReal)) := by
    have hBattach :
        Finset.sum B (fun ys => P (cylinder (k := k) (List.ofFn ys))) =
          ∑ ys : B, P (cylinder (k := k) (List.ofFn ys.1)) := by
      simpa using (Finset.sum_attach (s := B)
        (f := fun ys => P (cylinder (k := k) (List.ofFn ys)))).symm
    rw [hBattach]
    simp [hExt]
  rw [hA, hB]
  exact sum_prefixProb_eq_of_evidencePreservingEquiv (k := k) μ hμ A B e he

/-- Fixed-horizon transport witness for a single `(N,S,v)` row-visit cylinder:
both permuted and original truncated events are represented by finite cylinder
sums related by an evidence-preserving equivalence. -/
def RowVisitCylinderPrefixTransportUpToAt
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k) : Prop :=
  ∃ (Aσ A : Finset (Fin (N + 1) → Fin k)) (e : Aσ ≃ A),
    (∀ xs : Aσ, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) ∧
    P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N) =
      Finset.sum Aσ (fun xs => P (cylinder (k := k) (List.ofFn xs))) ∧
    P (rowVisitCylinderEventUpTo (k := k) i S v N) =
      Finset.sum A (fun xs => P (cylinder (k := k) (List.ofFn xs)))

/-- Core finite-horizon combinatorial target:
an evidence-preserving equivalence between the two canonical UpTo prefix carriers. -/
def RowVisitCylinderUpToCarrierEvidenceEquivAt
    (i : Fin k) (σ : Equiv.Perm ℕ) (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k) : Prop :=
  ∃ e :
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i (S.image σ) (fun m => v (σ.symm m)) N ≃
        rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N,
    ∀ xs,
      evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1

lemma rowVisitCylinderUpToCarrierEvidenceEquivAt_of_carrierEq
    (i : Fin k) (σ : Equiv.Perm ℕ) (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hcar :
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i (S.image σ) (fun m => v (σ.symm m)) N =
        rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N) :
    RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v := by
  classical
  refine ⟨
    { toFun := fun xs => ⟨xs.1, by
          have hx : xs.1 ∈
              rowVisitCylinderEventUpToPrefixCarrier (k := k) i (S.image σ)
                (fun m => v (σ.symm m)) N := xs.2
          rw [← hcar]
          exact hx⟩
      , invFun := fun ys => ⟨ys.1, by
          have hy : ys.1 ∈ rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N := ys.2
          rw [hcar]
          exact hy⟩
      , left_inv := ?_
      , right_inv := ?_ }, ?_⟩
  · intro xs
    ext
    rfl
  · intro ys
    ext
    rfl
  · intro xs
    rfl

lemma rowVisitCylinderEventUpTo_empty (i : Fin k) (v : ℕ → Fin k) (N : ℕ) :
    rowVisitCylinderEventUpTo (k := k) i (∅ : Finset ℕ) v N = Set.univ := by
  ext ω
  simp [rowVisitCylinderEventUpTo]

lemma rowVisitCylinderEventUpToPrefixCarrier_empty (i : Fin k) (v : ℕ → Fin k) (N : ℕ) :
    rowVisitCylinderEventUpToPrefixCarrier (k := k) i (∅ : Finset ℕ) v N =
      (Finset.univ : Finset (Fin (N + 1) → Fin k)) := by
  classical
  ext xs
  constructor
  · intro hx
    exact Finset.mem_univ xs
  · intro hx
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_univ xs, ?_⟩
    intro n hn
    have hn' : False := by
      simp at hn
    exact hn'.elim

lemma rowVisitCylinderEventUpToPrefixCarrier_eq_empty_of_nonempty_zero
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k)
    (hS : S.Nonempty) :
    rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v 0 = ∅ := by
  classical
  ext xs
  constructor
  · intro hxs
    rcases hS with ⟨n, hn⟩
    have hmem : rowVisitCylinderEventUpTo (k := k) i S v 0 (prefixExtend (k := k) 0 xs) := by
      simpa [rowVisitCylinderEventUpToPrefixCarrier] using (Finset.mem_filter.mp hxs).2
    rcases hmem n hn with ⟨t, htlt, _, _⟩
    exact (Nat.not_lt_zero t htlt).elim
  · intro h
    simp at h

lemma rowVisitCylinderUpToCarrierEvidenceEquivAt_empty
    (i : Fin k) (σ : Equiv.Perm ℕ) (N : ℕ) (v : ℕ → Fin k) :
    RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N (∅ : Finset ℕ) v := by
  classical
  refine ⟨
    { toFun := fun xs => ⟨xs.1, ?_⟩
      , invFun := fun ys => ⟨ys.1, ?_⟩
      , left_inv := ?_
      , right_inv := ?_ }, ?_⟩
  · simp [Finset.image_empty, rowVisitCylinderEventUpToPrefixCarrier_empty]
  · simp [rowVisitCylinderEventUpToPrefixCarrier_empty]
  · intro xs
    ext
    rfl
  · intro ys
    ext
    rfl
  · intro xs
    rfl

lemma rowVisitCylinderUpToCarrierEvidenceEquivAt_refl
    (i : Fin k) (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k) :
    RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i (Equiv.refl ℕ) N S v := by
  classical
  refine ⟨
    { toFun := fun xs => ⟨xs.1, ?_⟩
      , invFun := fun ys => ⟨ys.1, ?_⟩
      , left_inv := ?_
      , right_inv := ?_ }, ?_⟩
  · simpa [Finset.image_id] using xs.2
  · simp [Finset.image_id]
  · intro xs
    ext
    rfl
  · intro ys
    ext
    rfl
  · intro xs
    rfl

lemma rowVisitCylinderUpToCarrierEvidenceEquivAt_of_fixed
    (i : Fin k) (σ : Equiv.Perm ℕ) (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hS : S.image σ = S)
    (hv : ∀ n ∈ S, v (σ.symm n) = v n) :
    RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v := by
  have hv' : ∀ n ∈ S.image σ, (fun m => v (σ.symm m)) n = v n := by
    intro n hn
    have hn' : n ∈ S := by
      simpa [hS] using hn
    simpa using hv n hn'
  -- Use the permutation-level carrier equality (no need for fixing assumptions).
  have hcar :
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i (S.image σ) (fun m => v (σ.symm m)) N =
        rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N :=
    rowVisitCylinderEventUpToPrefixCarrier_congr (k := k) i N hS hv'
  exact rowVisitCylinderUpToCarrierEvidenceEquivAt_of_carrierEq
    (k := k) i σ N S v hcar

/-- Fixed-horizon constructor when `σ` fixes `S` pointwise. -/
lemma rowVisitCylinderUpToCarrierEvidenceEquivAt_of_fixing
    (i : Fin k) (σ : Equiv.Perm ℕ) (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hfix : ∀ n ∈ S, σ n = n) :
    RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v := by
  have hS : S.image σ = S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      rw [hfix y hy]
      exact hy
    · intro hx
      refine Finset.mem_image.mpr ?_
      exact ⟨x, hx, hfix x hx⟩
  have hv : ∀ n ∈ S, v (σ.symm n) = v n := by
    intro n hn
    have hsymm : σ.symm n = n := by
      have h := congrArg σ.symm (hfix n hn)
      have h' : n = σ.symm n := by
        simpa using h
      exact h'.symm
    simp [hsymm]
  exact rowVisitCylinderUpToCarrierEvidenceEquivAt_of_fixed
    (k := k) i σ N S v hS hv

/-- Fixed-data family constructor:
if `σ` stabilizes `S` and `v` is compatible on `S`, then we get a carrier
evidence equivalence witness for every finite horizon `N`. -/
theorem rowVisitCylinderUpToCarrierEvidenceEquivAt_family_of_fixed
    (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hS : S.image σ = S)
    (hv : ∀ n ∈ S, v (σ.symm n) = v n) :
    ∀ N : ℕ, RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v := by
  intro N
  exact rowVisitCylinderUpToCarrierEvidenceEquivAt_of_fixed
    (k := k) i σ N S v hS hv

/-- Fixed-data family constructor when `v` is constant on `S`. -/
theorem rowVisitCylinderUpToCarrierEvidenceEquivAt_family_of_fixed_constOn
    (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (a : Fin k)
    (hS : S.image σ = S)
    (hv : ∀ n ∈ S, v n = a) :
    ∀ N : ℕ, RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v := by
  have hv' : ∀ n ∈ S, v (σ.symm n) = v n := by
    intro n hn
    have hnimg : n ∈ S.image σ := by
      simp [hS, hn]
    rcases Finset.mem_image.mp hnimg with ⟨m, hm, hσ⟩
    have hsymm : σ.symm n = m := by
      apply σ.injective
      calc
        σ (σ.symm n) = n := by simp
        _ = σ m := by simp [hσ]
    have hmem : σ.symm n ∈ S := by
      simp [hsymm, hm]
    have hvsymm : v (σ.symm n) = a := hv _ hmem
    have hvn : v n = a := hv _ hn
    exact hvsymm.trans hvn.symm
  intro N
  exact rowVisitCylinderUpToCarrierEvidenceEquivAt_of_fixed
    (k := k) i σ N S v hS hv'

/-- Pointwise-fixing family constructor: `σ` fixes `S` pointwise. -/
theorem rowVisitCylinderUpToCarrierEvidenceEquivAt_family_of_fixing
    (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hfix : ∀ n ∈ S, σ n = n) :
    ∀ N : ℕ, RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v := by
  intro N
  exact rowVisitCylinderUpToCarrierEvidenceEquivAt_of_fixing
    (k := k) i σ N S v hfix

/-- Non-fixed all-horizon constructor on the identity permutation:
no stabilization assumptions on `S` or compatibility assumptions on `v` are needed. -/
theorem rowVisitCylinderUpToCarrierEvidenceEquivAt_family_refl
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) :
    ∀ N : ℕ, RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i (Equiv.refl ℕ) N S v := by
  intro N
  exact rowVisitCylinderUpToCarrierEvidenceEquivAt_refl (k := k) i N S v

lemma image_swap_pair (a b : ℕ) :
    (({a, b} : Finset ℕ).image (Equiv.swap a b)) = ({a, b} : Finset ℕ) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    simp at hy
    rcases hy with rfl | rfl <;> simp
  · intro hx
    simp at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_image.mpr ⟨b, by simp, by simp⟩
    · exact Finset.mem_image.mpr ⟨a, by simp, by simp⟩

/-- Image of a finset under a swap when both swapped points belong to the set. -/
lemma image_swap_of_mem (a b : ℕ) (S : Finset ℕ) (ha : a ∈ S) (hb : b ∈ S) :
    S.image (Equiv.swap a b) = S := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    by_cases hya : y = a
    · subst hya
      simpa using hb
    by_cases hyb : y = b
    · subst hyb
      simpa using ha
    have hswap : Equiv.swap a b y = y :=
      Equiv.swap_apply_of_ne_of_ne hya hyb
    simpa [hswap] using hy
  · intro hx
    by_cases hxa : x = a
    · subst hxa
      exact Finset.mem_image.mpr ⟨b, hb, by simp⟩
    by_cases hxb : x = b
    · subst hxb
      exact Finset.mem_image.mpr ⟨a, ha, by simp⟩
    have hswap : Equiv.swap a b x = x :=
      Equiv.swap_apply_of_ne_of_ne hxa hxb
    exact Finset.mem_image.mpr ⟨x, hx, by simp [hswap]⟩

/-- Non-fixed all-horizon constructor for the two-point swap orbit:
for `S = {a,b}`, compatibility is exactly `v a = v b`. -/
theorem rowVisitCylinderUpToCarrierEvidenceEquivAt_family_swap_pair_of_eq
    (i : Fin k) (a b : ℕ) (v : ℕ → Fin k)
    (hvb : v a = v b) :
    ∀ N : ℕ,
      RowVisitCylinderUpToCarrierEvidenceEquivAt
        (k := k) i (Equiv.swap a b) N ({a, b} : Finset ℕ) v := by
  refine rowVisitCylinderUpToCarrierEvidenceEquivAt_family_of_fixed
    (k := k) i (Equiv.swap a b) ({a, b} : Finset ℕ) v ?_ ?_
  · simpa using image_swap_pair (a := a) (b := b)
  · intro n hn
    simp at hn
    rcases hn with rfl | rfl
    · simp [hvb]
    · simp [hvb]

/-- Swap-family constructor when both swapped indices lie in `S`
and the values agree at those indices. -/
theorem rowVisitCylinderUpToCarrierEvidenceEquivAt_family_swap_of_mem
    (i : Fin k) (a b : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (ha : a ∈ S) (hb : b ∈ S) (hvb : v a = v b) :
    ∀ N : ℕ,
      RowVisitCylinderUpToCarrierEvidenceEquivAt
        (k := k) i (Equiv.swap a b) N S v := by
  have hS : S.image (Equiv.swap a b) = S :=
    image_swap_of_mem (a := a) (b := b) S ha hb
  have hsymm : (Equiv.swap a b).symm = (Equiv.swap a b) := by
    ext n
    simp
  have hv : ∀ n ∈ S, v ((Equiv.swap a b).symm n) = v n := by
    intro n hn
    have hna : n = a ∨ n = b ∨ (n ≠ a ∧ n ≠ b) := by
      by_cases hna : n = a
      · exact Or.inl hna
      by_cases hnb : n = b
      · exact Or.inr (Or.inl hnb)
      exact Or.inr (Or.inr ⟨hna, hnb⟩)
    rcases hna with hna | hnb | hne
    · subst hna
      simp [hsymm, hvb]
    · subst hnb
      simp [hsymm, hvb]
    · rcases hne with ⟨hna, hnb⟩
      have hswap : Equiv.swap a b n = n :=
        Equiv.swap_apply_of_ne_of_ne hna hnb
      simp [hsymm, hswap]
  intro N
  exact rowVisitCylinderUpToCarrierEvidenceEquivAt_of_fixed
    (k := k) i (Equiv.swap a b) N S v hS hv

/-- Adjacent swap inside a contiguous range: `a` and `a+1` lie in `range (m+1)`. -/
theorem rowVisitCylinderUpToCarrierEvidenceEquivAt_family_adjacent_swap_range_of_eq
    (i : Fin k) (m a : ℕ) (v : ℕ → Fin k)
    (ha : a + 1 < m + 1) (hvb : v a = v (a + 1)) :
    ∀ N : ℕ,
      RowVisitCylinderUpToCarrierEvidenceEquivAt
        (k := k) i (Equiv.swap a (a + 1)) N (Finset.range (m + 1)) v := by
  have haS : a ∈ Finset.range (m + 1) := by
    apply Finset.mem_range.mpr
    have : a < a + 1 := Nat.lt_succ_self a
    exact lt_trans this ha
  have hbS : a + 1 ∈ Finset.range (m + 1) := by
    exact Finset.mem_range.mpr ha
  intro N
  exact rowVisitCylinderUpToCarrierEvidenceEquivAt_family_swap_of_mem
    (k := k) i a (a + 1) (Finset.range (m + 1)) v haS hbS hvb N

/-- Two disjoint adjacent swaps inside a contiguous range. -/
theorem rowVisitCylinderUpToCarrierEvidenceEquivAt_family_two_adjacent_swaps_range_of_eq
    (i : Fin k) (m a b : ℕ) (v : ℕ → Fin k)
    (ha : a + 1 < m + 1) (hb : b + 1 < m + 1)
    (hsep : a + 1 < b)
    (hva : v a = v (a + 1)) (hvb : v b = v (b + 1)) :
    ∀ N : ℕ,
      RowVisitCylinderUpToCarrierEvidenceEquivAt
        (k := k) i
          ((Equiv.swap a (a + 1)).trans (Equiv.swap b (b + 1)))
          N (Finset.range (m + 1)) v := by
  have haS : a ∈ Finset.range (m + 1) := by
    apply Finset.mem_range.mpr
    have : a < a + 1 := Nat.lt_succ_self a
    exact lt_trans this ha
  have ha1S : a + 1 ∈ Finset.range (m + 1) := by
    exact Finset.mem_range.mpr ha
  have hbS : b ∈ Finset.range (m + 1) := by
    apply Finset.mem_range.mpr
    have : b < b + 1 := Nat.lt_succ_self b
    exact lt_trans this hb
  have hb1S : b + 1 ∈ Finset.range (m + 1) := by
    exact Finset.mem_range.mpr hb
  have hσ :
      ∀ N : ℕ,
        RowVisitCylinderUpToCarrierEvidenceEquivAt
          (k := k) i (Equiv.swap a (a + 1)) N (Finset.range (m + 1)) v :=
    rowVisitCylinderUpToCarrierEvidenceEquivAt_family_adjacent_swap_range_of_eq
      (k := k) i m a v ha hva
  have hSσ : (Finset.range (m + 1)).image (Equiv.swap a (a + 1)) =
      Finset.range (m + 1) :=
    image_swap_of_mem (a := a) (b := a + 1) (Finset.range (m + 1)) haS ha1S
  let v' : ℕ → Fin k := fun n => v ((Equiv.swap a (a + 1)).symm n)
  have hvb' : v' b = v' (b + 1) := by
    have hne_ba : b ≠ a := ne_of_gt hsep
    have hne_ba1 : b ≠ a + 1 := ne_of_gt hsep
    have hne_b1a : b + 1 ≠ a := by
      have : a < b + 1 := lt_trans hsep (Nat.lt_succ_self b)
      exact ne_of_gt this
    have hne_b1a1 : b + 1 ≠ a + 1 := by
      exact ne_of_gt (Nat.lt_succ_of_lt hsep)
    have hswap_b :
        (Equiv.swap a (a + 1)).symm b = b := by
      have hswap : Equiv.swap a (a + 1) b = b :=
        Equiv.swap_apply_of_ne_of_ne hne_ba hne_ba1
      simpa using hswap
    have hswap_b1 :
        (Equiv.swap a (a + 1)).symm (b + 1) = b + 1 := by
      have hswap : Equiv.swap a (a + 1) (b + 1) = b + 1 :=
        Equiv.swap_apply_of_ne_of_ne hne_b1a hne_b1a1
      simpa using hswap
    simp [v', hswap_b, hswap_b1, hvb]
  have hτ :
      ∀ N : ℕ,
        RowVisitCylinderUpToCarrierEvidenceEquivAt
          (k := k) i (Equiv.swap b (b + 1)) N
            ((Finset.range (m + 1)).image (Equiv.swap a (a + 1))) v' := by
    intro N
    have hτ' :
        RowVisitCylinderUpToCarrierEvidenceEquivAt
          (k := k) i (Equiv.swap b (b + 1)) N (Finset.range (m + 1)) v' :=
      rowVisitCylinderUpToCarrierEvidenceEquivAt_family_adjacent_swap_range_of_eq
        (k := k) i m b v' hb hvb' N
    simpa [hSσ] using hτ'
  intro N
  exact rowVisitCylinderUpToCarrierEvidenceEquivAt_trans
    (k := k) i (Equiv.swap a (a + 1)) (Equiv.swap b (b + 1))
    N (Finset.range (m + 1)) v (hσ N) (hτ N)

lemma image_swap_swap_triple_of_ne
    (a b c : ℕ) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (({a, b, c} : Finset ℕ).image ((Equiv.swap a b).trans (Equiv.swap b c))) =
      ({a, b, c} : Finset ℕ) := by
  classical
  have hswap_ab_a : Equiv.swap a b a = b := by
    simp
  have hswap_ab_b : Equiv.swap a b b = a := by
    simp
  have hswap_ab_c : Equiv.swap a b c = c := by
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · simpa [ne_comm] using hac
    · simpa [ne_comm] using hbc
  have hswap_bc_a : Equiv.swap b c a = a := by
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · simpa [ne_comm] using hab
    · simpa [ne_comm] using hac
  have hswap_bc_b : Equiv.swap b c b = c := by
    simp
  have hswap_bc_c : Equiv.swap b c c = b := by
    simp
  have hσa :
      (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)) a = c := by
    simp [Equiv.trans_apply, hswap_ab_a, hswap_bc_b]
  have hσb :
      (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)) b = a := by
    simp [Equiv.trans_apply, hswap_ab_b, hswap_bc_a]
  have hσc :
      (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)) c = b := by
    simp [Equiv.trans_apply, hswap_ab_c, hswap_bc_c]
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    have hy' : y = a ∨ y = b ∨ y = c := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hy
    rcases hy' with rfl | rfl | rfl
    · -- σ a = c
      simp [Finset.mem_insert, Finset.mem_singleton, hσa]
    · -- σ b = a
      simp [Finset.mem_insert, Finset.mem_singleton, hσb]
    · -- σ c = b
      simp [Finset.mem_insert, Finset.mem_singleton, hσc]
  · intro hx
    have hx' : x = a ∨ x = b ∨ x = c := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hx
    rcases hx' with rfl | rfl | rfl
    · -- pick y = b so σ b = a
      exact Finset.mem_image.mpr ⟨b, by simp, by simp [hσb]⟩
    · -- pick y = c so σ c = b
      exact Finset.mem_image.mpr ⟨c, by simp, by simp [hσc]⟩
    · -- pick y = a so σ a = c
      exact Finset.mem_image.mpr ⟨a, by simp, by simp [hσa]⟩

/-- Non-fixed all-horizon constructor for a 3-cycle orbit:
for `S = {a,b,c}`, compatibility is `v a = v b = v c`. -/
theorem rowVisitCylinderUpToCarrierEvidenceEquivAt_family_cycle3_of_eq
    (i : Fin k) (a b c : ℕ) (v : ℕ → Fin k)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hvb : v a = v b) (hvc : v b = v c) :
    ∀ N : ℕ,
      RowVisitCylinderUpToCarrierEvidenceEquivAt
        (k := k) i ((Equiv.swap a b).trans (Equiv.swap b c)) N ({a, b, c} : Finset ℕ) v := by
  refine rowVisitCylinderUpToCarrierEvidenceEquivAt_family_of_fixed
    (k := k) i ((Equiv.swap a b).trans (Equiv.swap b c)) ({a, b, c} : Finset ℕ) v ?_ ?_
  · simpa using image_swap_swap_triple_of_ne (a := a) (b := b) (c := c) hab hbc hac
  · have hswap_ab_a : Equiv.swap a b a = b := by
      simp
    have hswap_ab_b : Equiv.swap a b b = a := by
      simp
    have hswap_ab_c : Equiv.swap a b c = c := by
      refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
      · simpa [ne_comm] using hac
      · simpa [ne_comm] using hbc
    have hswap_bc_a : Equiv.swap b c a = a := by
      refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
      · simpa [ne_comm] using hab
      · simpa [ne_comm] using hac
    have hswap_bc_b : Equiv.swap b c b = c := by
      simp
    have hswap_bc_c : Equiv.swap b c c = b := by
      simp
    have hσa :
        (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)) a = c := by
      simp [Equiv.trans_apply, hswap_ab_a, hswap_bc_b]
    have hσb :
        (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)) b = a := by
      simp [Equiv.trans_apply, hswap_ab_b, hswap_bc_a]
    have hσc :
        (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)) c = b := by
      simp [Equiv.trans_apply, hswap_ab_c, hswap_bc_c]
    have hsymm_a :
        ((Equiv.trans (Equiv.swap a b) (Equiv.swap b c))).symm a = b := by
      apply (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)).injective
      calc
        (Equiv.trans (Equiv.swap a b) (Equiv.swap b c))
            ((Equiv.trans (Equiv.swap a b) (Equiv.swap b c)).symm a) = a :=
          (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)).apply_symm_apply a
        _ = (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)) b := by
          simp [hσb]
    have hsymm_b :
        ((Equiv.trans (Equiv.swap a b) (Equiv.swap b c))).symm b = c := by
      apply (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)).injective
      calc
        (Equiv.trans (Equiv.swap a b) (Equiv.swap b c))
            ((Equiv.trans (Equiv.swap a b) (Equiv.swap b c)).symm b) = b :=
          (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)).apply_symm_apply b
        _ = (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)) c := by
          simp [hσc]
    have hsymm_c :
        ((Equiv.trans (Equiv.swap a b) (Equiv.swap b c))).symm c = a := by
      apply (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)).injective
      calc
        (Equiv.trans (Equiv.swap a b) (Equiv.swap b c))
            ((Equiv.trans (Equiv.swap a b) (Equiv.swap b c)).symm c) = c :=
          (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)).apply_symm_apply c
        _ = (Equiv.trans (Equiv.swap a b) (Equiv.swap b c)) a := by
          simp [hσa]
    intro n hn
    have hn' : n = a ∨ n = b ∨ n = c := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hn
    rcases hn' with hna | hnb | hnc
    · subst n
      -- σ.symm a = b
      calc
        v ((Equiv.trans (Equiv.swap a b) (Equiv.swap b c)).symm a) = v b := by
          simp [hsymm_a]
        _ = v a := hvb.symm
    · subst n
      -- σ.symm b = c
      calc
        v ((Equiv.trans (Equiv.swap a b) (Equiv.swap b c)).symm b) = v c := by
          simp [hsymm_b]
        _ = v b := hvc.symm
    · subst n
      -- σ.symm c = a
      have hfac : v a = v b := hvb
      have hfac' : v a = v c := hfac.trans hvc
      calc
        v ((Equiv.trans (Equiv.swap a b) (Equiv.swap b c)).symm c) = v a := by
          simp [hsymm_c]
        _ = v c := hfac'

/-- Non-fixed finite-horizon constructor:
at horizon `N = 0`, any nonempty index set yields empty carriers on both sides,
so the carrier evidence equivalence holds without fixed-set assumptions. -/
theorem rowVisitCylinderUpToCarrierEvidenceEquivAt_zero_of_nonempty
    (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hS : S.Nonempty) :
    RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ 0 S v := by
  have hSimg : (S.image σ).Nonempty := by
    rcases hS with ⟨n, hn⟩
    exact ⟨σ n, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩
  have hleft :
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i (S.image σ) (fun m => v (σ.symm m)) 0 = ∅ :=
    rowVisitCylinderEventUpToPrefixCarrier_eq_empty_of_nonempty_zero
      (k := k) i (S.image σ) (fun m => v (σ.symm m)) hSimg
  have hright :
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v 0 = ∅ :=
    rowVisitCylinderEventUpToPrefixCarrier_eq_empty_of_nonempty_zero
      (k := k) i S v hS
  exact rowVisitCylinderUpToCarrierEvidenceEquivAt_of_carrierEq
    (k := k) i σ 0 S v (by rw [hleft, hright])

lemma rowVisitCylinderUpToCarrierEvidenceEquivAt_trans
    (i : Fin k) (σ τ : Equiv.Perm ℕ) (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hσ :
      RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hτ :
      RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i τ N (S.image σ)
        (fun m => v (σ.symm m))) :
    RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i (σ.trans τ) N S v := by
  classical
  rcases hσ with ⟨eσ, heσ⟩
  rcases hτ with ⟨eτ, heτ⟩
  -- Align the domain carrier for the composed permutation.
  have hS :
      S.image (σ.trans τ) = (S.image σ).image τ := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, haS, hax⟩
      refine Finset.mem_image.mpr ?_
      refine ⟨σ a, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨a, haS, rfl⟩
      · simpa [Equiv.trans_apply] using hax
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨b, hb, hbx⟩
      rcases Finset.mem_image.mp hb with ⟨a, haS, hab⟩
      refine Finset.mem_image.mpr ?_
      refine ⟨a, haS, ?_⟩
      subst hab
      simpa [Equiv.trans_apply] using hbx
  have hv :
      ∀ n ∈ S.image (σ.trans τ),
        v ((σ.trans τ).symm n) = v (σ.symm (τ.symm n)) := by
    intro n hn
    simp [Equiv.symm_trans_apply]
  have hcar :
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i (S.image (σ.trans τ))
        (fun m => v ((σ.trans τ).symm m)) N =
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i ((S.image σ).image τ)
        (fun m => v (σ.symm (τ.symm m))) N :=
    rowVisitCylinderEventUpToPrefixCarrier_congr (k := k) i N hS hv
  -- Compose the equivalences, transporting membership across `hcar`.
  refine ⟨
    { toFun := fun xs => eσ (eτ ⟨xs.1, by
        have hx : xs.1 ∈
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i (S.image (σ.trans τ))
              (fun m => v ((σ.trans τ).symm m)) N := xs.2
        -- move membership to the carrier for `(S.image σ).image τ`
        -- use `rw` to avoid simp rewriting to `True`
        simpa using (by
          -- goal: xs.1 ∈ rowVisitCylinderEventUpToPrefixCarrier ... ((S.image σ).image τ) ...
          -- rewrite the goal to the original carrier
          rw [← hcar]
          exact hx)⟩)
      , invFun := fun ys => ⟨(eτ.symm (eσ.symm ys)).1, by
          have hy :
              (eτ.symm (eσ.symm ys)).1 ∈
                rowVisitCylinderEventUpToPrefixCarrier (k := k) i ((S.image σ).image τ)
                  (fun m => v (σ.symm (τ.symm m))) N :=
            (eτ.symm (eσ.symm ys)).2
          -- move membership back along `hcar`, then rewrite the symmetric form
          have hyA :
              (eτ.symm (eσ.symm ys)).1 ∈
                rowVisitCylinderEventUpToPrefixCarrier (k := k) i (S.image (σ.trans τ))
                  (fun m => v ((σ.trans τ).symm m)) N := by
            rw [hcar]
            exact hy
          simpa [Equiv.symm_trans_apply] using hyA⟩
      , left_inv := ?_
      , right_inv := ?_ }, ?_⟩
  · intro xs
    ext
    simp
  · intro ys
    ext
    simp
  · intro xs
    -- evidence preservation by composition
    have hτ' := heτ ⟨xs.1, by
      have hx : xs.1 ∈
          rowVisitCylinderEventUpToPrefixCarrier (k := k) i (S.image (σ.trans τ))
            (fun m => v ((σ.trans τ).symm m)) N := xs.2
      simpa using (by
        rw [← hcar]
        exact hx)⟩
    have hσ' := heσ (eτ ⟨xs.1, by
      have hx : xs.1 ∈
          rowVisitCylinderEventUpToPrefixCarrier (k := k) i (S.image (σ.trans τ))
            (fun m => v ((σ.trans τ).symm m)) N := xs.2
      simpa using (by
        rw [← hcar]
        exact hx)⟩)
    exact hτ'.trans hσ'

lemma rowVisitCylinderUpToCarrierEvidenceEquivAt_family_trans
    (i : Fin k) (σ τ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hσ :
      ∀ N : ℕ, RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hτ :
      ∀ N : ℕ, RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i τ N (S.image σ)
        (fun m => v (σ.symm m))) :
    ∀ N : ℕ, RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i (σ.trans τ) N S v := by
  intro N
  exact rowVisitCylinderUpToCarrierEvidenceEquivAt_trans
    (k := k) i σ τ N S v (hσ N) (hτ N)

lemma rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hcar :
      RowVisitCylinderUpToCarrierEvidenceEquivAt
        (k := k) i σ N S v) :
    RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v := by
  rcases hcar with ⟨e, he⟩
  refine ⟨
    rowVisitCylinderEventUpToPrefixCarrier (k := k) i (S.image σ) (fun m => v (σ.symm m)) N,
    rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N,
    e, he, ?_, ?_⟩
  · exact measure_rowVisitCylinderEventUpTo_eq_sum_prefixCylinders
      (k := k) P i (S.image σ) (fun m => v (σ.symm m)) N
  · exact measure_rowVisitCylinderEventUpTo_eq_sum_prefixCylinders
      (k := k) P i S v N

/-- Constructor form: build a fixed-horizon transport witness directly from an
explicit evidence-preserving carrier equivalence for `(i,σ,S,v,N)`. -/
theorem rowVisitCylinderPrefixTransportUpToAt_constructor
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (e :
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i (S.image σ) (fun m => v (σ.symm m)) N ≃
        rowVisitCylinderEventUpToPrefixCarrier (k := k) i S v N)
    (he : ∀ xs, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1) :
    RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v := by
  exact rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
    (k := k) P i σ N S v ⟨e, he⟩

/-- Transport family for a 2-point swap when the values agree. -/
theorem rowVisitCylinderPrefixTransportUpToAt_family_swap_pair_of_eq
    (P : Measure (ℕ → Fin k)) (i : Fin k) (a b : ℕ) (v : ℕ → Fin k)
    (hvb : v a = v b) :
    ∀ N : ℕ,
      RowVisitCylinderPrefixTransportUpToAt
        (k := k) P i (Equiv.swap a b) N ({a, b} : Finset ℕ) v := by
  intro N
  exact rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
    (k := k) P i (Equiv.swap a b) N ({a, b} : Finset ℕ) v
    (rowVisitCylinderUpToCarrierEvidenceEquivAt_family_swap_pair_of_eq
      (k := k) i a b v hvb N)

/-- Transport family for a 3-cycle when the values agree. -/
theorem rowVisitCylinderPrefixTransportUpToAt_family_cycle3_of_eq
    (P : Measure (ℕ → Fin k)) (i : Fin k) (a b c : ℕ) (v : ℕ → Fin k)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hvb : v a = v b) (hvc : v b = v c) :
    ∀ N : ℕ,
      RowVisitCylinderPrefixTransportUpToAt
        (k := k) P i ((Equiv.swap a b).trans (Equiv.swap b c)) N ({a, b, c} : Finset ℕ) v := by
  intro N
  exact rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
    (k := k) P i ((Equiv.swap a b).trans (Equiv.swap b c)) N ({a, b, c} : Finset ℕ) v
    (rowVisitCylinderUpToCarrierEvidenceEquivAt_family_cycle3_of_eq
      (k := k) i a b c v hab hbc hac hvb hvc N)

/-- Transport family for a swap within a finite set when the swapped values agree. -/
theorem rowVisitCylinderPrefixTransportUpToAt_family_swap_of_mem
    (P : Measure (ℕ → Fin k)) (i : Fin k) (a b : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (ha : a ∈ S) (hb : b ∈ S) (hvb : v a = v b) :
    ∀ N : ℕ,
      RowVisitCylinderPrefixTransportUpToAt
        (k := k) P i (Equiv.swap a b) N S v := by
  intro N
  exact rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
    (k := k) P i (Equiv.swap a b) N S v
    (rowVisitCylinderUpToCarrierEvidenceEquivAt_family_swap_of_mem
      (k := k) i a b S v ha hb hvb N)

/-- Adjacent swap inside a contiguous range: transport family form. -/
theorem rowVisitCylinderPrefixTransportUpToAt_family_adjacent_swap_range_of_eq
    (P : Measure (ℕ → Fin k)) (i : Fin k) (m a : ℕ) (v : ℕ → Fin k)
    (ha : a + 1 < m + 1) (hvb : v a = v (a + 1)) :
    ∀ N : ℕ,
      RowVisitCylinderPrefixTransportUpToAt
        (k := k) P i (Equiv.swap a (a + 1)) N (Finset.range (m + 1)) v := by
  have haS : a ∈ Finset.range (m + 1) := by
    apply Finset.mem_range.mpr
    have : a < a + 1 := Nat.lt_succ_self a
    exact lt_trans this ha
  have hbS : a + 1 ∈ Finset.range (m + 1) := by
    exact Finset.mem_range.mpr ha
  intro N
  exact rowVisitCylinderPrefixTransportUpToAt_family_swap_of_mem
    (k := k) P i a (a + 1) (Finset.range (m + 1)) v haS hbS hvb N

/-- Transport family for two disjoint adjacent swaps inside a contiguous range. -/
theorem rowVisitCylinderPrefixTransportUpToAt_family_two_adjacent_swaps_range_of_eq
    (P : Measure (ℕ → Fin k)) (i : Fin k) (m a b : ℕ) (v : ℕ → Fin k)
    (ha : a + 1 < m + 1) (hb : b + 1 < m + 1)
    (hsep : a + 1 < b)
    (hva : v a = v (a + 1)) (hvb : v b = v (b + 1)) :
    ∀ N : ℕ,
      RowVisitCylinderPrefixTransportUpToAt
        (k := k) P i
          ((Equiv.swap a (a + 1)).trans (Equiv.swap b (b + 1)))
          N (Finset.range (m + 1)) v := by
  intro N
  exact rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
    (k := k) P i ((Equiv.swap a (a + 1)).trans (Equiv.swap b (b + 1)))
    N (Finset.range (m + 1)) v
    (rowVisitCylinderUpToCarrierEvidenceEquivAt_family_two_adjacent_swaps_range_of_eq
      (k := k) i m a b v ha hb hsep hva hvb N)

lemma rowVisitCylinderPrefixTransportUpToAt_empty
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (N : ℕ) (v : ℕ → Fin k) :
    RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N (∅ : Finset ℕ) v := by
  exact rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
    (k := k) P i σ N (∅ : Finset ℕ) v
    (rowVisitCylinderUpToCarrierEvidenceEquivAt_empty (k := k) i σ N v)

lemma rowVisitCylinderPrefixTransportUpToAt_refl
    (P : Measure (ℕ → Fin k)) (i : Fin k)
    (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k) :
    RowVisitCylinderPrefixTransportUpToAt (k := k) P i (Equiv.refl ℕ) N S v := by
  exact rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
    (k := k) P i (Equiv.refl ℕ) N S v
    (rowVisitCylinderUpToCarrierEvidenceEquivAt_refl (k := k) i N S v)

lemma rowVisitCylinderPrefixTransportUpToAt_of_fixed
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hS : S.image σ = S)
    (hv : ∀ n ∈ S, v (σ.symm n) = v n) :
    RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v := by
  exact rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
    (k := k) P i σ N S v
    (rowVisitCylinderUpToCarrierEvidenceEquivAt_of_fixed (k := k) i σ N S v hS hv)

/-- Fixed-data constructor: if `σ` stabilizes `S` and `v` is compatible with
the induced index relabeling on `S`, we get the finite-horizon transport
witness for `(i,σ,S,v,N)`. -/
theorem rowVisitCylinderPrefixTransportUpToAt_constructor_fixed
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hS : S.image σ = S)
    (hv : ∀ n ∈ S, v (σ.symm n) = v n) :
    RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v := by
  exact rowVisitCylinderPrefixTransportUpToAt_of_fixed (k := k) P i σ N S v hS hv

/-- Family form: if `σ` stabilizes `S` and `v` is compatible on `S`,
then the finite-horizon transport witnesses hold uniformly in `N`. -/
theorem rowVisitCylinderPrefixTransportUpToAt_family_of_fixed
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (S : Finset ℕ) (v : ℕ → Fin k)
    (hS : S.image σ = S)
    (hv : ∀ n ∈ S, v (σ.symm n) = v n) :
    ∀ N : ℕ, RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v := by
  intro N
  exact rowVisitCylinderPrefixTransportUpToAt_of_fixed (k := k) P i σ N S v hS hv

/-- Fixed-data transport family when `v` is constant on `S`. -/
theorem rowVisitCylinderPrefixTransportUpToAt_family_of_fixed_constOn
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (S : Finset ℕ) (v : ℕ → Fin k) (a : Fin k)
    (hS : S.image σ = S)
    (hv : ∀ n ∈ S, v n = a) :
    ∀ N : ℕ, RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v := by
  intro N
  exact rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
    (k := k) P i σ N S v
    (rowVisitCylinderUpToCarrierEvidenceEquivAt_family_of_fixed_constOn
      (k := k) i σ S v a hS hv N)

/-- Family form on the identity permutation: no stabilization assumptions are needed. -/
theorem rowVisitCylinderPrefixTransportUpToAt_family_refl
    (P : Measure (ℕ → Fin k)) (i : Fin k)
    (S : Finset ℕ) (v : ℕ → Fin k) :
    ∀ N : ℕ, RowVisitCylinderPrefixTransportUpToAt (k := k) P i (Equiv.refl ℕ) N S v := by
  intro N
  exact rowVisitCylinderPrefixTransportUpToAt_refl (k := k) P i N S v

/-- Pointwise-fixing family constructor for transport. -/
theorem rowVisitCylinderPrefixTransportUpToAt_family_of_fixing
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (S : Finset ℕ) (v : ℕ → Fin k)
    (hfix : ∀ n ∈ S, σ n = n) :
    ∀ N : ℕ, RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v := by
  intro N
  exact rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
    (k := k) P i σ N S v
    (rowVisitCylinderUpToCarrierEvidenceEquivAt_of_fixing (k := k) i σ N S v hfix)

lemma rowVisitCylinderPrefixTransportUpToAt_trans_of_carrierEvidenceEquiv
    (P : Measure (ℕ → Fin k)) (i : Fin k)
    (σ τ : Equiv.Perm ℕ) (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hσ :
      RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hτ :
      RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i τ N (S.image σ)
        (fun m => v (σ.symm m))) :
    RowVisitCylinderPrefixTransportUpToAt (k := k) P i (σ.trans τ) N S v := by
  exact rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
    (k := k) P i (σ.trans τ) N S v
    (rowVisitCylinderUpToCarrierEvidenceEquivAt_trans (k := k) i σ τ N S v hσ hτ)

lemma rowVisitCylinderPrefixTransportUpToAt_symm
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (h : RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v) :
    RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ.symm N (S.image σ)
      (fun m => v (σ.symm m)) := by
  classical
  rcases h with ⟨Aσ, A, e, he, hperm, horig⟩
  refine ⟨A, Aσ, e.symm, ?_, ?_, ?_⟩
  · intro ys
    have h0 := he (e.symm ys)
    simpa using h0.symm
  · -- permuted event for `σ.symm` is the original event
    have hS : (S.image σ).image σ.symm = S := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
        simpa using hz
      · intro hx
        refine Finset.mem_image.mpr ?_
        refine ⟨σ x, ?_, by simp⟩
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hset :
        rowVisitCylinderEventUpTo (k := k) i ((S.image σ).image σ.symm) v N =
          rowVisitCylinderEventUpTo (k := k) i S v N :=
      rowVisitCylinderEventUpTo_congr (k := k) i (N := N) hS (by
        intro n hn
        rfl)
    simpa [hset] using horig
  · -- original event for `σ.symm` matches the permuted event from `h`
    simpa using hperm

lemma rowVisitCylinderEventUpTo_prob_eq_of_transportWitness
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (Aσ A : Finset (Fin (N + 1) → Fin k)) (e : Aσ ≃ A)
    (he : ∀ xs : Aσ, evidenceOf (n := N) xs.1 = evidenceOf (n := N) (e xs).1)
    (hperm :
      P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N) =
        Finset.sum Aσ (fun xs => P (cylinder (k := k) (List.ofFn xs))))
    (horig :
      P (rowVisitCylinderEventUpTo (k := k) i S v N) =
        Finset.sum A (fun xs => P (cylinder (k := k) (List.ofFn xs)))) :
    P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N) =
      P (rowVisitCylinderEventUpTo (k := k) i S v N) := by
  calc
    P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N)
        = Finset.sum Aσ (fun xs => P (cylinder (k := k) (List.ofFn xs))) := hperm
    _ = Finset.sum A (fun ys => P (cylinder (k := k) (List.ofFn ys))) :=
      sum_cylinderProb_eq_of_extension_and_evidencePreservingEquiv
        (k := k) μ hμ P hExt Aσ A e he
    _ = P (rowVisitCylinderEventUpTo (k := k) i S v N) := horig.symm

theorem rowVisitCylinderEventUpTo_prob_eq_of_prefixTransportUpToAt
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (htransport : RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v) :
    P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N) =
      P (rowVisitCylinderEventUpTo (k := k) i S v N) := by
  rcases htransport with ⟨Aσ, A, e, he, hperm, horig⟩
  exact rowVisitCylinderEventUpTo_prob_eq_of_transportWitness
    (k := k) μ hμ P hExt i σ N S v Aσ A e he hperm horig

theorem rowVisitCylinderEventUpTo_prob_eq_of_carrierEvidenceEquiv
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hcar :
      RowVisitCylinderUpToCarrierEvidenceEquivAt
        (k := k) i σ N S v) :
    P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N) =
      P (rowVisitCylinderEventUpTo (k := k) i S v N) := by
  rcases hcar with ⟨e, he⟩
  exact rowVisitCylinderEventUpTo_prob_eq_of_prefixTransportUpToAt
    (k := k) μ hμ P hExt i σ N S v
    (rowVisitCylinderPrefixTransportUpToAt_constructor
      (k := k) P i σ N S v e he)

theorem rowVisitCylinderEventUpTo_prob_eq_of_fixed
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (hS : S.image σ = S)
    (hv : ∀ n ∈ S, v (σ.symm n) = v n) :
    P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N) =
      P (rowVisitCylinderEventUpTo (k := k) i S v N) := by
  exact rowVisitCylinderEventUpTo_prob_eq_of_prefixTransportUpToAt
    (k := k) μ hμ P hExt i σ N S v
    (rowVisitCylinderPrefixTransportUpToAt_constructor_fixed
      (k := k) P i σ N S v hS hv)

theorem rowVisitCylinderEventUpTo_prob_eq_of_zero_nonempty
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (S : Finset ℕ) (v : ℕ → Fin k)
    (hS : S.Nonempty) :
    P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) 0) =
      P (rowVisitCylinderEventUpTo (k := k) i S v 0) := by
  exact rowVisitCylinderEventUpTo_prob_eq_of_carrierEvidenceEquiv
    (k := k) μ hμ P hExt i σ 0 S v
    (rowVisitCylinderUpToCarrierEvidenceEquivAt_zero_of_nonempty (k := k) i σ S v hS)

theorem rowVisitCylinderInvariantAll_of_markovExchangeable_prefixTransport
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (htransportAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ),
        RowVisitCylinderPrefixTransportAt (k := k) P i σ) :
    RowVisitCylinderInvariantAll (k := k) P := by
  intro i σ
  exact rowVisitCylinderInvariantAt_of_markovExchangeable_prefixTransport
    (k := k) μ hμ P hExt i σ (htransportAll i σ)

/-- No-`none` branch condition for visit-indexed rows on a finite index set. -/
def RowNoNoneOnFinset (i : Fin k) (S : Finset ℕ) (ω : ℕ → Fin k) : Prop :=
  ∀ n ∈ S, nthVisitTime (k := k) ω i n ≠ none

/-- Almost-everywhere no-`none` branch condition on a finite index set. -/
def RowNoNoneOnFinsetAE (P : Measure (ℕ → Fin k)) (i : Fin k) (S : Finset ℕ) : Prop :=
  ∀ᵐ ω ∂P, RowNoNoneOnFinset (k := k) i S ω

lemma rowNoNoneOnFinsetAE_of_rowInfiniteVisits
    (P : Measure (ℕ → Fin k)) (i : Fin k) (S : Finset ℕ)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    RowNoNoneOnFinsetAE (k := k) P i S := by
  have hnoAll : ∀ n : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none := by
    intro n
    exact ae_nthVisitTime_ne_none_of_ae_infinite_visits (k := k) P i n hrowInf
  classical
  induction' S using Finset.induction_on with a S haS ih
  · simp [RowNoNoneOnFinsetAE, RowNoNoneOnFinset]
  · filter_upwards [hnoAll a, ih] with ω hnoA hnoS n hn
    rcases Finset.mem_insert.mp hn with hEq | hnS
    · simpa [hEq] using hnoA
    · exact hnoS n hnS

lemma rowNoNoneOnFinsetAE_of_noNoneAll
    (P : Measure (ℕ → Fin k)) (i : Fin k)
    (hnoAll : ∀ n : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) :
    ∀ S : Finset ℕ, RowNoNoneOnFinsetAE (k := k) P i S := by
  intro S
  induction' S using Finset.induction_on with a S haS ih
  · simp [RowNoNoneOnFinsetAE, RowNoNoneOnFinset]
  · filter_upwards [hnoAll a, ih] with ω hnoA hnoS n hn
    rcases Finset.mem_insert.mp hn with hEq | hnS
    · simpa [hEq] using hnoA
    · exact hnoS n hnS

lemma rowNoNoneOnFinsetAE_all_of_noNoneAll
    (P : Measure (ℕ → Fin k))
    (hnoAll : ∀ (i : Fin k) (n : ℕ), ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) :
    ∀ (i : Fin k) (S : Finset ℕ), RowNoNoneOnFinsetAE (k := k) P i S := by
  intro i S
  exact rowNoNoneOnFinsetAE_of_noNoneAll (k := k) P i (fun n => hnoAll i n) S

lemma rowNoNoneOnPairAE_of_noNoneAll
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ)
    (hnoAll : ∀ m : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i m ≠ none) :
    RowNoNoneOnFinsetAE (k := k) P i ({n, σ n}) := by
  exact rowNoNoneOnFinsetAE_of_noNoneAll (k := k) P i hnoAll ({n, σ n})

lemma rowNoNoneOnPairAE_of_rowInfiniteVisits
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    RowNoNoneOnFinsetAE (k := k) P i ({n, σ n}) := by
  exact rowNoNoneOnFinsetAE_of_rowInfiniteVisits (k := k) P i ({n, σ n}) hrowInf

/-- Under a no-`none` hypothesis at index `n`, `rowSuccessorAtNthVisit` is
represented by an explicit visit time. -/
lemma rowSuccessorAtNthVisit_eq_successorAt_of_noNone
    (i : Fin k) (n : ℕ) (ω : ℕ → Fin k)
    (hno : nthVisitTime (k := k) ω i n ≠ none) :
    ∃ t : ℕ, nthVisitTime (k := k) ω i n = some t ∧
      rowSuccessorAtNthVisit (k := k) i n ω = successorAt (k := k) ω t := by
  cases hnt : nthVisitTime (k := k) ω i n with
  | none =>
      exact (hno hnt).elim
  | some t =>
      refine ⟨t, rfl, ?_⟩
      simp [rowSuccessorAtNthVisit, hnt]

/-- Finite-index version of the no-`none` branch witness extraction. -/
lemma rowSuccessorAtNthVisit_eq_successorAt_on_finset
    (i : Fin k) (S : Finset ℕ) (ω : ℕ → Fin k)
    (hno : RowNoNoneOnFinset (k := k) i S ω) :
    ∀ n ∈ S, ∃ t : ℕ, nthVisitTime (k := k) ω i n = some t ∧
      rowSuccessorAtNthVisit (k := k) i n ω = successorAt (k := k) ω t := by
  intro n hnS
  exact rowSuccessorAtNthVisit_eq_successorAt_of_noNone (k := k) i n ω (hno n hnS)

lemma mem_rowVisitCylinderEvent_iff_exists_times_of_noNone
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (ω : ℕ → Fin k)
    (hno : RowNoNoneOnFinset (k := k) i S ω) :
    ω ∈ rowVisitCylinderEvent (k := k) i S v ↔
      ∀ n ∈ S, ∃ t : ℕ,
        nthVisitTime (k := k) ω i n = some t ∧ successorAt (k := k) ω t = v n := by
  constructor
  · intro hrow n hnS
    rcases rowSuccessorAtNthVisit_eq_successorAt_of_noNone (k := k) i n ω (hno n hnS) with
      ⟨t, ht, hrowEq⟩
    refine ⟨t, ht, ?_⟩
    exact hrowEq.symm.trans (hrow n hnS)
  · intro htimes n hnS
    rcases htimes n hnS with ⟨t, ht, hsucc⟩
    have hrowEq : rowSuccessorAtNthVisit (k := k) i n ω = successorAt (k := k) ω t := by
      simp [rowSuccessorAtNthVisit, ht]
    exact hrowEq.trans hsucc

lemma mem_rowVisitCylinderEvent_iff_iUnion_upTo_of_noNone
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) (ω : ℕ → Fin k)
    (hno : RowNoNoneOnFinset (k := k) i S ω) :
    ω ∈ rowVisitCylinderEvent (k := k) i S v ↔
      ω ∈ ⋃ N : ℕ, rowVisitCylinderEventUpTo (k := k) i S v N := by
  constructor
  · intro hrow
    have htimes :
        ∀ n ∈ S, ∃ t : ℕ,
          nthVisitTime (k := k) ω i n = some t ∧ successorAt (k := k) ω t = v n :=
      (mem_rowVisitCylinderEvent_iff_exists_times_of_noNone (k := k) i S v ω hno).1 hrow
    classical
    let tSel : ℕ → ℕ :=
      fun n => if hn : n ∈ S then Classical.choose (htimes n hn) else 0
    let N0 : ℕ := Finset.sup S tSel
    let N : ℕ := N0 + 1
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    intro n hnS
    have htSel :
        tSel n = Classical.choose (htimes n hnS) := by
      simp [tSel, hnS]
    have hspec :
        nthVisitTime (k := k) ω i n = some (Classical.choose (htimes n hnS)) ∧
          successorAt (k := k) ω (Classical.choose (htimes n hnS)) = v n :=
      Classical.choose_spec (htimes n hnS)
    refine ⟨tSel n, ?_, ?_, ?_⟩
    · have hle : tSel n ≤ N0 := Finset.le_sup hnS
      have : tSel n < N0 + 1 := Nat.lt_succ_of_le hle
      simpa [N] using this
    · simpa [htSel] using hspec.1
    · simpa [htSel] using hspec.2
  · intro hup n hnS
    rcases Set.mem_iUnion.mp hup with ⟨N, hN⟩
    rcases hN n hnS with ⟨t, htN, htime, hsucc⟩
    have hrowEq : rowSuccessorAtNthVisit (k := k) i n ω = successorAt (k := k) ω t := by
      simp [rowSuccessorAtNthVisit, htime]
    exact hrowEq.trans hsucc

lemma rowVisitCylinderEvent_ae_eq_iUnion_upTo_of_noNoneAE
    (P : Measure (ℕ → Fin k)) (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k)
    (hnoAE : RowNoNoneOnFinsetAE (k := k) P i S) :
    rowVisitCylinderEvent (k := k) i S v =ᵐ[P]
      ⋃ N : ℕ, rowVisitCylinderEventUpTo (k := k) i S v N := by
  filter_upwards [hnoAE] with ω hω
  exact propext
    (mem_rowVisitCylinderEvent_iff_iUnion_upTo_of_noNone
      (k := k) i S v ω hω)

lemma rowVisitCylinderEventUpTo_mono
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k) :
    Monotone (fun N : ℕ => rowVisitCylinderEventUpTo (k := k) i S v N) := by
  intro N M hNM ω hω n hnS
  rcases hω n hnS with ⟨t, htN, htime, hsucc⟩
  refine ⟨t, lt_of_lt_of_le htN hNM, htime, hsucc⟩

theorem rowVisitCylinderEvent_prob_eq_of_upToEq_and_noNoneAE
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (S : Finset ℕ) (v : ℕ → Fin k)
    (hupToEq :
      ∀ N : ℕ,
        P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N) =
          P (rowVisitCylinderEventUpTo (k := k) i S v N))
    (hnoPermAE : RowNoNoneOnFinsetAE (k := k) P i (S.image σ))
    (hnoOrigAE : RowNoNoneOnFinsetAE (k := k) P i S) :
    P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) =
      P (rowVisitCylinderEvent (k := k) i S v) := by
  have hpermAE :
      rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m)) =ᵐ[P]
        ⋃ N : ℕ, rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N :=
    rowVisitCylinderEvent_ae_eq_iUnion_upTo_of_noNoneAE
      (k := k) P i (S.image σ) (fun m => v (σ.symm m)) hnoPermAE
  have horigAE :
      rowVisitCylinderEvent (k := k) i S v =ᵐ[P]
        ⋃ N : ℕ, rowVisitCylinderEventUpTo (k := k) i S v N :=
    rowVisitCylinderEvent_ae_eq_iUnion_upTo_of_noNoneAE
      (k := k) P i S v hnoOrigAE
  have hmonoPerm :
      Monotone (fun N : ℕ =>
        rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N) :=
    rowVisitCylinderEventUpTo_mono (k := k) i (S.image σ) (fun m => v (σ.symm m))
  have hmonoOrig :
      Monotone (fun N : ℕ => rowVisitCylinderEventUpTo (k := k) i S v N) :=
    rowVisitCylinderEventUpTo_mono (k := k) i S v
  have hiSupEq :
      (⨆ N : ℕ,
        P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N)) =
      (⨆ N : ℕ, P (rowVisitCylinderEventUpTo (k := k) i S v N)) := by
    refine le_antisymm ?_ ?_
    · refine iSup_le ?_
      intro N
      calc
        P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N)
            = P (rowVisitCylinderEventUpTo (k := k) i S v N) := hupToEq N
        _ ≤ ⨆ M : ℕ, P (rowVisitCylinderEventUpTo (k := k) i S v M) :=
          le_iSup (fun M => P (rowVisitCylinderEventUpTo (k := k) i S v M)) N
    · refine iSup_le ?_
      intro N
      calc
        P (rowVisitCylinderEventUpTo (k := k) i S v N)
            = P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N) :=
              (hupToEq N).symm
        _ ≤ ⨆ M : ℕ,
              P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) M) :=
          le_iSup
            (fun M =>
              P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) M)) N
  calc
    P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m)))
        = P (⋃ N : ℕ, rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N) := by
          exact measure_congr hpermAE
    _ = ⨆ N : ℕ,
          P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N) := by
          exact (hmonoPerm.measure_iUnion (μ := P))
    _ = ⨆ N : ℕ, P (rowVisitCylinderEventUpTo (k := k) i S v N) := hiSupEq
    _ = P (⋃ N : ℕ, rowVisitCylinderEventUpTo (k := k) i S v N) := by
          exact (hmonoOrig.measure_iUnion (μ := P)).symm
    _ = P (rowVisitCylinderEvent (k := k) i S v) := by
          exact (measure_congr horigAE).symm

lemma rowVisitCylinderEventUpTo_prob_eq_of_prefixTransportUpToFamily
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (htransportUpTo :
      ∀ N : ℕ, RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v) :
    ∀ N : ℕ,
      P (rowVisitCylinderEventUpTo (k := k) i (S.image σ) (fun m => v (σ.symm m)) N) =
        P (rowVisitCylinderEventUpTo (k := k) i S v N) := by
  intro N
  exact rowVisitCylinderEventUpTo_prob_eq_of_prefixTransportUpToAt
    (k := k) μ hμ P hExt i σ N S v (htransportUpTo N)

theorem rowVisitCylinderEvent_prob_eq_of_markovExchangeable_prefixTransportUpToFamily_and_noNoneAE
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (S : Finset ℕ) (v : ℕ → Fin k)
    (htransportUpTo :
      ∀ N : ℕ, RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hnoPermAE : RowNoNoneOnFinsetAE (k := k) P i (S.image σ))
    (hnoOrigAE : RowNoNoneOnFinsetAE (k := k) P i S) :
    P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) =
      P (rowVisitCylinderEvent (k := k) i S v) := by
  refine rowVisitCylinderEvent_prob_eq_of_upToEq_and_noNoneAE
    (k := k) (P := P) (i := i) (σ := σ) (S := S) (v := v) ?_ hnoPermAE hnoOrigAE
  intro N
  exact rowVisitCylinderEventUpTo_prob_eq_of_prefixTransportUpToFamily
    (k := k) μ hμ P hExt i σ S v htransportUpTo N

theorem rowVisitCylinderEvent_prob_eq_of_markovExchangeable_prefixTransportUpToFamily_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (S : Finset ℕ) (v : ℕ → Fin k)
    (htransportUpTo :
      ∀ N : ℕ, RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) =
      P (rowVisitCylinderEvent (k := k) i S v) := by
  exact rowVisitCylinderEvent_prob_eq_of_markovExchangeable_prefixTransportUpToFamily_and_noNoneAE
    (k := k) μ hμ P hExt i σ S v htransportUpTo
    (rowNoNoneOnFinsetAE_of_rowInfiniteVisits (k := k) P i (S.image σ) hrowInf)
    (rowNoNoneOnFinsetAE_of_rowInfiniteVisits (k := k) P i S hrowInf)

theorem rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_and_noNoneAE
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (S : Finset ℕ) (v : ℕ → Fin k)
    (hcarUpTo :
      ∀ N : ℕ, RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hnoPermAE : RowNoNoneOnFinsetAE (k := k) P i (S.image σ))
    (hnoOrigAE : RowNoNoneOnFinsetAE (k := k) P i S) :
    P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) =
      P (rowVisitCylinderEvent (k := k) i S v) := by
  exact rowVisitCylinderEvent_prob_eq_of_markovExchangeable_prefixTransportUpToFamily_and_noNoneAE
    (k := k) μ hμ P hExt i σ S v
    (htransportUpTo := fun N =>
      rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
        (k := k) P i σ N S v (hcarUpTo N))
    hnoPermAE hnoOrigAE

theorem rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (S : Finset ℕ) (v : ℕ → Fin k)
    (hcarUpTo :
      ∀ N : ℕ, RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) =
      P (rowVisitCylinderEvent (k := k) i S v) := by
  exact rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_and_noNoneAE
    (k := k) μ hμ P hExt i σ S v hcarUpTo
    (rowNoNoneOnFinsetAE_of_rowInfiniteVisits (k := k) P i (S.image σ) hrowInf)
    (rowNoNoneOnFinsetAE_of_rowInfiniteVisits (k := k) P i S hrowInf)

theorem rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_constOn_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (S : Finset ℕ) (v : ℕ → Fin k) (a : Fin k)
    (hS : S.image σ = S)
    (hv : ∀ n ∈ S, v n = a)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) =
      P (rowVisitCylinderEvent (k := k) i S v) := by
  exact rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_and_rowInfiniteVisits
    (k := k) μ hμ P hExt i σ S v
    (hcarUpTo := rowVisitCylinderUpToCarrierEvidenceEquivAt_family_of_fixed_constOn
      (k := k) i σ S v a hS hv)
    hrowInf

theorem rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_swap_of_mem_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (a b : ℕ) (S : Finset ℕ) (v : ℕ → Fin k)
    (ha : a ∈ S) (hb : b ∈ S) (hvb : v a = v b)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i (S.image (Equiv.swap a b))
        (fun m => v ((Equiv.swap a b).symm m))) =
      P (rowVisitCylinderEvent (k := k) i S v) := by
  exact rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_and_rowInfiniteVisits
    (k := k) μ hμ P hExt i (Equiv.swap a b) S v
    (hcarUpTo := rowVisitCylinderUpToCarrierEvidenceEquivAt_family_swap_of_mem
      (k := k) i a b S v ha hb hvb)
    hrowInf

theorem rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_adjacent_swap_range_of_eq_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (m a : ℕ) (v : ℕ → Fin k)
    (ha : a + 1 < m + 1) (hvb : v a = v (a + 1))
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i ((Finset.range (m + 1)).image (Equiv.swap a (a + 1)))
        (fun n => v ((Equiv.swap a (a + 1)).symm n))) =
      P (rowVisitCylinderEvent (k := k) i (Finset.range (m + 1)) v) := by
  exact rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_and_rowInfiniteVisits
    (k := k) μ hμ P hExt i (Equiv.swap a (a + 1)) (Finset.range (m + 1)) v
    (hcarUpTo := rowVisitCylinderUpToCarrierEvidenceEquivAt_family_adjacent_swap_range_of_eq
      (k := k) i m a v ha hvb)
    hrowInf

theorem rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_two_adjacent_swaps_range_of_eq_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (m a b : ℕ) (v : ℕ → Fin k)
    (ha : a + 1 < m + 1) (hb : b + 1 < m + 1)
    (hsep : a + 1 < b)
    (hva : v a = v (a + 1)) (hvb : v b = v (b + 1))
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i
        ((Finset.range (m + 1)).image ((Equiv.swap a (a + 1)).trans (Equiv.swap b (b + 1))))
        (fun n => v (((Equiv.swap a (a + 1)).trans (Equiv.swap b (b + 1))).symm n))) =
      P (rowVisitCylinderEvent (k := k) i (Finset.range (m + 1)) v) := by
  exact rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_and_rowInfiniteVisits
    (k := k) μ hμ P hExt i
      ((Equiv.swap a (a + 1)).trans (Equiv.swap b (b + 1))) (Finset.range (m + 1)) v
    (hcarUpTo := rowVisitCylinderUpToCarrierEvidenceEquivAt_family_two_adjacent_swaps_range_of_eq
      (k := k) i m a b v ha hb hsep hva hvb)
    hrowInf

theorem rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_trans_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ τ : Equiv.Perm ℕ)
    (S : Finset ℕ) (v : ℕ → Fin k)
    (hcarσ :
      ∀ N : ℕ, RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hcarτ :
      ∀ N : ℕ, RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i τ N (S.image σ)
        (fun m => v (σ.symm m)))
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i (S.image (σ.trans τ))
          (fun m => v ((σ.trans τ).symm m))) =
      P (rowVisitCylinderEvent (k := k) i S v) := by
  exact
    rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_and_rowInfiniteVisits
      (k := k) μ hμ P hExt i (σ.trans τ) S v
      (hcarUpTo :=
        rowVisitCylinderUpToCarrierEvidenceEquivAt_family_trans
          (k := k) i σ τ S v hcarσ hcarτ)
      hrowInf

theorem rowVisitCylinderInvariantAt_of_markovExchangeable_carrierEvidenceEquivUpToFamily_trans_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ τ : Equiv.Perm ℕ)
    (hcarσ :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hcarτ :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i τ N (S.image σ)
          (fun m => v (σ.symm m)))
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    RowVisitCylinderInvariantAt (k := k) P i (σ.trans τ) := by
  intro S v
  exact
    rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_trans_and_rowInfiniteVisits
      (k := k) μ hμ P hExt i σ τ S v
      (hcarσ := fun N => hcarσ S v N)
      (hcarτ := fun N => hcarτ S v N)
      hrowInf

theorem rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_refl_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (S : Finset ℕ) (v : ℕ → Fin k)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i (S.image (Equiv.refl ℕ))
        (fun m => v ((Equiv.refl ℕ).symm m))) =
      P (rowVisitCylinderEvent (k := k) i S v) := by
  exact
    rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_and_rowInfiniteVisits
      (k := k) μ hμ P hExt i (Equiv.refl ℕ) S v
      (hcarUpTo := rowVisitCylinderUpToCarrierEvidenceEquivAt_family_refl (k := k) i S v)
      hrowInf

theorem rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_swap_pair_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (a b : ℕ) (v : ℕ → Fin k)
    (hvb : v a = v b)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i
          (({a, b} : Finset ℕ).image (Equiv.swap a b))
          (fun m => v ((Equiv.swap a b).symm m))) =
      P (rowVisitCylinderEvent (k := k) i ({a, b} : Finset ℕ) v) := by
  exact
    rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_and_rowInfiniteVisits
      (k := k) μ hμ P hExt i (Equiv.swap a b) ({a, b} : Finset ℕ) v
      (hcarUpTo :=
        rowVisitCylinderUpToCarrierEvidenceEquivAt_family_swap_pair_of_eq
          (k := k) i a b v hvb)
      hrowInf

theorem rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_cycle3_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (a b c : ℕ) (v : ℕ → Fin k)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hvb : v a = v b) (hvc : v b = v c)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i
          (({a, b, c} : Finset ℕ).image ((Equiv.swap a b).trans (Equiv.swap b c)))
          (fun m => v (((Equiv.swap a b).trans (Equiv.swap b c)).symm m))) =
      P (rowVisitCylinderEvent (k := k) i ({a, b, c} : Finset ℕ) v) := by
  exact
    rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_and_rowInfiniteVisits
      (k := k) μ hμ P hExt i ((Equiv.swap a b).trans (Equiv.swap b c))
      ({a, b, c} : Finset ℕ) v
      (hcarUpTo :=
        rowVisitCylinderUpToCarrierEvidenceEquivAt_family_cycle3_of_eq
          (k := k) i a b c v hab hbc hac hvb hvc)
      hrowInf

theorem rowVisitCylinderEvent_prob_eq_of_fixed_and_noNoneAE
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (S : Finset ℕ) (v : ℕ → Fin k)
    (hS : S.image σ = S)
    (hv : ∀ n ∈ S, v (σ.symm n) = v n)
    (hnoPermAE : RowNoNoneOnFinsetAE (k := k) P i (S.image σ))
    (hnoOrigAE : RowNoNoneOnFinsetAE (k := k) P i S) :
    P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) =
      P (rowVisitCylinderEvent (k := k) i S v) := by
  exact rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_and_noNoneAE
    (k := k) μ hμ P hExt i σ S v
    (hcarUpTo :=
      rowVisitCylinderUpToCarrierEvidenceEquivAt_family_of_fixed
        (k := k) i σ S v hS hv)
    hnoPermAE hnoOrigAE

theorem rowVisitCylinderEvent_prob_eq_of_fixed_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (S : Finset ℕ) (v : ℕ → Fin k)
    (hS : S.image σ = S)
    (hv : ∀ n ∈ S, v (σ.symm n) = v n)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) =
      P (rowVisitCylinderEvent (k := k) i S v) := by
  exact rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_and_rowInfiniteVisits
    (k := k) μ hμ P hExt i σ S v
    (hcarUpTo :=
      rowVisitCylinderUpToCarrierEvidenceEquivAt_family_of_fixed
        (k := k) i σ S v hS hv)
    hrowInf

theorem rowVisitCylinderInvariantAt_of_markovExchangeable_prefixTransportUpTo_and_noNoneAE
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (htransportUpTo :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hnoAll : ∀ S : Finset ℕ, RowNoNoneOnFinsetAE (k := k) P i S) :
    RowVisitCylinderInvariantAt (k := k) P i σ := by
  intro S v
  refine rowVisitCylinderEvent_prob_eq_of_upToEq_and_noNoneAE
    (k := k) (P := P) (i := i) (σ := σ) (S := S) (v := v) ?_ ?_ ?_
  · intro N
    exact rowVisitCylinderEventUpTo_prob_eq_of_prefixTransportUpToAt
      (k := k) μ hμ P hExt i σ N S v (htransportUpTo S v N)
  · exact hnoAll (S.image σ)
  · exact hnoAll S

theorem rowVisitCylinderInvariantAll_of_markovExchangeable_prefixTransportUpTo_and_noNoneAE
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (htransportUpToAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hnoAll : ∀ (i : Fin k) (S : Finset ℕ), RowNoNoneOnFinsetAE (k := k) P i S) :
    RowVisitCylinderInvariantAll (k := k) P := by
  intro i σ
  exact rowVisitCylinderInvariantAt_of_markovExchangeable_prefixTransportUpTo_and_noNoneAE
    (k := k) μ hμ P hExt i σ
    (htransportUpTo := fun S v N => htransportUpToAll i σ S v N)
    (hnoAll := fun S => hnoAll i S)

theorem rowVisitCylinderInvariantAll_of_markovExchangeable_prefixTransportUpTo_and_noNoneAll
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (htransportUpToAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hnoNoneAll :
      ∀ (i : Fin k) (n : ℕ), ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) :
    RowVisitCylinderInvariantAll (k := k) P := by
  exact rowVisitCylinderInvariantAll_of_markovExchangeable_prefixTransportUpTo_and_noNoneAE
    (k := k) μ hμ P hExt htransportUpToAll
    (rowNoNoneOnFinsetAE_all_of_noNoneAll (k := k) P hnoNoneAll)

theorem rowVisitCylinderInvariantAt_of_markovExchangeable_carrierEvidenceEquivUpTo_and_noNoneAE
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (hcarAll :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hnoAll : ∀ S : Finset ℕ, RowNoNoneOnFinsetAE (k := k) P i S) :
    RowVisitCylinderInvariantAt (k := k) P i σ := by
  exact rowVisitCylinderInvariantAt_of_markovExchangeable_prefixTransportUpTo_and_noNoneAE
    (k := k) μ hμ P hExt i σ
    (htransportUpTo := fun S v N =>
      rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
        (k := k) P i σ N S v (hcarAll S v N))
    (hnoAll := hnoAll)

theorem rowVisitCylinderInvariantAt_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (htransportUpTo :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    RowVisitCylinderInvariantAt (k := k) P i σ := by
  refine rowVisitCylinderInvariantAt_of_markovExchangeable_prefixTransportUpTo_and_noNoneAE
    (k := k) μ hμ P hExt i σ htransportUpTo ?_
  intro S
  exact rowNoNoneOnFinsetAE_of_rowInfiniteVisits (k := k) P i S hrowInf

theorem rowVisitCylinderInvariantAt_of_markovExchangeable_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (hcarAll :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    RowVisitCylinderInvariantAt (k := k) P i σ := by
  exact
    rowVisitCylinderInvariantAt_of_markovExchangeable_carrierEvidenceEquivUpToFamily_trans_and_rowInfiniteVisits
      (k := k) μ hμ P hExt i σ (Equiv.refl ℕ)
      (hcarσ := fun S v N => hcarAll S v N)
      (hcarτ := fun S v N =>
        rowVisitCylinderUpToCarrierEvidenceEquivAt_refl (k := k) i N
          (S.image σ) (fun m => v (σ.symm m)))
      (hrowInf := hrowInf)

theorem rowVisitCylinderInvariantAll_of_markovExchangeable_carrierEvidenceEquivUpTo_and_noNoneAE
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hcarAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hnoAll : ∀ (i : Fin k) (S : Finset ℕ), RowNoNoneOnFinsetAE (k := k) P i S) :
    RowVisitCylinderInvariantAll (k := k) P := by
  intro i σ
  exact rowVisitCylinderInvariantAt_of_markovExchangeable_carrierEvidenceEquivUpTo_and_noNoneAE
    (k := k) μ hμ P hExt i σ
    (hcarAll := fun S v N => hcarAll i σ S v N)
    (hnoAll := fun S => hnoAll i S)

theorem rowVisitCylinderInvariantAll_of_markovExchangeable_carrierEvidenceEquivUpTo_and_noNoneAll
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hcarAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hnoNoneAll :
      ∀ (i : Fin k) (n : ℕ), ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) :
    RowVisitCylinderInvariantAll (k := k) P := by
  exact rowVisitCylinderInvariantAll_of_markovExchangeable_carrierEvidenceEquivUpTo_and_noNoneAE
    (k := k) μ hμ P hExt hcarAll
    (rowNoNoneOnFinsetAE_all_of_noNoneAll (k := k) P hnoNoneAll)

theorem rowVisitCylinderInvariantAll_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (htransportUpToAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hrowInf : ∀ i : Fin k, ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    RowVisitCylinderInvariantAll (k := k) P := by
  refine rowVisitCylinderInvariantAll_of_markovExchangeable_prefixTransportUpTo_and_noNoneAE
    (k := k) μ hμ P hExt htransportUpToAll ?_
  intro i S
  exact rowNoNoneOnFinsetAE_of_rowInfiniteVisits (k := k) P i S (hrowInf i)

theorem rowVisitCylinderInvariantAll_of_markovExchangeable_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hcarAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hrowInf : ∀ i : Fin k, ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    RowVisitCylinderInvariantAll (k := k) P := by
  intro i σ
  exact rowVisitCylinderInvariantAt_of_markovExchangeable_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
    (k := k) μ hμ P hExt i σ
    (hcarAll := fun S v N => hcarAll i σ S v N)
    (hrowInf := hrowInf i)

theorem exists_extension_rowVisitInvariantAll_of_markovExchangeable_rowRecurrent_and_carrierEvidenceEquivUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrowRec : MarkovRowRecurrentPrefixMeasure (k := k) μ)
    (hcarExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      RowVisitCylinderInvariantAll (k := k) P := by
  rcases hrowRec with ⟨P, hPprob, hExt, hrowInf⟩
  refine ⟨P, hPprob, hExt, ?_⟩
  exact rowVisitCylinderInvariantAll_of_markovExchangeable_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
    (k := k) μ hμ P hExt (hcarExt P hPprob hExt) hrowInf


theorem exists_extension_rowVisitInvariantAll_of_markovExchangeable_rowRecurrent_and_prefixTransportUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrowRec : MarkovRowRecurrentPrefixMeasure (k := k) μ)
    (htransportExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      RowVisitCylinderInvariantAll (k := k) P := by
  rcases hrowRec with ⟨P, hPprob, hExt, hrowInf⟩
  refine ⟨P, hPprob, hExt, ?_⟩
  exact rowVisitCylinderInvariantAll_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
    (k := k) μ hμ P hExt (htransportExt P hPprob hExt) hrowInf


/-- Under a global no-`none` hypothesis at index `n`, singleton row events are
exactly the existential-time successor events. -/
lemma rowSuccessorValueEvent_eq_exists_time_of_noNone
    (i : Fin k) (n : ℕ) (a : Fin k)
    (hno : ∀ ω : ℕ → Fin k, nthVisitTime (k := k) ω i n ≠ none) :
    rowSuccessorValueEvent (k := k) i n a =
      {ω : ℕ → Fin k |
        ∃ t : ℕ, nthVisitTime (k := k) ω i n = some t ∧ successorAt (k := k) ω t = a} := by
  ext ω
  constructor
  · intro hω
    rcases rowSuccessorAtNthVisit_eq_successorAt_of_noNone (k := k) i n ω (hno ω) with
      ⟨t, ht, hrow⟩
    refine ⟨t, ht, ?_⟩
    exact hrow.symm.trans hω
  · intro hω
    rcases hω with ⟨t, ht, hsucc⟩
    have hrow : rowSuccessorAtNthVisit (k := k) i n ω = successorAt (k := k) ω t := by
      simp [rowSuccessorAtNthVisit, ht]
    exact hrow.trans hsucc

lemma mem_rowSuccessorValueEvent_iff_exists_time_of_noNone
    (i : Fin k) (n : ℕ) (a : Fin k) (ω : ℕ → Fin k)
    (hno : nthVisitTime (k := k) ω i n ≠ none) :
    ω ∈ rowSuccessorValueEvent (k := k) i n a ↔
      ∃ t : ℕ, nthVisitTime (k := k) ω i n = some t ∧ successorAt (k := k) ω t = a := by
  constructor
  · intro hω
    rcases rowSuccessorAtNthVisit_eq_successorAt_of_noNone (k := k) i n ω hno with
      ⟨t, ht, hrow⟩
    refine ⟨t, ht, ?_⟩
    exact hrow.symm.trans hω
  · intro hω
    rcases hω with ⟨t, ht, hsucc⟩
    have hrow : rowSuccessorAtNthVisit (k := k) i n ω = successorAt (k := k) ω t := by
      simp [rowSuccessorAtNthVisit, ht]
    exact hrow.trans hsucc

lemma rowSuccessorValueEvent_ae_eq_exists_time_of_noNoneAE
    (P : Measure (ℕ → Fin k)) (i : Fin k) (n : ℕ) (a : Fin k)
    (hnoAE : ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) :
    rowSuccessorValueEvent (k := k) i n a =ᵐ[P]
      {ω : ℕ → Fin k |
        ∃ t : ℕ, nthVisitTime (k := k) ω i n = some t ∧ successorAt (k := k) ω t = a} := by
  filter_upwards [hnoAE] with ω hnoω
  exact propext (mem_rowSuccessorValueEvent_iff_exists_time_of_noNone (k := k) i n a ω hnoω)

/-- Singleton-coordinate consequence of row-visit-cylinder invariance. -/
lemma rowSuccessorValueEvent_prob_eq_of_rowVisitInvariant
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (hvisit : RowVisitCylinderInvariantAt (k := k) P i σ)
    (n : ℕ) (a : Fin k) :
    P (rowSuccessorValueEvent (k := k) i (σ n) a) =
      P (rowSuccessorValueEvent (k := k) i n a) := by
  let S : Finset ℕ := {n}
  let v : ℕ → Fin k := fun m => if m = n then a else i
  have hs :
      P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) =
        P (rowVisitCylinderEvent (k := k) i S v) :=
    hvisit S v
  have hleft :
      rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m)) =
        rowSuccessorValueEvent (k := k) i (σ n) a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent, S, v]
  have hright :
      rowVisitCylinderEvent (k := k) i S v =
        rowSuccessorValueEvent (k := k) i n a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent, S, v]
  simpa [hleft, hright] using hs

/-- Singleton permutation equality, now explicitly routed through a no-`none`
branch condition on the pair of indices `{n, σ n}`. -/
lemma rowSuccessorValueEvent_prob_eq_of_rowVisitInvariant_noNone
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (hvisit : RowVisitCylinderInvariantAt (k := k) P i σ)
    (n : ℕ) (a : Fin k)
    (hnoPair : ∀ ω : ℕ → Fin k, RowNoNoneOnFinset (k := k) i ({n, σ n}) ω) :
    P (rowSuccessorValueEvent (k := k) i (σ n) a) =
      P (rowSuccessorValueEvent (k := k) i n a) := by
  have hnoσ : ∀ ω : ℕ → Fin k, nthVisitTime (k := k) ω i (σ n) ≠ none := by
    intro ω
    exact hnoPair ω (σ n) (by simp)
  have hnoN : ∀ ω : ℕ → Fin k, nthVisitTime (k := k) ω i n ≠ none := by
    intro ω
    exact hnoPair ω n (by simp)
  have hsetσ := rowSuccessorValueEvent_eq_exists_time_of_noNone (k := k) i (σ n) a hnoσ
  have hsetN := rowSuccessorValueEvent_eq_exists_time_of_noNone (k := k) i n a hnoN
  have hbase :=
    rowSuccessorValueEvent_prob_eq_of_rowVisitInvariant
      (k := k) (P := P) (i := i) (σ := σ) hvisit (n := n) (a := a)
  calc
    P (rowSuccessorValueEvent (k := k) i (σ n) a)
        =
      P {ω : ℕ → Fin k |
        ∃ t : ℕ, nthVisitTime (k := k) ω i (σ n) = some t ∧ successorAt (k := k) ω t = a} := by
          rw [hsetσ]
    _ =
      P {ω : ℕ → Fin k |
        ∃ t : ℕ, nthVisitTime (k := k) ω i n = some t ∧ successorAt (k := k) ω t = a} := by
          simpa [hsetσ, hsetN] using hbase
    _ = P (rowSuccessorValueEvent (k := k) i n a) := by
          rw [hsetN]

lemma rowSuccessorValueEvent_prob_eq_of_rowVisitInvariant_noNoneAE
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (hvisit : RowVisitCylinderInvariantAt (k := k) P i σ)
    (n : ℕ) (a : Fin k)
    (hnoPairAE : RowNoNoneOnFinsetAE (k := k) P i ({n, σ n})) :
    P (rowSuccessorValueEvent (k := k) i (σ n) a) =
      P (rowSuccessorValueEvent (k := k) i n a) := by
  let Eσ : Set (ℕ → Fin k) :=
    {ω : ℕ → Fin k |
      ∃ t : ℕ, nthVisitTime (k := k) ω i (σ n) = some t ∧ successorAt (k := k) ω t = a}
  let En : Set (ℕ → Fin k) :=
    {ω : ℕ → Fin k |
      ∃ t : ℕ, nthVisitTime (k := k) ω i n = some t ∧ successorAt (k := k) ω t = a}
  have hnoσAE : ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i (σ n) ≠ none := by
    filter_upwards [hnoPairAE] with ω hω
    exact hω (σ n) (by simp)
  have hnoNAE : ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none := by
    filter_upwards [hnoPairAE] with ω hω
    exact hω n (by simp)
  have hσae :
      rowSuccessorValueEvent (k := k) i (σ n) a =ᵐ[P] Eσ := by
    simpa [Eσ] using
      rowSuccessorValueEvent_ae_eq_exists_time_of_noNoneAE
        (k := k) P i (σ n) a hnoσAE
  have hNae :
      rowSuccessorValueEvent (k := k) i n a =ᵐ[P] En := by
    simpa [En] using
      rowSuccessorValueEvent_ae_eq_exists_time_of_noNoneAE
        (k := k) P i n a hnoNAE
  have hbase :=
    rowSuccessorValueEvent_prob_eq_of_rowVisitInvariant
      (k := k) (P := P) (i := i) (σ := σ) hvisit (n := n) (a := a)
  calc
    P (rowSuccessorValueEvent (k := k) i (σ n) a) = P Eσ := measure_congr hσae
    _ = P En := by
      rw [← measure_congr hσae, ← measure_congr hNae]
      exact hbase
    _ = P (rowSuccessorValueEvent (k := k) i n a) := (measure_congr hNae).symm

theorem rowSuccessorValueEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_noNoneAll
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k)
    (htransportUpTo :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hnoNoneAll :
      ∀ m : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i m ≠ none) :
    P (rowSuccessorValueEvent (k := k) i (σ n) a) =
      P (rowSuccessorValueEvent (k := k) i n a) := by
  have hvisit : RowVisitCylinderInvariantAt (k := k) P i σ :=
    rowVisitCylinderInvariantAt_of_markovExchangeable_prefixTransportUpTo_and_noNoneAE
      (k := k) μ hμ P hExt i σ htransportUpTo
      (rowNoNoneOnFinsetAE_of_noNoneAll (k := k) P i hnoNoneAll)
  exact rowSuccessorValueEvent_prob_eq_of_rowVisitInvariant_noNoneAE
    (k := k) (P := P) (i := i) (σ := σ) (hvisit := hvisit)
    (n := n) (a := a)
    (hnoPairAE := rowNoNoneOnPairAE_of_noNoneAll (k := k) P i σ n hnoNoneAll)

theorem rowSuccessorValueEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k)
    (htransportUpTo :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowSuccessorValueEvent (k := k) i (σ n) a) =
      P (rowSuccessorValueEvent (k := k) i n a) := by
  have hnoNoneAll :
      ∀ m : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i m ≠ none := by
    exact ae_nthVisitTime_ne_none_all_of_ae_infinite_visits (k := k) P i hrowInf
  exact rowSuccessorValueEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_noNoneAll
    (k := k) μ hμ P hExt i σ n a htransportUpTo hnoNoneAll

theorem rowSuccessorValueEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpTo_and_noNoneAll
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k)
    (hcarAll :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hnoNoneAll :
      ∀ m : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i m ≠ none) :
    P (rowSuccessorValueEvent (k := k) i (σ n) a) =
      P (rowSuccessorValueEvent (k := k) i n a) := by
  exact rowSuccessorValueEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_noNoneAll
    (k := k) μ hμ P hExt i σ n a
    (htransportUpTo := fun S v N =>
      rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
        (k := k) P i σ N S v (hcarAll S v N))
    hnoNoneAll

theorem rowSuccessorValueEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k)
    (hcarAll :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowSuccessorValueEvent (k := k) i (σ n) a) =
      P (rowSuccessorValueEvent (k := k) i n a) := by
  exact rowSuccessorValueEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
    (k := k) μ hμ P hExt i σ n a
    (htransportUpTo := fun S v N =>
      rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
        (k := k) P i σ N S v (hcarAll S v N))
    hrowInf

lemma singleton_rowVisitCylinderEvent_prob_eq_of_rowVisitInvariant_noNoneAE
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (hvisit : RowVisitCylinderInvariantAt (k := k) P i σ)
    (n : ℕ) (a : Fin k)
    (hnoPairAE : RowNoNoneOnFinsetAE (k := k) P i ({n, σ n})) :
    P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
      P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i)) := by
  have hsingle :=
    rowSuccessorValueEvent_prob_eq_of_rowVisitInvariant_noNoneAE
      (k := k) (P := P) (i := i) (σ := σ)
      (hvisit := hvisit) (n := n) (a := a) hnoPairAE
  have hleft :
      rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i) =
        rowSuccessorValueEvent (k := k) i (σ n) a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent]
  have hright :
      rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i) =
        rowSuccessorValueEvent (k := k) i n a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent]
  simpa [hleft, hright] using hsingle

lemma singleton_rowVisitCylinderEvent_prob_eq_of_rowVisitInvariant_rowInfiniteVisits
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k)
    (hvisit : RowVisitCylinderInvariantAt (k := k) P i σ)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
      P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i)) := by
  have hnoPairAE :
      RowNoNoneOnFinsetAE P i ({n, σ n}) :=
    rowNoNoneOnPairAE_of_rowInfiniteVisits (k := k) P i σ n hrowInf
  exact singleton_rowVisitCylinderEvent_prob_eq_of_rowVisitInvariant_noNoneAE
    (k := k) (P := P) (i := i) (σ := σ) (n := n) (a := a) hvisit hnoPairAE

theorem singleton_rowVisitCylinderEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_noNoneAll
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k)
    (htransportUpTo :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hnoNoneAll :
      ∀ m : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i m ≠ none) :
    P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
      P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i)) := by
  have hvisit : RowVisitCylinderInvariantAt (k := k) P i σ :=
    rowVisitCylinderInvariantAt_of_markovExchangeable_prefixTransportUpTo_and_noNoneAE
      (k := k) μ hμ P hExt i σ htransportUpTo
      (rowNoNoneOnFinsetAE_of_noNoneAll (k := k) P i hnoNoneAll)
  have hnoPairAE : RowNoNoneOnFinsetAE (k := k) P i ({n, σ n}) :=
    rowNoNoneOnPairAE_of_noNoneAll (k := k) P i σ n hnoNoneAll
  exact singleton_rowVisitCylinderEvent_prob_eq_of_rowVisitInvariant_noNoneAE
    (k := k) (P := P) (i := i) (σ := σ) (n := n) (a := a) hvisit hnoPairAE

theorem singleton_rowVisitCylinderEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k)
    (htransportUpTo :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
      P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i)) := by
  have hnoNoneAll :
      ∀ m : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i m ≠ none := by
    exact ae_nthVisitTime_ne_none_all_of_ae_infinite_visits (k := k) P i hrowInf
  exact singleton_rowVisitCylinderEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_noNoneAll
    (k := k) μ hμ P hExt i σ n a htransportUpTo hnoNoneAll

theorem singleton_rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpTo_and_noNoneAll
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k)
    (hcarAll :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hnoNoneAll :
      ∀ m : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i m ≠ none) :
    P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
      P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i)) := by
  exact singleton_rowVisitCylinderEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_noNoneAll
    (k := k) μ hμ P hExt i σ n a
    (htransportUpTo := fun S v N =>
      rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
        (k := k) P i σ N S v (hcarAll S v N))
    hnoNoneAll

theorem singleton_rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k)
    (hcarAll :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
      P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i)) := by
  exact singleton_rowVisitCylinderEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
    (k := k) μ hμ P hExt i σ n a
    (htransportUpTo := fun S v N =>
      rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
        (k := k) P i σ N S v (hcarAll S v N))
    hrowInf

lemma rowVisitCylinderEvent_iInter_prob_eq_of_rowVisitInvariant
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (hvisit : RowVisitCylinderInvariantAt (k := k) P i σ)
    (S : Finset ℕ) (v : ℕ → Fin k) :
    P (⋂ n ∈ S, rowSuccessorValueEvent (k := k) i (σ n) (v n)) =
      P (⋂ n ∈ S, rowSuccessorValueEvent (k := k) i n (v n)) := by
  have hs : P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) =
      P (rowVisitCylinderEvent (k := k) i S v) := hvisit S v
  have hleft :
      (⋂ n ∈ S, rowSuccessorValueEvent (k := k) i (σ n) (v n)) =
        rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m)) := by
    calc
      (⋂ n ∈ S, rowSuccessorValueEvent (k := k) i (σ n) (v n))
          = {ω : ℕ → Fin k | ∀ n ∈ S, rowSuccessorAtNthVisit (k := k) i (σ n) ω = v n} := by
              ext ω
              simp [rowSuccessorValueEvent]
      _ = rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m)) := by
            exact rowSuccessorVisit_perm_event_set_eq (k := k) i σ S v
  have hright :
      (⋂ n ∈ S, rowSuccessorValueEvent (k := k) i n (v n)) =
        rowVisitCylinderEvent (k := k) i S v := by
    symm
    exact rowVisitCylinderEvent_eq_iInter_rowSuccessorValueEvent (k := k) i S v
  calc
    P (⋂ n ∈ S, rowSuccessorValueEvent (k := k) i (σ n) (v n))
        = P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) := by
            rw [hleft]
    _ = P (rowVisitCylinderEvent (k := k) i S v) := hs
    _ = P (⋂ n ∈ S, rowSuccessorValueEvent (k := k) i n (v n)) := by
            rw [hright]

/-- Focus counterexample: row-visit permutation invariance is not automatic for
arbitrary extension measures. For the deterministic path `0,1,1,1,...` on
`Fin 2`, swapping visit indices `0` and `1` at anchor `0` changes the singleton
row-successor event probability. -/
theorem not_rowVisitCylinderInvariantAt_dirac_omega01 :
    let i0 : Fin 2 := ⟨0, by decide⟩
    let i1 : Fin 2 := ⟨1, by decide⟩
    let ω01 : ℕ → Fin 2 := fun n => if n = 0 then i0 else i1
    ¬ RowVisitCylinderInvariantAt (k := 2)
      (Measure.dirac ω01) i0 (Equiv.swap 0 1) := by
  intro i0 i1 ω01 hinv
  have hEq := rowSuccessorValueEvent_prob_eq_of_rowVisitInvariant
    (k := 2) (P := Measure.dirac ω01) (i := i0) (σ := Equiv.swap 0 1)
    hinv (n := 0) (a := i1)
  have hswap : (Equiv.swap 0 1) 0 = 1 := by simp
  rw [hswap] at hEq
  have hLeft :
      (Measure.dirac ω01) (rowSuccessorValueEvent (k := 2) i0 1 i1) = 0 := by
    unfold rowSuccessorValueEvent
    rw [Measure.dirac_apply' ω01 (measurableSet_rowSuccessorAtNthVisit_eq (k := 2) i0 1 i1)]
    have hnot : ¬ rowSuccessorAtNthVisit (k := 2) i0 1 ω01 = i1 := by
      simp [rowSuccessorAtNthVisit, ω01, nthVisitTime,
        nthVisitTimeExists, isNthVisitTime, visitCountBefore, i0, i1]
    simp [Set.indicator, hnot]
  have hRight :
      (Measure.dirac ω01) (rowSuccessorValueEvent (k := 2) i0 0 i1) = 1 := by
    unfold rowSuccessorValueEvent
    rw [Measure.dirac_apply' ω01 (measurableSet_rowSuccessorAtNthVisit_eq (k := 2) i0 0 i1)]
    have hmem : rowSuccessorAtNthVisit (k := 2) i0 0 ω01 = i1 := by
      simp [rowSuccessorAtNthVisit, ω01, nthVisitTime,
        nthVisitTimeExists, isNthVisitTime, visitCountBefore, i0, i1]
    simp [Set.indicator, hmem]
  rw [hLeft, hRight] at hEq
  exact zero_ne_one hEq

/-- Finite-horizon carrier equivalence is not available without additional
structure assumptions: for `k=2`, `N=1`, anchor `0`, `S={0}` and `σ=(0 1)`,
the permuted carrier is empty while the original carrier is nonempty. -/
theorem not_rowVisitCylinderUpToCarrierEvidenceEquivAt_swap01_N1 :
    let i0 : Fin 2 := ⟨0, by decide⟩
    let i1 : Fin 2 := ⟨1, by decide⟩
    let σ : Equiv.Perm ℕ := Equiv.swap 0 1
    let S : Finset ℕ := ({0} : Finset ℕ)
    let v : ℕ → Fin 2 := fun _ => i1
    ¬ RowVisitCylinderUpToCarrierEvidenceEquivAt (k := 2) i0 σ 1 S v := by
  intro i0 i1 σ S v hEq
  classical
  set L := rowVisitCylinderEventUpToPrefixCarrier (k := 2) i0 (S.image σ) (fun m => v (σ.symm m)) 1
  set R := rowVisitCylinderEventUpToPrefixCarrier (k := 2) i0 S v 1
  have hLempty : L = (∅ : Finset (Fin (1 + 1) → Fin 2)) := by
    ext xs
    constructor
    · intro hxs
      have hmem : rowVisitCylinderEventUpTo (k := 2) i0 (S.image σ) (fun m => v (σ.symm m)) 1
          (prefixExtend (k := 2) 1 xs) := by
        simpa [L, rowVisitCylinderEventUpToPrefixCarrier] using (Finset.mem_filter.mp hxs).2
      have h1 : 1 ∈ S.image σ := by
        simp [S, σ]
      rcases hmem 1 h1 with ⟨t, htlt, htime, _⟩
      have ht0 : t = 0 := Nat.lt_one_iff.mp htlt
      subst ht0
      have his : isNthVisitTime (k := 2) (prefixExtend (k := 2) 1 xs) i0 1 0 :=
        (nthVisitTime_eq_some_iff (k := 2) (prefixExtend (k := 2) 1 xs) i0 1 0).1 htime
      have hnot : ¬ isNthVisitTime (k := 2) (prefixExtend (k := 2) 1 xs) i0 1 0 := by
        simp [isNthVisitTime, visitCountBefore]
      exact (hnot his).elim
    · intro hxs
      simp at hxs
  let xs01 : Fin (1 + 1) → Fin 2 := fun j => if j.1 = 0 then i0 else i1
  have hRnonempty : xs01 ∈ R := by
    refine Finset.mem_filter.mpr ?_
    refine ⟨Finset.mem_univ xs01, ?_⟩
    intro n hn
    have hn0 : n = 0 := by simpa [S] using hn
    subst hn0
    refine ⟨0, by decide, ?_, ?_⟩
    · apply (nthVisitTime_eq_some_iff (k := 2) (prefixExtend (k := 2) 1 xs01) i0 0 0).2
      simp [isNthVisitTime, visitCountBefore, prefixExtend, xs01, i0, i1]
    · simp [successorAt, prefixExtend, xs01, v, i0, i1]
  rcases hEq with ⟨e, _he⟩
  let xr : R := ⟨xs01, hRnonempty⟩
  have hxL : (e.symm xr).1 ∈ L := (e.symm xr).2
  have : (e.symm xr).1 ∈ (∅ : Finset (Fin (1 + 1) → Fin 2)) := by
    rw [← hLempty]
    exact hxL
  simp at this

theorem not_universal_rowVisitCylinderUpToCarrierEvidenceEquivAt :
    ¬ (∀ (i : Fin 2) (σ : Equiv.Perm ℕ) (N : ℕ) (S : Finset ℕ) (v : ℕ → Fin 2),
      RowVisitCylinderUpToCarrierEvidenceEquivAt (k := 2) i σ N S v) := by
  intro hall
  have hbad := hall
    (⟨0, by decide⟩ : Fin 2) (Equiv.swap 0 1) 1 ({0} : Finset ℕ)
    (fun _ => (⟨1, by decide⟩ : Fin 2))
  exact not_rowVisitCylinderUpToCarrierEvidenceEquivAt_swap01_N1 hbad

theorem not_rowVisitCylinderPrefixTransportAt_dirac_omega01_of_extension
    (μ : FiniteAlphabet.PrefixMeasure (Fin 2))
    (hμ : MarkovExchangeablePrefixMeasure (k := 2) μ)
    (hExt :
      ∀ xs : List (Fin 2),
        μ xs = (Measure.dirac (fun n : ℕ => if n = 0 then (⟨0, by decide⟩ : Fin 2) else ⟨1, by decide⟩))
          (cylinder (k := 2) xs)) :
    ¬ RowVisitCylinderPrefixTransportAt (k := 2)
      (Measure.dirac (fun n : ℕ => if n = 0 then (⟨0, by decide⟩ : Fin 2) else ⟨1, by decide⟩))
      (⟨0, by decide⟩ : Fin 2) (Equiv.swap 0 1) := by
  intro htransport
  have hinv :
      RowVisitCylinderInvariantAt (k := 2)
        (Measure.dirac (fun n : ℕ => if n = 0 then (⟨0, by decide⟩ : Fin 2) else ⟨1, by decide⟩))
        (⟨0, by decide⟩ : Fin 2) (Equiv.swap 0 1) :=
    rowVisitCylinderInvariantAt_of_markovExchangeable_prefixTransport
      (k := 2) μ hμ
      (Measure.dirac (fun n : ℕ => if n = 0 then (⟨0, by decide⟩ : Fin 2) else ⟨1, by decide⟩))
      hExt
      (⟨0, by decide⟩ : Fin 2) (Equiv.swap 0 1) htransport
  have hnot :
      ¬ RowVisitCylinderInvariantAt (k := 2)
          (Measure.dirac (fun n : ℕ => if n = 0 then (⟨0, by decide⟩ : Fin 2) else ⟨1, by decide⟩))
          (⟨0, by decide⟩ : Fin 2) (Equiv.swap 0 1) := by
    simpa using not_rowVisitCylinderInvariantAt_dirac_omega01
  exact hnot hinv

theorem not_exists_markovExchangeable_extension_with_prefixTransportAt_dirac_omega01 :
    ¬ ∃ (μ : FiniteAlphabet.PrefixMeasure (Fin 2)),
      MarkovExchangeablePrefixMeasure (k := 2) μ ∧
      (∀ xs : List (Fin 2),
        μ xs = (Measure.dirac (fun n : ℕ => if n = 0 then (⟨0, by decide⟩ : Fin 2) else ⟨1, by decide⟩))
          (cylinder (k := 2) xs)) ∧
      RowVisitCylinderPrefixTransportAt (k := 2)
        (Measure.dirac (fun n : ℕ => if n = 0 then (⟨0, by decide⟩ : Fin 2) else ⟨1, by decide⟩))
        (⟨0, by decide⟩ : Fin 2) (Equiv.swap 0 1) := by
  intro h
  rcases h with ⟨μ, hμ, hExt, htransport⟩
  exact
    (not_rowVisitCylinderPrefixTransportAt_dirac_omega01_of_extension
      (μ := μ) hμ hExt) htransport

/-- If row-visit cylinder events are permutation-invariant under `P`, then the
row-process law has the corresponding finite-cylinder invariance. -/
lemma rowProcessLaw_perm_cylinder_of_rowVisitInvariant
    (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
    (hvisit : RowVisitCylinderInvariantAt (k := k) P i σ) :
    ∀ (S : Finset ℕ) (v : ℕ → Fin k),
      rowProcessLaw (k := k) P i
        (rowFiniteCylinder (k := k) (S.image σ) (fun m => v (σ.symm m))) =
      rowProcessLaw (k := k) P i (rowFiniteCylinder (k := k) S v) := by
  intro S v
  rw [rowProcessLaw_rowFiniteCylinder_apply (k := k) P i (S := S.image σ) (v := fun m => v (σ.symm m))]
  rw [rowProcessLaw_rowFiniteCylinder_apply (k := k) P i (S := S) (v := v)]
  exact hvisit S v

lemma rowProcessLaw_perm_cylinder_all_of_rowVisitInvariantAll
    (P : Measure (ℕ → Fin k))
    (hvisitAll : RowVisitCylinderInvariantAll (k := k) P) :
    ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k),
      rowProcessLaw (k := k) P i
        (rowFiniteCylinder (k := k) (S.image σ) (fun m => v (σ.symm m))) =
      rowProcessLaw (k := k) P i (rowFiniteCylinder (k := k) S v) := by
  intro i σ S v
  exact rowProcessLaw_perm_cylinder_of_rowVisitInvariant (k := k) P i σ (hvisitAll i σ) S v

/-- Coordinate permutation action on row trajectories. -/
def rowPermute (σ : Equiv.Perm ℕ) (r : ℕ → Fin k) : ℕ → Fin k :=
  fun n => r (σ n)

lemma measurable_rowPermute (σ : Equiv.Perm ℕ) :
    Measurable (rowPermute (k := k) σ) := by
  classical
  have hcoord : ∀ n : ℕ, Measurable (fun r : ℕ → Fin k => r (σ n)) := by
    intro n
    simpa using (measurable_pi_apply (σ n))
  simpa [rowPermute] using
    (measurable_pi_lambda (f := rowPermute (k := k) σ) hcoord)

/-- Generator set of row finite-cylinder events. -/
def rowFiniteCylinderSets (k : ℕ) : Set (Set (ℕ → Fin k)) :=
  {A | ∃ S : Finset ℕ, ∃ v : ℕ → Fin k, A = rowFiniteCylinder (k := k) S v}

lemma isPiSystem_rowFiniteCylinderSets :
    IsPiSystem (rowFiniteCylinderSets k) := by
  intro s hs t ht hne
  rcases hs with ⟨S, v, rfl⟩
  rcases ht with ⟨T, w, rfl⟩
  rcases hne with ⟨r0, hr0⟩
  have hr0S : ∀ n ∈ S, r0 n = v n := hr0.1
  have hr0T : ∀ n ∈ T, r0 n = w n := hr0.2
  let u : ℕ → Fin k := fun n => if n ∈ S then v n else w n
  refine ⟨S ∪ T, u, ?_⟩
  ext r
  constructor
  · intro hr n hnU
    by_cases hnS : n ∈ S
    · simpa [rowFiniteCylinder, u, hnS] using hr.1 n hnS
    · have hnT : n ∈ T := (Finset.mem_union.mp hnU).resolve_left hnS
      simpa [rowFiniteCylinder, u, hnS] using hr.2 n hnT
  · intro hr
    constructor
    · intro n hnS
      have hnU : n ∈ S ∪ T := Finset.mem_union.mpr (Or.inl hnS)
      simpa [rowFiniteCylinder, u, hnS] using hr n hnU
    · intro n hnT
      have hnU : n ∈ S ∪ T := Finset.mem_union.mpr (Or.inr hnT)
      by_cases hnS : n ∈ S
      · have hvw : v n = w n := by
          calc
            v n = r0 n := (hr0S n hnS).symm
            _ = w n := hr0T n hnT
        simpa [rowFiniteCylinder, u, hnS, hvw] using hr n hnU
      · simpa [rowFiniteCylinder, u, hnS] using hr n hnU

/-- Extend row finite-cylinder equalities to full measure equality under a
generated-sigma assumption. -/
lemma rowProcessLaw_perm_eq_of_generateFrom
    (P : Measure (ℕ → Fin k))
    (hfin : IsFiniteMeasure P)
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (hperm :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k),
        rowProcessLaw (k := k) P i
          (rowFiniteCylinder (k := k) (S.image σ) (fun m => v (σ.symm m))) =
        rowProcessLaw (k := k) P i (rowFiniteCylinder (k := k) S v)) :
    Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
      rowProcessLaw (k := k) P i := by
  letI : IsFiniteMeasure P := hfin
  let μσ : Measure (ℕ → Fin k) :=
    Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i)
  let ν : Measure (ℕ → Fin k) := rowProcessLaw (k := k) P i
  have h_eq :
      ∀ s ∈ rowFiniteCylinderSets k, μσ s = ν s := by
    intro s hs
    rcases hs with ⟨S, v, rfl⟩
    rw [show μσ = Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) by rfl]
    rw [Measure.map_apply (measurable_rowPermute (k := k) σ)
      (measurableSet_rowFiniteCylinder (k := k) S v)]
    have hpre :
        (rowPermute (k := k) σ) ⁻¹' (rowFiniteCylinder (k := k) S v) =
          rowFiniteCylinder (k := k) (S.image σ)
            (fun m => v (σ.symm m)) := by
      ext r
      simp [rowPermute, rowFiniteCylinder]
    rw [hpre]
    simpa [ν] using hperm S v
  have htop : ∀ t ∈ ({Set.univ} : Set (Set (ℕ → Fin k))), μσ t ≠ ⊤ := by
    intro t ht
    have htuniv : t = (Set.univ : Set (ℕ → Fin k)) := by simpa using ht
    subst htuniv
    rw [show μσ = Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) by rfl]
    rw [Measure.map_apply (measurable_rowPermute (k := k) σ) MeasurableSet.univ]
    simp [rowProcessLaw]
  have hT_eq : ∀ t ∈ ({Set.univ} : Set (Set (ℕ → Fin k))), μσ t = ν t := by
    intro t ht
    have htuniv : t = (Set.univ : Set (ℕ → Fin k)) := by simpa using ht
    subst htuniv
    rw [show μσ = Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) by rfl]
    rw [Measure.map_apply (measurable_rowPermute (k := k) σ) MeasurableSet.univ]
    simp [ν, rowProcessLaw]
  have hST_eq :
      ∀ t ∈ ({Set.univ} : Set (Set (ℕ → Fin k))),
        ∀ s ∈ rowFiniteCylinderSets k, μσ (s ∩ t) = ν (s ∩ t) := by
    intro t ht s hs
    have htuniv : t = (Set.univ : Set (ℕ → Fin k)) := by simpa using ht
    subst htuniv
    simp [h_eq s hs]
  have hU : ⋃₀ ({Set.univ} : Set (Set (ℕ → Fin k))) = Set.univ := by
    simp
  have hcount : ({Set.univ} : Set (Set (ℕ → Fin k))).Countable := by
    exact Set.countable_singleton (Set.univ : Set (ℕ → Fin k))
  have hpi : IsPiSystem (rowFiniteCylinderSets k) := isPiSystem_rowFiniteCylinderSets (k := k)
  have hμν : μσ = ν :=
    Measure.ext_of_generateFrom_of_cover
    (μ := μσ) (ν := ν) (S := rowFiniteCylinderSets k) (T := {Set.univ})
    hgen hcount hpi hU htop hST_eq hT_eq
  simpa [μσ, ν] using hμν

theorem rowProcess_perm_eq_of_markovExchangeable_prefixTransportUpTo_and_noNoneAll
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (htransportUpTo :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hnoNoneAll :
      ∀ n : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none)
    (hfin : IsFiniteMeasure P) :
    Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
      rowProcessLaw (k := k) P i := by
  have hvisit : RowVisitCylinderInvariantAt (k := k) P i σ :=
    rowVisitCylinderInvariantAt_of_markovExchangeable_prefixTransportUpTo_and_noNoneAE
      (k := k) μ hμ P hExt i σ htransportUpTo
      (rowNoNoneOnFinsetAE_of_noNoneAll (k := k) P i hnoNoneAll)
  have hperm :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k),
        rowProcessLaw (k := k) P i
          (rowFiniteCylinder (k := k) (S.image σ) (fun m => v (σ.symm m))) =
        rowProcessLaw (k := k) P i (rowFiniteCylinder (k := k) S v) := by
    intro S v
    exact rowProcessLaw_perm_cylinder_of_rowVisitInvariant
      (k := k) P i σ (hvisit := hvisit) S v
  exact rowProcessLaw_perm_eq_of_generateFrom (k := k) P hfin i σ hgen hperm

theorem rowProcess_perm_eq_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (htransportUpTo :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i})
    (hfin : IsFiniteMeasure P) :
    Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
      rowProcessLaw (k := k) P i := by
  have hnoNoneAll :
      ∀ n : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none :=
    ae_nthVisitTime_ne_none_all_of_ae_infinite_visits (k := k) P i hrowInf
  exact rowProcess_perm_eq_of_markovExchangeable_prefixTransportUpTo_and_noNoneAll
    (k := k) μ hμ P hExt hgen i σ htransportUpTo hnoNoneAll hfin

theorem rowProcess_perm_eq_of_markovExchangeable_carrierEvidenceEquivUpTo_and_noNoneAll
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (hcarAll :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hnoNoneAll :
      ∀ n : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none)
    (hfin : IsFiniteMeasure P) :
    Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
      rowProcessLaw (k := k) P i := by
  exact rowProcess_perm_eq_of_markovExchangeable_prefixTransportUpTo_and_noNoneAll
    (k := k) μ hμ P hExt hgen i σ
    (htransportUpTo := fun S v N =>
      rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
        (k := k) P i σ N S v (hcarAll S v N))
    hnoNoneAll hfin

theorem rowProcess_perm_eq_of_markovExchangeable_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (i : Fin k) (σ : Equiv.Perm ℕ)
    (hcarAll :
      ∀ (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hrowInf : ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i})
    (hfin : IsFiniteMeasure P) :
    Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
      rowProcessLaw (k := k) P i := by
  exact rowProcess_perm_eq_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
    (k := k) μ hμ P hExt hgen i σ
    (htransportUpTo := fun S v N =>
      rowVisitCylinderPrefixTransportUpToAt_of_carrierEvidenceEquiv
        (k := k) P i σ N S v (hcarAll S v N))
    hrowInf hfin

/-- Concrete Fortini row-exchangeability placeholder aligned with current
Markov-exchangeability interface. -/
def FortiniRowExchangeableConcrete (μ : FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  MarkovExchangeablePrefixMeasure (k := k) μ

/-- Strengthened concrete row-exchangeability package:
Markov-exchangeability plus finite-permutation row-cylinder pushforward invariance. -/
def FortiniRowExchangeableConcreteStrengthened
    (μ : FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  FortiniRowExchangeableConcrete (k := k) μ ∧
    ∀ (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
      (S : Finset ℕ) (v : ℕ → Fin k),
      rowProcessLaw (k := k) P i
        {r : ℕ → Fin k | ∀ n ∈ S, r (σ n) = v n} =
      rowProcessLaw (k := k) P i
        (rowFiniteCylinder (k := k) (S.image σ) (fun m => v (σ.symm m)))

/-- Packaging lemma: concrete row-exchangeability strengthens to include the
finite-permutation row-cylinder pushforward equality law. -/
theorem fortiniRowExchangeableConcrete_strengthening
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ) :
    FortiniRowExchangeableConcreteStrengthened (k := k) μ := by
  refine ⟨hμ, ?_⟩
  intro P i σ S v
  exact rowProcessLaw_perm_cylinder_apply (k := k) P i σ S v

/-- Generated-σ-algebra strengthening: row-process laws are permutation-invariant
as measures once the ambient measurable space is identified with the sigma
generated by row finite cylinders. -/
theorem fortiniRowExchangeableConcrete_strengthening_generated
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (hvisitAll :
      ∀ (P : Measure (ℕ → Fin k)), RowVisitCylinderInvariantAll (k := k) P)
    (hnoNoneAll :
      ∀ (P : Measure (ℕ → Fin k)) (i : Fin k) (n : ℕ),
        ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) :
    FortiniRowExchangeableConcreteStrengthened (k := k) μ ∧
      (∀ (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
        (n : ℕ) (a : Fin k),
        P (rowSuccessorValueEvent (k := k) i (σ n) a) =
          P (rowSuccessorValueEvent (k := k) i n a)) ∧
      (∀ (P : Measure (ℕ → Fin k))
        (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
        Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
          rowProcessLaw (k := k) P i) := by
  refine ⟨fortiniRowExchangeableConcrete_strengthening (k := k) μ hμ, ?_, ?_⟩
  · intro P i σ n a
    have hnoPairAE : RowNoNoneOnFinsetAE (k := k) P i ({n, σ n}) :=
      rowNoNoneOnPairAE_of_noNoneAll (k := k) P i σ n (hnoAll := hnoNoneAll P i)
    exact
      rowSuccessorValueEvent_prob_eq_of_rowVisitInvariant_noNoneAE
        (k := k) (P := P) (i := i) (σ := σ)
        (hvisit := hvisitAll P i σ) (n := n) (a := a) hnoPairAE
  · intro P i σ hfin
    have hpermAll :
        ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k),
          rowProcessLaw (k := k) P i
            (rowFiniteCylinder (k := k) (S.image σ) (fun m => v (σ.symm m))) =
          rowProcessLaw (k := k) P i (rowFiniteCylinder (k := k) S v) :=
      rowProcessLaw_perm_cylinder_all_of_rowVisitInvariantAll (k := k) P (hvisitAll P)
    exact rowProcessLaw_perm_eq_of_generateFrom (k := k) P hfin i σ hgen
      (hperm := hpermAll i σ)

theorem fortiniRowExchangeableConcrete_strengthening_generated_of_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (hvisitAll :
      ∀ (P : Measure (ℕ → Fin k)), RowVisitCylinderInvariantAll (k := k) P)
    (hrowInfAll :
      ∀ (P : Measure (ℕ → Fin k)) (i : Fin k),
        ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    FortiniRowExchangeableConcreteStrengthened (k := k) μ ∧
      (∀ (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ)
        (n : ℕ) (a : Fin k),
        P (rowSuccessorValueEvent (k := k) i (σ n) a) =
          P (rowSuccessorValueEvent (k := k) i n a)) ∧
      (∀ (P : Measure (ℕ → Fin k))
        (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
        Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
          rowProcessLaw (k := k) P i) := by
  have hnoNoneAll :
      ∀ (P : Measure (ℕ → Fin k)) (i : Fin k) (n : ℕ),
        ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none := by
    intro P i
    exact ae_nthVisitTime_ne_none_all_of_ae_infinite_visits (k := k) P i (hrowInfAll P i)
  exact fortiniRowExchangeableConcrete_strengthening_generated
    (k := k) μ hμ hgen hvisitAll hnoNoneAll

theorem fortiniRowExchangeableConcrete_strengthening_generated_at_of_prefixTransport
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (htransportAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ),
        RowVisitCylinderPrefixTransportAt (k := k) P i σ)
    (hnoNoneAll :
      ∀ (i : Fin k) (n : ℕ),
        ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) :
    (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
      P (rowSuccessorValueEvent (k := k) i (σ n) a) =
        P (rowSuccessorValueEvent (k := k) i n a)) ∧
    (∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
      Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
        rowProcessLaw (k := k) P i) := by
  have hvisitAll : RowVisitCylinderInvariantAll (k := k) P :=
    rowVisitCylinderInvariantAll_of_markovExchangeable_prefixTransport
      (k := k) μ hμ P hExt htransportAll
  refine ⟨?_, ?_⟩
  · intro i σ n a
    have hnoPairAE : RowNoNoneOnFinsetAE (k := k) P i ({n, σ n}) :=
      rowNoNoneOnPairAE_of_noNoneAll (k := k) P i σ n (hnoAll := hnoNoneAll i)
    exact rowSuccessorValueEvent_prob_eq_of_rowVisitInvariant_noNoneAE
      (k := k) (P := P) (i := i) (σ := σ) (hvisit := hvisitAll i σ)
      (n := n) (a := a) hnoPairAE
  · intro i σ hfin
    have hperm :
        ∀ (S : Finset ℕ) (v : ℕ → Fin k),
          rowProcessLaw (k := k) P i
            (rowFiniteCylinder (k := k) (S.image σ) (fun m => v (σ.symm m))) =
          rowProcessLaw (k := k) P i (rowFiniteCylinder (k := k) S v) := by
      intro S v
      exact rowProcessLaw_perm_cylinder_of_rowVisitInvariant
        (k := k) P i σ (hvisit := hvisitAll i σ) S v
    exact rowProcessLaw_perm_eq_of_generateFrom (k := k) P hfin i σ hgen hperm

theorem fortiniRowExchangeableConcrete_strengthening_generated_at_of_prefixTransportUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (htransportUpToAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hnoNoneAll :
      ∀ (i : Fin k) (n : ℕ),
        ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) :
    (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
      P (rowSuccessorValueEvent (k := k) i (σ n) a) =
        P (rowSuccessorValueEvent (k := k) i n a)) ∧
    (∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
      Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
        rowProcessLaw (k := k) P i) := by
  refine ⟨?_, ?_⟩
  · intro i σ n a
    exact rowSuccessorValueEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_noNoneAll
      (k := k) μ hμ P hExt i σ n a
      (htransportUpTo := fun S v N => htransportUpToAll i σ S v N)
      (hnoNoneAll := fun m => hnoNoneAll i m)
  · intro i σ hfin
    exact rowProcess_perm_eq_of_markovExchangeable_prefixTransportUpTo_and_noNoneAll
      (k := k) μ hμ P hExt hgen i σ
      (htransportUpTo := fun S v N => htransportUpToAll i σ S v N)
      (hnoNoneAll := fun m => hnoNoneAll i m) hfin

theorem fortiniRowExchangeableConcrete_strengthening_generated_at_of_prefixTransportUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (htransportUpToAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hrowInf : ∀ i : Fin k, ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
      P (rowSuccessorValueEvent (k := k) i (σ n) a) =
        P (rowSuccessorValueEvent (k := k) i n a)) ∧
    (∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
      Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
        rowProcessLaw (k := k) P i) := by
  refine ⟨?_, ?_⟩
  · intro i σ n a
    exact rowSuccessorValueEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
      (k := k) μ hμ P hExt i σ n a
      (htransportUpTo := fun S v N => htransportUpToAll i σ S v N)
      (hrowInf := hrowInf i)
  · intro i σ hfin
    exact rowProcess_perm_eq_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
      (k := k) μ hμ P hExt hgen i σ
      (htransportUpTo := fun S v N => htransportUpToAll i σ S v N)
      (hrowInf := hrowInf i) hfin

theorem fortiniRowExchangeableConcrete_strengthening_generated_at_of_carrierEvidenceEquivUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (hcarAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hnoNoneAll :
      ∀ (i : Fin k) (n : ℕ),
        ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) :
    (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
      P (rowSuccessorValueEvent (k := k) i (σ n) a) =
        P (rowSuccessorValueEvent (k := k) i n a)) ∧
    (∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
      Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
        rowProcessLaw (k := k) P i) := by
  refine ⟨?_, ?_⟩
  · intro i σ n a
    exact rowSuccessorValueEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpTo_and_noNoneAll
      (k := k) μ hμ P hExt i σ n a
      (hcarAll := fun S v N => hcarAll i σ S v N)
      (hnoNoneAll := fun m => hnoNoneAll i m)
  · intro i σ hfin
    exact rowProcess_perm_eq_of_markovExchangeable_carrierEvidenceEquivUpTo_and_noNoneAll
      (k := k) μ hμ P hExt hgen i σ
      (hcarAll := fun S v N => hcarAll i σ S v N)
      (hnoNoneAll := fun m => hnoNoneAll i m) hfin

theorem fortiniRowExchangeableConcrete_strengthening_generated_at_of_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (hcarAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hrowInf : ∀ i : Fin k, ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
      P (rowSuccessorValueEvent (k := k) i (σ n) a) =
        P (rowSuccessorValueEvent (k := k) i n a)) ∧
    (∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
      Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
        rowProcessLaw (k := k) P i) := by
  have hvisitAt :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ), RowVisitCylinderInvariantAt (k := k) P i σ := by
    intro i σ
    exact
      rowVisitCylinderInvariantAt_of_markovExchangeable_carrierEvidenceEquivUpToFamily_trans_and_rowInfiniteVisits
        (k := k) μ hμ P hExt i σ (Equiv.refl ℕ)
        (hcarσ := fun S v N => hcarAll i σ S v N)
        (hcarτ := fun S v N =>
          hcarAll i (Equiv.refl ℕ) (S.image σ) (fun m => v (σ.symm m)) N)
        (hrowInf := hrowInf i)
  refine ⟨?_, ?_⟩
  · intro i σ n a
    have hnoPairAE : RowNoNoneOnFinsetAE (k := k) P i ({n, σ n}) :=
      rowNoNoneOnPairAE_of_rowInfiniteVisits (k := k) P i σ n (hrowInf := hrowInf i)
    exact rowSuccessorValueEvent_prob_eq_of_rowVisitInvariant_noNoneAE
      (k := k) (P := P) (i := i) (σ := σ) (hvisit := hvisitAt i σ)
      (n := n) (a := a) hnoPairAE
  · intro i σ hfin
    have hperm :
        ∀ (S : Finset ℕ) (v : ℕ → Fin k),
          rowProcessLaw (k := k) P i
            (rowFiniteCylinder (k := k) (S.image σ) (fun m => v (σ.symm m))) =
          rowProcessLaw (k := k) P i (rowFiniteCylinder (k := k) S v) := by
      intro S v
      exact rowProcessLaw_perm_cylinder_of_rowVisitInvariant
        (k := k) P i σ (hvisit := hvisitAt i σ) S v
    exact rowProcessLaw_perm_eq_of_generateFrom (k := k) P hfin i σ hgen hperm

theorem singleton_rowVisitCylinderEvent_perm_eq_of_fortiniRowExchangeableConcrete_generated
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (hvisitAll :
      ∀ (P : Measure (ℕ → Fin k)), RowVisitCylinderInvariantAll (k := k) P)
    (hnoNoneAll :
      ∀ (P : Measure (ℕ → Fin k)) (i : Fin k) (n : ℕ),
        ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) :
    ∀ (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
      P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
        P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i)) := by
  have hstrength :=
    fortiniRowExchangeableConcrete_strengthening_generated
      (k := k) μ hμ hgen hvisitAll hnoNoneAll
  rcases hstrength with ⟨_, hsingle, _⟩
  intro P i σ n a
  have hEq := hsingle P i σ n a
  have hleft :
      rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i) =
        rowSuccessorValueEvent (k := k) i (σ n) a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent]
  have hright :
      rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i) =
        rowSuccessorValueEvent (k := k) i n a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent]
  simpa [hleft, hright] using hEq

theorem singleton_rowVisitCylinderEvent_perm_eq_of_fortiniRowExchangeableConcrete_generated_of_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (hvisitAll :
      ∀ (P : Measure (ℕ → Fin k)), RowVisitCylinderInvariantAll (k := k) P)
    (hrowInfAll :
      ∀ (P : Measure (ℕ → Fin k)) (i : Fin k),
        ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    ∀ (P : Measure (ℕ → Fin k)) (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
      P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
        P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i)) := by
  have hstrength :=
    fortiniRowExchangeableConcrete_strengthening_generated_of_rowInfiniteVisits
      (k := k) μ hμ hgen hvisitAll hrowInfAll
  rcases hstrength with ⟨_, hsingle, _⟩
  intro P i σ n a
  exact singleton_rowVisitCylinderEvent_prob_eq_of_rowVisitInvariant_noNoneAE
    (k := k) (P := P) (i := i) (σ := σ) (n := n) (a := a)
    (hvisit := hvisitAll P i σ)
    (hnoPairAE := rowNoNoneOnPairAE_of_rowInfiniteVisits (k := k) P i σ n (hrowInfAll P i))

theorem singleton_rowVisitCylinderEvent_perm_eq_of_fortiniRowExchangeableConcrete_generated_at_of_prefixTransportUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (htransportUpToAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hnoNoneAll :
      ∀ (i : Fin k) (n : ℕ),
        ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) :
    ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
      P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
        P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i)) := by
  have hstrength :=
    fortiniRowExchangeableConcrete_strengthening_generated_at_of_prefixTransportUpTo
      (k := k) μ hμ P hExt hgen htransportUpToAll hnoNoneAll
  rcases hstrength with ⟨hsingle, _⟩
  intro i σ n a
  have hEq := hsingle i σ n a
  have hleft :
      rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i) =
        rowSuccessorValueEvent (k := k) i (σ n) a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent]
  have hright :
      rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i) =
        rowSuccessorValueEvent (k := k) i n a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent]
  simpa [hleft, hright] using hEq

theorem singleton_rowVisitCylinderEvent_perm_eq_of_fortiniRowExchangeableConcrete_generated_at_of_prefixTransportUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (htransportUpToAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)
    (hrowInf : ∀ i : Fin k, ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
      P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
        P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i)) := by
  have hstrength :=
    fortiniRowExchangeableConcrete_strengthening_generated_at_of_prefixTransportUpTo_and_rowInfiniteVisits
      (k := k) μ hμ P hExt hgen htransportUpToAll hrowInf
  rcases hstrength with ⟨hsingle, _⟩
  intro i σ n a
  have hEq := hsingle i σ n a
  have hleft :
      rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i) =
        rowSuccessorValueEvent (k := k) i (σ n) a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent]
  have hright :
      rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i) =
        rowSuccessorValueEvent (k := k) i n a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent]
  simpa [hleft, hright] using hEq

theorem singleton_rowVisitCylinderEvent_perm_eq_of_fortiniRowExchangeableConcrete_generated_at_of_carrierEvidenceEquivUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (hcarAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hnoNoneAll :
      ∀ (i : Fin k) (n : ℕ),
        ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) :
    ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
      P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
        P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i)) := by
  have hstrength :=
    fortiniRowExchangeableConcrete_strengthening_generated_at_of_carrierEvidenceEquivUpTo
      (k := k) μ hμ P hExt hgen hcarAll hnoNoneAll
  rcases hstrength with ⟨hsingle, _⟩
  intro i σ n a
  have hEq := hsingle i σ n a
  have hleft :
      rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i) =
        rowSuccessorValueEvent (k := k) i (σ n) a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent]
  have hright :
      rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i) =
        rowSuccessorValueEvent (k := k) i n a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent]
  simpa [hleft, hright] using hEq

theorem singleton_rowVisitCylinderEvent_perm_eq_of_fortiniRowExchangeableConcrete_generated_at_of_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (P : Measure (ℕ → Fin k))
    (hExt : ∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs))
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (hcarAll :
      ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
        RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)
    (hrowInf : ∀ i : Fin k, ∀ᵐ ω ∂P, Set.Infinite {t : ℕ | ω t = i}) :
    ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
      P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
        P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i)) := by
  have hstrength :=
    fortiniRowExchangeableConcrete_strengthening_generated_at_of_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
      (k := k) μ hμ P hExt hgen hcarAll hrowInf
  rcases hstrength with ⟨hsingle, _⟩
  intro i σ n a
  have hEq := hsingle i σ n a
  have hleft :
      rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i) =
        rowSuccessorValueEvent (k := k) i (σ n) a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent]
  have hright :
      rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i) =
        rowSuccessorValueEvent (k := k) i n a := by
    ext ω
    simp [rowVisitCylinderEvent, rowSuccessorValueEvent]
  simpa [hleft, hright] using hEq

/-- Concrete Fortini strong-row-recurrence placeholder aligned with current
recurrence interface. -/
def FortiniStrongRowRecurrentConcrete (μ : FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  MarkovRecurrentPrefixMeasure (k := k) μ

/-- Strengthened row-wise recurrence interface for the Fortini path. -/
def FortiniStrongRowRecurrentConcreteRow
    (μ : FiniteAlphabet.PrefixMeasure (Fin k)) : Prop :=
  MarkovRowRecurrentPrefixMeasure (k := k) μ

/-- Row-wise recurrence package with explicit a.e. no-`none` visit-time
consequence for all anchors and indices. -/
lemma ae_nthVisitTime_ne_none_of_fortiniStrongRowRecurrentConcreteRow
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hrec : FortiniStrongRowRecurrentConcreteRow (k := k) μ) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ i : Fin k, ∀ n : ℕ, ∀ᵐ ω ∂P, nthVisitTime (k := k) ω i n ≠ none) := by
  exact ae_nthVisitTime_ne_none_of_markovRowRecurrentPrefixMeasure (k := k) μ hrec

theorem exists_extension_singleton_rowVisitCylinderEvent_perm_eq_of_fortiniStrongRowRecurrentConcreteRow
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hrec : FortiniStrongRowRecurrentConcreteRow (k := k) μ) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      ((∀ (i : Fin k) (σ : Equiv.Perm ℕ), RowVisitCylinderInvariantAt (k := k) P i σ) →
        ∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
          P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
            P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i))) := by
  rcases hrec with ⟨P, hPprob, hrep, hrowInf⟩
  refine ⟨P, hPprob, hrep, ?_⟩
  intro hvisitAll i σ n a
  exact singleton_rowVisitCylinderEvent_prob_eq_of_rowVisitInvariant_rowInfiniteVisits
    (k := k) (P := P) (i := i) (σ := σ) (n := n) (a := a)
    (hvisit := hvisitAll i σ) (hrowInf := hrowInf i)

theorem exists_extension_singleton_rowVisitCylinderEvent_perm_eq_of_markovExchangeable_rowRecurrent_and_carrierEvidenceEquivUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrowRec : MarkovRowRecurrentPrefixMeasure (k := k) μ)
    (hcarExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
          P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i))) := by
  rcases hrowRec with ⟨P, hPprob, hExt, hrowInf⟩
  refine ⟨P, hPprob, hExt, ?_⟩
  intro i σ n a
  exact singleton_rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
    (k := k) μ hμ P hExt i σ n a
    (hcarAll := fun S v N => hcarExt P hPprob hExt i σ S v N)
    (hrowInf := hrowInf i)

theorem exists_extension_singleton_rowVisitCylinderEvent_refl_eq_of_markovExchangeable_rowRecurrent_and_carrierEvidenceEquivUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrowRec : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (n : ℕ) (a : Fin k),
        P (rowVisitCylinderEvent (k := k) i {(Equiv.refl ℕ) n}
            (fun m => if m = (Equiv.refl ℕ) n then a else i)) =
          P (rowVisitCylinderEvent (k := k) i {n}
            (fun m => if m = n then a else i))) := by
  rcases hrowRec with ⟨P, hPprob, hExt, hrowInf⟩
  refine ⟨P, hPprob, hExt, ?_⟩
  intro i n a
  exact
    rowVisitCylinderEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpToFamily_refl_and_rowInfiniteVisits
      (k := k) μ hμ P hExt i ({n} : Finset ℕ) (fun m => if m = n then a else i)
      (hrowInf := hrowInf i)

theorem exists_extension_rowVisitCylinderEvent_perm_eq_of_markovExchangeable_rowRecurrent_and_fixed
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrowRec : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k),
        S.image σ = S →
        (∀ n ∈ S, v (σ.symm n) = v n) →
        P (rowVisitCylinderEvent (k := k) i (S.image σ) (fun m => v (σ.symm m))) =
          P (rowVisitCylinderEvent (k := k) i S v)) := by
  rcases hrowRec with ⟨P, hPprob, hExt, hrowInf⟩
  refine ⟨P, hPprob, hExt, ?_⟩
  intro i σ S v hS hv
  exact rowVisitCylinderEvent_prob_eq_of_fixed_and_rowInfiniteVisits
    (k := k) μ hμ P hExt i σ S v hS hv (hrowInf := hrowInf i)

theorem exists_extension_rowVisitCylinderEvent_swap_pair_perm_eq_of_markovExchangeable_rowRecurrent_and_carrierEvidenceEquivUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrowRec : MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (a b : ℕ) (v : ℕ → Fin k), v a = v b →
        P (rowVisitCylinderEvent (k := k) i
              (({a, b} : Finset ℕ).image (Equiv.swap a b))
              (fun m => v ((Equiv.swap a b).symm m))) =
          P (rowVisitCylinderEvent (k := k) i ({a, b} : Finset ℕ) v)) := by
  rcases
    exists_extension_rowVisitCylinderEvent_perm_eq_of_markovExchangeable_rowRecurrent_and_fixed
      (k := k) μ hμ hrowRec with ⟨P, hPprob, hExt, hfixed⟩
  refine ⟨P, hPprob, hExt, ?_⟩
  intro i a b v hvb
  exact hfixed i (Equiv.swap a b) ({a, b} : Finset ℕ) v
    (by simpa using image_swap_pair (a := a) (b := b))
    (by
      intro n hn
      simp at hn
      rcases hn with rfl | rfl <;> simp [hvb])

theorem exists_extension_singleton_rowVisitCylinderEvent_perm_eq_of_markovExchangeable_rowRecurrent_and_prefixTransportUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrowRec : MarkovRowRecurrentPrefixMeasure (k := k) μ)
    (htransportExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
          P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i))) := by
  rcases hrowRec with ⟨P, hPprob, hExt, hrowInf⟩
  refine ⟨P, hPprob, hExt, ?_⟩
  intro i σ n a
  exact singleton_rowVisitCylinderEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
    (k := k) μ hμ P hExt i σ n a
    (htransportUpTo := fun S v N => htransportExt P hPprob hExt i σ S v N)
    (hrowInf := hrowInf i)

theorem exists_extension_singleton_rowVisitCylinderEvent_perm_eq_of_fortiniConcrete_rowRecurrent_and_carrierEvidenceEquivUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (hrowRec : FortiniStrongRowRecurrentConcreteRow (k := k) μ)
    (hcarExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
          P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i))) := by
  exact exists_extension_singleton_rowVisitCylinderEvent_perm_eq_of_markovExchangeable_rowRecurrent_and_carrierEvidenceEquivUpTo
    (k := k) μ hμ hrowRec hcarExt

theorem exists_extension_singleton_rowVisitCylinderEvent_perm_eq_of_fortiniConcrete_rowRecurrent_and_prefixTransportUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (hrowRec : FortiniStrongRowRecurrentConcreteRow (k := k) μ)
    (htransportExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowVisitCylinderEvent (k := k) i {σ n} (fun m => if m = σ n then a else i)) =
          P (rowVisitCylinderEvent (k := k) i {n} (fun m => if m = n then a else i))) := by
  exact exists_extension_singleton_rowVisitCylinderEvent_perm_eq_of_markovExchangeable_rowRecurrent_and_prefixTransportUpTo
    (k := k) μ hμ hrowRec htransportExt

theorem exists_extension_rowVisitInvariantAll_of_fortiniConcrete_rowRecurrent_and_carrierEvidenceEquivUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (hrowRec : FortiniStrongRowRecurrentConcreteRow (k := k) μ)
    (hcarExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      RowVisitCylinderInvariantAll (k := k) P := by
  exact exists_extension_rowVisitInvariantAll_of_markovExchangeable_rowRecurrent_and_carrierEvidenceEquivUpTo
    (k := k) μ hμ hrowRec hcarExt

theorem exists_extension_rowVisitInvariantAll_of_fortiniConcrete_rowRecurrent_and_prefixTransportUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (hrowRec : FortiniStrongRowRecurrentConcreteRow (k := k) μ)
    (htransportExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      RowVisitCylinderInvariantAll (k := k) P := by
  exact exists_extension_rowVisitInvariantAll_of_markovExchangeable_rowRecurrent_and_prefixTransportUpTo
    (k := k) μ hμ hrowRec htransportExt

theorem exists_extension_rowSuccessorValueEvent_perm_eq_of_markovExchangeable_rowRecurrent_and_carrierEvidenceEquivUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrowRec : MarkovRowRecurrentPrefixMeasure (k := k) μ)
    (hcarExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowSuccessorValueEvent (k := k) i (σ n) a) =
          P (rowSuccessorValueEvent (k := k) i n a)) := by
  rcases hrowRec with ⟨P, hPprob, hExt, hrowInf⟩
  refine ⟨P, hPprob, hExt, ?_⟩
  intro i σ n a
  exact rowSuccessorValueEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
    (k := k) μ hμ P hExt i σ n a
    (hcarAll := fun S v N => hcarExt P hPprob hExt i σ S v N)
    (hrowInf := hrowInf i)

theorem exists_extension_rowSuccessorValueEvent_perm_eq_of_markovExchangeable_rowRecurrent_and_prefixTransportUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrowRec : MarkovRowRecurrentPrefixMeasure (k := k) μ)
    (htransportExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowSuccessorValueEvent (k := k) i (σ n) a) =
          P (rowSuccessorValueEvent (k := k) i n a)) := by
  rcases hrowRec with ⟨P, hPprob, hExt, hrowInf⟩
  refine ⟨P, hPprob, hExt, ?_⟩
  intro i σ n a
  exact rowSuccessorValueEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
    (k := k) μ hμ P hExt i σ n a
    (htransportUpTo := fun S v N => htransportExt P hPprob hExt i σ S v N)
    (hrowInf := hrowInf i)

theorem exists_extension_rowSuccessorValueEvent_perm_eq_of_fortiniConcrete_rowRecurrent_and_carrierEvidenceEquivUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (hrowRec : FortiniStrongRowRecurrentConcreteRow (k := k) μ)
    (hcarExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowSuccessorValueEvent (k := k) i (σ n) a) =
          P (rowSuccessorValueEvent (k := k) i n a)) := by
  exact exists_extension_rowSuccessorValueEvent_perm_eq_of_markovExchangeable_rowRecurrent_and_carrierEvidenceEquivUpTo
    (k := k) μ hμ hrowRec hcarExt

theorem exists_extension_rowSuccessorValueEvent_perm_eq_of_fortiniConcrete_rowRecurrent_and_prefixTransportUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (hrowRec : FortiniStrongRowRecurrentConcreteRow (k := k) μ)
    (htransportExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowSuccessorValueEvent (k := k) i (σ n) a) =
          P (rowSuccessorValueEvent (k := k) i n a)) := by
  exact exists_extension_rowSuccessorValueEvent_perm_eq_of_markovExchangeable_rowRecurrent_and_prefixTransportUpTo
    (k := k) μ hμ hrowRec htransportExt

theorem exists_extension_rowSuccessorValueEvent_and_rowProcess_perm_eq_of_markovExchangeable_rowRecurrent_and_carrierEvidenceEquivUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrowRec : MarkovRowRecurrentPrefixMeasure (k := k) μ)
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (hcarExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowSuccessorValueEvent (k := k) i (σ n) a) =
          P (rowSuccessorValueEvent (k := k) i n a)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
        Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
          rowProcessLaw (k := k) P i) := by
  rcases hrowRec with ⟨P, hPprob, hExt, hrowInf⟩
  refine ⟨P, hPprob, hExt, ?_, ?_⟩
  · intro i σ n a
    exact rowSuccessorValueEvent_prob_eq_of_markovExchangeable_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
      (k := k) μ hμ P hExt i σ n a
      (hcarAll := fun S v N => hcarExt P hPprob hExt i σ S v N)
      (hrowInf := hrowInf i)
  · intro i σ hfin
    exact rowProcess_perm_eq_of_markovExchangeable_carrierEvidenceEquivUpTo_and_rowInfiniteVisits
      (k := k) μ hμ P hExt hgen i σ
      (hcarAll := fun S v N => hcarExt P hPprob hExt i σ S v N)
      (hrowInf := hrowInf i) hfin

theorem exists_extension_rowSuccessorValueEvent_and_rowProcess_perm_eq_of_fortiniConcrete_rowRecurrent_and_carrierEvidenceEquivUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (hrowRec : FortiniStrongRowRecurrentConcreteRow (k := k) μ)
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (hcarExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowSuccessorValueEvent (k := k) i (σ n) a) =
          P (rowSuccessorValueEvent (k := k) i n a)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
        Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
          rowProcessLaw (k := k) P i) := by
  exact exists_extension_rowSuccessorValueEvent_and_rowProcess_perm_eq_of_markovExchangeable_rowRecurrent_and_carrierEvidenceEquivUpTo
    (k := k) μ hμ hrowRec hgen hcarExt

theorem exists_extension_rowSuccessorValueEvent_and_rowProcess_perm_eq_of_markovExchangeable_rowRecurrent_and_prefixTransportUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrowRec : MarkovRowRecurrentPrefixMeasure (k := k) μ)
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (htransportExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowSuccessorValueEvent (k := k) i (σ n) a) =
          P (rowSuccessorValueEvent (k := k) i n a)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
        Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
          rowProcessLaw (k := k) P i) := by
  rcases hrowRec with ⟨P, hPprob, hExt, hrowInf⟩
  refine ⟨P, hPprob, hExt, ?_, ?_⟩
  · intro i σ n a
    exact rowSuccessorValueEvent_prob_eq_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
      (k := k) μ hμ P hExt i σ n a
      (htransportUpTo := fun S v N => htransportExt P hPprob hExt i σ S v N)
      (hrowInf := hrowInf i)
  · intro i σ hfin
    exact rowProcess_perm_eq_of_markovExchangeable_prefixTransportUpTo_and_rowInfiniteVisits
      (k := k) μ hμ P hExt hgen i σ
      (htransportUpTo := fun S v N => htransportExt P hPprob hExt i σ S v N)
      (hrowInf := hrowInf i) hfin

theorem exists_extension_rowSuccessorValueEvent_and_rowProcess_perm_eq_of_fortiniConcrete_rowRecurrent_and_prefixTransportUpTo
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : FortiniRowExchangeableConcrete (k := k) μ)
    (hrowRec : FortiniStrongRowRecurrentConcreteRow (k := k) μ)
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (htransportExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderPrefixTransportUpToAt (k := k) P i σ N S v)) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowSuccessorValueEvent (k := k) i (σ n) a) =
          P (rowSuccessorValueEvent (k := k) i n a)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
        Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
          rowProcessLaw (k := k) P i) := by
  exact exists_extension_rowSuccessorValueEvent_and_rowProcess_perm_eq_of_markovExchangeable_rowRecurrent_and_prefixTransportUpTo
    (k := k) μ hμ hrowRec hgen htransportExt

/-- Row-wise recurrence implies `(n+1)`-st visit-time existence almost surely
for each anchor `i` and visit index `n`. -/
lemma nthVisitTimeExists_ae_of_fortiniStrongRowRecurrentConcreteRow
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hrec : FortiniStrongRowRecurrentConcreteRow (k := k) μ) :
    ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ i : Fin k, ∀ n : ℕ, ∀ᵐ ω ∂P, nthVisitTimeExists (k := k) ω i n) := by
  rcases hrec with ⟨P, hPprob, hrep, hrow⟩
  refine ⟨P, hPprob, hrep, ?_⟩
  intro i n
  exact (hrow i).mono (fun ω hω =>
    nthVisitTimeExists_of_strongRowRecurrentAt (k := k) ω i n (by
      simpa [strongRowRecurrentAt, visitSet] using hω))

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

/-! ### Explicit Fortini crux interface: successor-matrix invariance ⇒ mixture -/

/-- Fortini successor-matrix invariance theorem (explicit interface):
from a concrete extension `P` with row-successor invariance and row-process
permutation invariance, derive the Markov mixture representation. -/
def FortiniSuccessorMatrixInvarianceTheorem (k : ℕ) : Prop :=
  ∀ μ : FiniteAlphabet.PrefixMeasure (Fin k),
    (∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
      (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
        P (rowSuccessorValueEvent (k := k) i (σ n) a) =
          P (rowSuccessorValueEvent (k := k) i n a)) ∧
      (∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
        Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
          rowProcessLaw (k := k) P i)) →
      ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
        ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi

/-- Chaining lemma: carrier-evidence route + successor-matrix invariance
implies the concrete Fortini mixture theorem, without new wrappers. -/
theorem fortiniConcreteTheorem_of_markovExchangeable_rowRecurrent_and_carrierEvidenceEquivUpTo
    (hTheorem : FortiniSuccessorMatrixInvarianceTheorem k)
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrowRec : MarkovRowRecurrentPrefixMeasure (k := k) μ)
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (hcarExt :
      ∀ (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v)) :
    ∃ (pi : Measure (MarkovParam k)), IsProbabilityMeasure pi ∧
      ∀ xs : List (Fin k), μ xs = ∫⁻ θ, wordProb (k := k) θ xs ∂pi := by
  have hsucc :
      ∃ (P : Measure (ℕ → Fin k)), IsProbabilityMeasure P ∧
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) ∧
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (n : ℕ) (a : Fin k),
          P (rowSuccessorValueEvent (k := k) i (σ n) a) =
            P (rowSuccessorValueEvent (k := k) i n a)) ∧
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ), IsFiniteMeasure P →
          Measure.map (rowPermute (k := k) σ) (rowProcessLaw (k := k) P i) =
            rowProcessLaw (k := k) P i) :=
    exists_extension_rowSuccessorValueEvent_and_rowProcess_perm_eq_of_markovExchangeable_rowRecurrent_and_carrierEvidenceEquivUpTo
      (k := k) μ hμ hrowRec hgen hcarExt
  exact hTheorem μ hsucc

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
  from_markovExchangeable := by intro _ h; exact h
  from_markovRecurrent := by intro _ h; exact h

def fortiniPackage_of_successorMatrixInvariance_with_rowRecLift
    (hTheorem : FortiniSuccessorMatrixInvarianceTheorem k)
    (hgen :
      (inferInstance : MeasurableSpace (ℕ → Fin k)) =
        MeasurableSpace.generateFrom (rowFiniteCylinderSets k))
    (hcarExt :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k)) (P : Measure (ℕ → Fin k)),
        IsProbabilityMeasure P →
        (∀ xs : List (Fin k), μ xs = P (cylinder (k := k) xs)) →
        (∀ (i : Fin k) (σ : Equiv.Perm ℕ) (S : Finset ℕ) (v : ℕ → Fin k) (N : ℕ),
          RowVisitCylinderUpToCarrierEvidenceEquivAt (k := k) i σ N S v))
    (hrowRec_to_row :
      ∀ (μ : FiniteAlphabet.PrefixMeasure (Fin k)),
        FortiniStrongRowRecurrentConcrete (k := k) μ →
          MarkovRowRecurrentPrefixMeasure (k := k) μ) :
    FortiniSuccessorMatrixPackage k := by
  -- Use the newly isolated crux to build the concrete theorem.
  refine fortiniPackage_of_concreteTheorem (k := k) ?_
  intro μ hμ hrowRec
  exact
    fortiniConcreteTheorem_of_markovExchangeable_rowRecurrent_and_carrierEvidenceEquivUpTo
      (k := k) hTheorem μ hμ (hrowRec_to_row μ hrowRec) hgen
        (fun P hP hrep => hcarExt μ P hP hrep)

theorem anchorInvariant_of_fortiniPackage
    (pkg : FortiniSuccessorMatrixPackage k) :
    AnchorInvariantSuccessorMatrixTheorem k := by
  intro μ hμ hrec
  exact pkg.theorem_of_rows μ
    (pkg.from_markovExchangeable μ hμ)
    (pkg.from_markovRecurrent μ hrec)

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
