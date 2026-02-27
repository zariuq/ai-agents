import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCrux

noncomputable section

namespace Mettapedia.Logic
namespace MarkovDeFinettiHard

open MeasureTheory

namespace FortiniCrossCounterexample

abbrev S : Type := Fin 2

def s0 : S := ⟨0, by decide⟩
def s1 : S := ⟨1, by decide⟩

def pathA : ℕ → S := fun _ => s0

def pathB : ℕ → S := fun n => if n % 2 = 0 then s0 else s1

def Pmix : Measure (ℕ → S) :=
  ((1 / 2 : ENNReal) • Measure.dirac pathA) + ((1 / 2 : ENNReal) • Measure.dirac pathB)

def badRowKernel (i : S) (r : ℕ → S) : ProbabilityMeasure S :=
  if _hi : i = s0 then
    ⟨Measure.dirac (r 0), Measure.dirac.isProbabilityMeasure⟩
  else
    ⟨Measure.dirac (if r 0 = s0 then s1 else s0), Measure.dirac.isProbabilityMeasure⟩

lemma measurable_badRowKernel_eval (i b : S) :
    Measurable (fun r : ℕ → S => (badRowKernel i r : Measure S) ({b} : Set S)) := by
  by_cases hi : i = s0
  · subst hi
    let A : Set (ℕ → S) := {r : ℕ → S | r 0 = b}
    have hA : MeasurableSet A := by
      exact measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
    have hEq :
        (fun r : ℕ → S => (badRowKernel s0 r : Measure S) ({b} : Set S))
          = A.indicator (fun _ => (1 : ENNReal)) := by
      funext r
      simp [badRowKernel, A, Set.indicator, Set.mem_setOf_eq, Measure.dirac_apply']
    rw [hEq]
    exact measurable_const.indicator hA
  · have hEq :
        (fun r : ℕ → S => (badRowKernel i r : Measure S) ({b} : Set S))
          =
        ({r : ℕ → S | (if r 0 = s0 then s1 else s0) = b}).indicator (fun _ => (1 : ENNReal)) := by
      funext r
      simp [badRowKernel, hi, Set.indicator, Set.mem_setOf_eq, Measure.dirac_apply']
    have hset :
        MeasurableSet {r : ℕ → S | (if r 0 = s0 then s1 else s0) = b} := by
      have hpred : MeasurableSet {r : ℕ → S | r 0 = s0} := by
        exact measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
      have hfun : Measurable (fun r : ℕ → S => if r 0 = s0 then s1 else s0) :=
        Measurable.ite hpred measurable_const measurable_const
      exact measurableSet_eq_fun hfun measurable_const
    rw [hEq]
    exact measurable_const.indicator hset

lemma hEval_badRowKernel_Pmix :
    ∀ i : S, ∀ b : S,
      AEMeasurable
        (fun r : ℕ → S => (badRowKernel i r : Measure S) ({b} : Set S))
        (rowProcessLaw (k := 2) Pmix i) := by
  intro i b
  exact (measurable_badRowKernel_eval i b).aemeasurable

lemma pathA_start : pathA 0 = s0 := by rfl

lemma pathB_start : pathB 0 = s0 := by
  simp [pathB]

lemma pathB_one : pathB 1 = s1 := by
  simp [pathB]

lemma pathB_two : pathB 2 = s0 := by
  simp [pathB]


lemma rowSucc00_pathA :
    rowSuccessorAtNthVisit (k := 2) s0 0 pathA = s0 := by
  have h0 : pathA 0 = s0 := pathA_start
  calc
    rowSuccessorAtNthVisit (k := 2) s0 0 pathA
        = successorAt (k := 2) pathA 0 := by
            exact rowSuccessorAtNthVisit_zero_eq_successor_of_start (k := 2) pathA s0 h0
    _ = s0 := by simp [successorAt, pathA]

lemma rowSucc10_pathB :
    rowSuccessorAtNthVisit (k := 2) s1 0 pathB = s0 := by
  have hvisit : isNthVisitTime (k := 2) pathB s1 0 1 := by
    refine ⟨?_, ?_⟩
    · exact pathB_one
    · simp [visitCountBefore, pathB]
  have htime : nthVisitTime (k := 2) pathB s1 0 = some 1 := by
    exact (nthVisitTime_eq_some_iff (k := 2) pathB s1 0 1).2 hvisit
  calc
    rowSuccessorAtNthVisit (k := 2) s1 0 pathB
        = successorAt (k := 2) pathB 1 := by
            simp [rowSuccessorAtNthVisit, htime]
    _ = s0 := by
          simp [successorAt, pathB]

lemma rowSucc00_pathB :
    rowSuccessorAtNthVisit (k := 2) s0 0 pathB = s1 := by
  have h0 : pathB 0 = s0 := pathB_start
  calc
    rowSuccessorAtNthVisit (k := 2) s0 0 pathB
        = successorAt (k := 2) pathB 0 := by
            exact rowSuccessorAtNthVisit_zero_eq_successor_of_start (k := 2) pathB s0 h0
    _ = s1 := by
          simp [successorAt, pathB]

lemma stepProd_010_pathA :
    rowKernelStepProd (k := 2) badRowKernel pathA [s0, s1, s0] = 0 := by
  have h0 :
      ((badRowKernel s0 (rowSuccessorVisitProcess (k := 2) s0 pathA) : Measure S)
        ({s1} : Set S)) = 0 := by
    have hr0 : rowSuccessorVisitProcess (k := 2) s0 pathA 0 = s0 := by
      simpa [rowSuccessorVisitProcess] using rowSucc00_pathA
    have hdirac :
        ((badRowKernel s0 (rowSuccessorVisitProcess (k := 2) s0 pathA) : Measure S)
          ({s1} : Set S))
          =
        (Measure.dirac (rowSuccessorVisitProcess (k := 2) s0 pathA 0) ({s1} : Set S)) := by
      simp [badRowKernel, s0]
    rw [hdirac, hr0]
    simp [s0, s1]
  calc
    rowKernelStepProd (k := 2) badRowKernel pathA [s0, s1, s0]
        = ((badRowKernel s0 (rowSuccessorVisitProcess (k := 2) s0 pathA) : Measure S)
            ({s1} : Set S)) *
          rowKernelStepProd (k := 2) badRowKernel pathA [s1, s0] := by
            simp [rowKernelStepProd]
    _ = 0 := by simp [h0]

lemma stepProd_010_pathB :
    rowKernelStepProd (k := 2) badRowKernel pathB [s0, s1, s0] = 0 := by
  have hfirst :
      ((badRowKernel s0 (rowSuccessorVisitProcess (k := 2) s0 pathB) : Measure S)
        ({s1} : Set S)) = 1 := by
    have hr0 : rowSuccessorVisitProcess (k := 2) s0 pathB 0 = s1 := by
      simpa [rowSuccessorVisitProcess] using rowSucc00_pathB
    have hdirac :
        ((badRowKernel s0 (rowSuccessorVisitProcess (k := 2) s0 pathB) : Measure S)
          ({s1} : Set S))
          =
        (Measure.dirac (rowSuccessorVisitProcess (k := 2) s0 pathB 0) ({s1} : Set S)) := by
      simp [badRowKernel, s0]
    rw [hdirac, hr0]
    simp [s1]
  have h1 :
      ((badRowKernel s1 (rowSuccessorVisitProcess (k := 2) s1 pathB) : Measure S)
        ({s0} : Set S)) = 0 := by
    have hr0 : rowSuccessorVisitProcess (k := 2) s1 pathB 0 = s0 := by
      simpa [rowSuccessorVisitProcess] using rowSucc10_pathB
    have hs1ne : s1 ≠ s0 := by decide
    have hdirac :
        ((badRowKernel s1 (rowSuccessorVisitProcess (k := 2) s1 pathB) : Measure S)
          ({s0} : Set S))
          =
        (Measure.dirac
            (if rowSuccessorVisitProcess (k := 2) s1 pathB 0 = s0 then s1 else s0)
            ({s0} : Set S)) := by
      simp [badRowKernel, hs1ne]
    rw [hdirac, hr0]
    simp [s0, s1]
  calc
    rowKernelStepProd (k := 2) badRowKernel pathB [s0, s1, s0]
        = ((badRowKernel s0 (rowSuccessorVisitProcess (k := 2) s0 pathB) : Measure S)
            ({s1} : Set S)) *
          (((badRowKernel s1 (rowSuccessorVisitProcess (k := 2) s1 pathB) : Measure S)
            ({s0} : Set S)) *
            rowKernelStepProd (k := 2) badRowKernel pathB [s0]) := by
              simp [rowKernelStepProd]
    _ = 0 := by simp [hfirst, h1]

lemma mem_cyl_010_pathA :
    pathA ∉ MarkovDeFinettiRecurrence.cylinder (k := 2) [s0, s1, s0] := by
  intro h
  have h1 : pathA 1 = s1 := by
    exact Set.mem_iInter.mp h ⟨1, by decide⟩
  simp [pathA, s0, s1] at h1

lemma mem_cyl_010_pathB :
    pathB ∈ MarkovDeFinettiRecurrence.cylinder (k := 2) [s0, s1, s0] := by
  refine Set.mem_iInter.mpr ?_
  intro i
  fin_cases i <;> simp [pathB]

lemma Pmix_cyl_010 :
    Pmix (MarkovDeFinettiRecurrence.cylinder (k := 2) [s0, s1, s0]) = (1 / 2 : ENNReal) := by
  let C : Set (ℕ → S) := MarkovDeFinettiRecurrence.cylinder (k := 2) [s0, s1, s0]
  have hC : MeasurableSet C := measurableSet_cylinder (k := 2) [s0, s1, s0]
  have hA : (Measure.dirac pathA) C = 0 := by
    simp [C, mem_cyl_010_pathA]
  have hB : (Measure.dirac pathB) C = 1 := by
    simp [C, mem_cyl_010_pathB]
  calc
    Pmix C
        = ((1 / 2 : ENNReal) • Measure.dirac pathA) C +
          ((1 / 2 : ENNReal) • Measure.dirac pathB) C := by
            simp [Pmix, Measure.add_apply, hC]
    _ = (1 / 2 : ENNReal) * (Measure.dirac pathA C) +
          (1 / 2 : ENNReal) * (Measure.dirac pathB C) := by
            simp [Measure.smul_apply, hC]
    _ = (1 / 2 : ENNReal) := by simp [hA, hB]

lemma Pmix_rhs_010 :
    (∫⁻ ω,
      (if ω 0 = s0 then rowKernelStepProd (k := 2) badRowKernel ω [s0, s1, s0] else 0) ∂Pmix)
      = 0 := by
  let f : (ℕ → S) → ENNReal := fun ω =>
    if ω 0 = s0 then rowKernelStepProd (k := 2) badRowKernel ω [s0, s1, s0] else 0
  have hfA : f pathA = 0 := by
    simp [f, pathA_start, stepProd_010_pathA]
  have hfB : f pathB = 0 := by
    simp [f, pathB_start, stepProd_010_pathB]
  calc
    (∫⁻ ω, f ω ∂Pmix)
        = (∫⁻ ω, f ω ∂(((1 / 2 : ENNReal) • Measure.dirac pathA))) +
          (∫⁻ ω, f ω ∂(((1 / 2 : ENNReal) • Measure.dirac pathB))) := by
            simp [Pmix, lintegral_add_measure]
    _ = (1 / 2 : ENNReal) * (∫⁻ ω, f ω ∂(Measure.dirac pathA)) +
          (1 / 2 : ENNReal) * (∫⁻ ω, f ω ∂(Measure.dirac pathB)) := by
            simp [lintegral_smul_measure]
    _ = 0 := by simp [hfA, hfB]

theorem not_crossAnchorProductIdentity_badRowKernel :
    ¬ CrossAnchorProductIdentity (k := 2) Pmix badRowKernel := by
  intro hcross
  have hspec := hcross s0 s1 [s0]
  have hL : Pmix (MarkovDeFinettiRecurrence.cylinder (k := 2) [s0, s1, s0]) = (1 / 2 : ENNReal) :=
    Pmix_cyl_010
  have hR :
      (∫⁻ ω,
        (if ω 0 = s0 then rowKernelStepProd (k := 2) badRowKernel ω [s0, s1, s0] else 0) ∂Pmix)
      = 0 :=
    Pmix_rhs_010
  have hhalf : (1 / 2 : ENNReal) = 0 := by
    calc
      (1 / 2 : ENNReal)
          = Pmix (MarkovDeFinettiRecurrence.cylinder (k := 2) [s0, s1, s0]) := hL.symm
      _ = (∫⁻ ω,
            (if ω 0 = s0 then rowKernelStepProd (k := 2) badRowKernel ω [s0, s1, s0] else 0) ∂Pmix) := hspec
      _ = 0 := hR
  exact (by norm_num : (1 / 2 : ENNReal) ≠ 0) hhalf

/-! ## Finite-prefix carrier mismatch witness (k = 2, i = 0, b = 1, N = 2) -/

noncomputable abbrev carrier_n1_N2 : Finset (Fin 3 → S) :=
  rowVisitCylinderEventUpToPrefixCarrier (k := 2) s0 {1}
    (fun m => if m = 1 then s1 else s0) 2

noncomputable abbrev carrier_n0_N2 : Finset (Fin 3 → S) :=
  rowVisitCylinderEventUpToPrefixCarrier (k := 2) s0 {0}
    (fun m => if m = 0 then s1 else s0) 2

def xs001 : Fin 3 → S
  | ⟨0, _⟩ => s0
  | ⟨1, _⟩ => s0
  | _ => s1

def xs010 : Fin 3 → S
  | ⟨0, _⟩ => s0
  | ⟨1, _⟩ => s1
  | _ => s0

def xs011 : Fin 3 → S
  | ⟨0, _⟩ => s0
  | _ => s1

lemma mem_carrier_n1_N2_xs001 : xs001 ∈ carrier_n1_N2 := by
  classical
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_univ _, ?_⟩
  intro n hn
  have hn1 : n = 1 := by simpa using hn
  subst hn1
  refine ⟨1, by decide, ?_, ?_⟩
  · apply (nthVisitTime_eq_some_iff (k := 2) (prefixExtend (k := 2) 2 xs001) s0 1 1).2
    constructor <;> decide
  · simp [successorAt, prefixExtend, xs001]

lemma carrier_n1_N2_eq_xs001 (x : Fin 3 → S) (hx : x ∈ carrier_n1_N2) : x = xs001 := by
  classical
  have hrow := (Finset.mem_filter.mp hx).2
  have hspec := hrow 1 (by simp)
  rcases hspec with ⟨t, htlt, htime, hsucc⟩
  have ht1 : t = 1 := by
    have ht01 : t = 0 ∨ t = 1 := by omega
    rcases ht01 with rfl | rfl
    · have hvisit0 :
        isNthVisitTime (k := 2) (prefixExtend (k := 2) 2 x) s0 1 0 := by
        exact (nthVisitTime_eq_some_iff (k := 2) (prefixExtend (k := 2) 2 x) s0 1 0).1
          (by simpa using htime)
      have : (0 : ℕ) = 1 := by simpa [visitCountBefore] using hvisit0.2
      cases this
    · rfl
  subst ht1
  have hvisit1 :
      isNthVisitTime (k := 2) (prefixExtend (k := 2) 2 x) s0 1 1 := by
    exact (nthVisitTime_eq_some_iff (k := 2) (prefixExtend (k := 2) 2 x) s0 1 1).1 htime
  have hx0nat : x 0 = s0 := by
    have hpx0 : prefixExtend (k := 2) 2 x 0 = s0 := by
      by_contra h0
      have hzero : visitCountBefore (k := 2) (prefixExtend (k := 2) 2 x) s0 1 = 0 := by
        simp [visitCountBefore, h0]
      exact Nat.zero_ne_one (hzero.symm.trans hvisit1.2)
    simpa [prefixExtend] using hpx0
  have hx1nat : x 1 = s0 := by
    simpa [prefixExtend] using hvisit1.1
  have hx2nat : x 2 = s1 := by
    simpa [successorAt, prefixExtend] using hsucc
  funext j
  fin_cases j
  · simpa [xs001] using hx0nat
  · simpa [xs001] using hx1nat
  · simpa [xs001] using hx2nat

lemma carrier_n1_N2_subsingleton : Subsingleton carrier_n1_N2 := by
  classical
  refine ⟨?_⟩
  intro x y
  apply Subtype.ext
  exact (carrier_n1_N2_eq_xs001 x.1 x.2).trans (carrier_n1_N2_eq_xs001 y.1 y.2).symm

lemma mem_carrier_n0_N2_xs010 : xs010 ∈ carrier_n0_N2 := by
  classical
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_univ _, ?_⟩
  intro n hn
  have hn0 : n = 0 := by simpa using hn
  subst hn0
  refine ⟨0, by decide, ?_, ?_⟩
  · exact nthVisitTime_zero_eq_some_zero_of_start (k := 2)
      (prefixExtend (k := 2) 2 xs010) s0 (by simp [prefixExtend, xs010])
  · simp [successorAt, prefixExtend, xs010]

lemma mem_carrier_n0_N2_xs011 : xs011 ∈ carrier_n0_N2 := by
  classical
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_univ _, ?_⟩
  intro n hn
  have hn0 : n = 0 := by simpa using hn
  subst hn0
  refine ⟨0, by decide, ?_, ?_⟩
  · exact nthVisitTime_zero_eq_some_zero_of_start (k := 2)
      (prefixExtend (k := 2) 2 xs011) s0 (by simp [prefixExtend, xs011])
  · simp [successorAt, prefixExtend, xs011]

lemma xs010_ne_xs011 : xs010 ≠ xs011 := by
  intro h
  have h2 := congrArg (fun f => f ⟨2, by decide⟩) h
  simp [xs010, xs011, s0, s1] at h2

theorem not_exists_equiv_carrier_n1_to_n0_N2 :
    ¬ Nonempty (carrier_n1_N2 ≃ carrier_n0_N2) := by
  classical
  rintro ⟨e⟩
  have hsub0 : Subsingleton carrier_n1_N2 := carrier_n1_N2_subsingleton
  let y0 : carrier_n0_N2 := ⟨xs010, mem_carrier_n0_N2_xs010⟩
  let y1 : carrier_n0_N2 := ⟨xs011, mem_carrier_n0_N2_xs011⟩
  have hpre : e.symm y0 = e.symm y1 := hsub0.elim _ _
  have hy : y0 = y1 := by
    have hy' : e (e.symm y0) = e (e.symm y1) := congrArg e hpre
    simpa using hy'
  have hvals : xs010 = xs011 := by
    exact congrArg Subtype.val hy
  exact xs010_ne_xs011 hvals

theorem not_hcarrier0_shape_k2 :
    ¬ (∀ n N : ℕ, Nonempty (
        rowVisitCylinderEventUpToPrefixCarrier (k := 2) s0 {n}
          (fun m => if m = n then s1 else s0) N ≃
        rowVisitCylinderEventUpToPrefixCarrier (k := 2) s0 {0}
          (fun m => if m = 0 then s1 else s0) N)) := by
  intro hall
  exact not_exists_equiv_carrier_n1_to_n0_N2 (hall 1 2)

/-- Strong-shape refutation matching the old carrier-equivalence bridge:
even before adding evidence-preservation, the required equivalence family fails. -/
theorem not_hcarrier0_strong_shape_k2 :
    ¬ (∀ n N : ℕ,
        ∃ e :
          rowVisitCylinderEventUpToPrefixCarrier (k := 2) s0 {n}
            (fun m => if m = n then s1 else s0) N ≃
            rowVisitCylinderEventUpToPrefixCarrier (k := 2) s0 {0}
              (fun m => if m = 0 then s1 else s0) N,
          ∀ xs :
            rowVisitCylinderEventUpToPrefixCarrier (k := 2) s0 {n}
              (fun m => if m = n then s1 else s0) N,
            Mettapedia.Logic.MarkovExchangeability.evidenceOf (n := N) xs.1 =
              Mettapedia.Logic.MarkovExchangeability.evidenceOf (n := N) (e xs).1) := by
  intro hall
  have hallEquiv :
      ∀ n N : ℕ,
        Nonempty
          (rowVisitCylinderEventUpToPrefixCarrier (k := 2) s0 {n}
            (fun m => if m = n then s1 else s0) N ≃
            rowVisitCylinderEventUpToPrefixCarrier (k := 2) s0 {0}
              (fun m => if m = 0 then s1 else s0) N) := by
    intro n N
    rcases hall n N with ⟨e, _⟩
    exact ⟨e⟩
  exact not_hcarrier0_shape_k2 hallEquiv

end FortiniCrossCounterexample

end MarkovDeFinettiHard
end Mettapedia.Logic
