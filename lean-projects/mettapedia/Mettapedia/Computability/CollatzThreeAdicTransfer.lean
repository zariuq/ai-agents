import Mettapedia.Computability.CollatzThreeAdic

/-!
# Transfer-operator interface for the exact 3-adic Collatz counter

This file repackages the sparse DP from `CollatzThreeAdic` in transfer-operator
language. It does not prove asymptotics yet; it just exposes the exact kernel
that later Perron–Frobenius / saddle-point work should study.
-/

namespace CollatzThreeAdic

/-- A finite-step transfer kernel on exact 3-adic residue states. -/
abbrev TransferKernel := GapResidueKey → GapResidueKey → Nat

/-- Multiplicity of one-step transitions from `src` to `dst`, counted by the
exact gap-labeled transition list. -/
def transitionMultiplicity (bitLength oddSteps placed : Nat) : TransferKernel :=
  fun src dst =>
    (stateTransitions bitLength oddSteps placed src).foldl
      (fun total tr => total + if tr.nextKey = dst then 1 else 0) 0

/-- The exact one-step transfer operator induced by the gap transition kernel. -/
abbrev kernelStep := stepStage

/-- Iterate the exact transfer operator through all odd placements. -/
abbrev kernelStages := stages

/-- Exact transfer-operator mass profile across odd placements. -/
abbrev kernelSigmas := sigmas

private theorem getD_foldl_transitionList_eq
    (trs : List GapTransition) (init : GapResidueStage) (count : Nat) (dst : GapResidueKey) :
    (trs.foldl (fun st tr => stageInsertAdd st tr.nextKey count) init).getD dst 0 =
      init.getD dst 0 +
        count * (trs.foldl (fun total tr => total + if tr.nextKey = dst then 1 else 0) 0) := by
  have hfoldIndicator :
      ∀ (trs : List GapTransition) (dst : GapResidueKey) (init : Nat),
        trs.foldl (fun total tr => total + if tr.nextKey = dst then 1 else 0) init =
          init + trs.foldl (fun total tr => total + if tr.nextKey = dst then 1 else 0) 0 := by
    intro trs dst init
    induction trs generalizing init with
    | nil => simp
    | cons tr trs ih =>
        rw [List.foldl_cons, List.foldl_cons]
        rw [ih (init + if tr.nextKey = dst then 1 else 0)]
        simp
        rw [ih (if tr.nextKey = dst then 1 else 0)]
        simp [Nat.add_assoc]
  induction trs generalizing init with
  | nil => simp
  | cons tr trs ih =>
      simp [List.foldl_cons, ih]
      by_cases h : tr.nextKey = dst
      · subst h
        simp [stageInsertAdd, Nat.add_assoc, Nat.add_comm]
        rw [hfoldIndicator trs tr.nextKey 1]
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · have hget : (stageInsertAdd init tr.nextKey count).getD dst 0 = init.getD dst 0 := by
          simp [stageInsertAdd, Std.HashMap.getD_insert, h]
        rw [hget]
        simp [h]

private theorem getD_foldl_transitionArray_eq
    (trs : Array GapTransition) (init : GapResidueStage) (count : Nat) (dst : GapResidueKey) :
    (trs.foldl (fun st tr => stageInsertAdd st tr.nextKey count) init).getD dst 0 =
      init.getD dst 0 +
        count * (trs.foldl (fun total tr => total + if tr.nextKey = dst then 1 else 0) 0) := by
  rw [← Array.foldl_toList
    (xs := trs) (f := fun st tr => stageInsertAdd st tr.nextKey count) (init := init)]
  rw [← Array.foldl_toList
    (xs := trs) (f := fun total tr => total + if tr.nextKey = dst then 1 else 0) (init := 0)]
  simpa using getD_foldl_transitionList_eq trs.toList init count dst

private theorem foldl_add_transitionMultiplicity_eq
    (bitLength oddSteps placed : Nat)
    (entries : List (GapResidueKey × Nat)) (dst : GapResidueKey) (init : Nat) :
    entries.foldl
        (fun acc entry => acc + entry.2 * transitionMultiplicity bitLength oddSteps placed entry.1 dst)
        init =
      init +
        entries.foldl
          (fun acc entry => acc + entry.2 * transitionMultiplicity bitLength oddSteps placed entry.1 dst)
          0 := by
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      rw [List.foldl_cons, List.foldl_cons]
      rw [ih (init + entry.2 * transitionMultiplicity bitLength oddSteps placed entry.1 dst)]
      simp
      rw [ih (entry.2 * transitionMultiplicity bitLength oddSteps placed entry.1 dst)]
      simp [Nat.add_assoc]

private theorem getD_foldl_entries_eq
    (bitLength oddSteps placed : Nat)
    (entries : List (GapResidueKey × Nat)) (init : GapResidueStage) (dst : GapResidueKey) :
    (entries.foldl
        (fun next entry =>
          (stateTransitions bitLength oddSteps placed entry.1).foldl
            (fun st tr => stageInsertAdd st tr.nextKey entry.2) next)
        init).getD dst 0 =
      init.getD dst 0 +
        entries.foldl
          (fun acc entry => acc + entry.2 * transitionMultiplicity bitLength oddSteps placed entry.1 dst)
          0 := by
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      simp [List.foldl_cons]
      rw [ih]
      rw [getD_foldl_transitionArray_eq]
      have hfold := foldl_add_transitionMultiplicity_eq bitLength oddSteps placed entries dst
        (entry.2 * transitionMultiplicity bitLength oddSteps placed entry.1 dst)
      rw [hfold]
      simp [transitionMultiplicity, Nat.add_assoc]

theorem transitionFold_getD_eq_transitionMultiplicity
    (bitLength oddSteps placed : Nat) (src : GapResidueKey)
    (init : GapResidueStage) (count : Nat) (dst : GapResidueKey) :
    ((stateTransitions bitLength oddSteps placed src).foldl
        (fun st tr => stageInsertAdd st tr.nextKey count) init).getD dst 0 =
      init.getD dst 0 + count * transitionMultiplicity bitLength oddSteps placed src dst := by
  simpa [transitionMultiplicity] using
    getD_foldl_transitionArray_eq
      (trs := stateTransitions bitLength oddSteps placed src)
      (init := init) (count := count) (dst := dst)

theorem transitionMultiplicity_eq_zero_of_not_lt
    {bitLength oddSteps placed : Nat}
    (h : ¬ placed < oddSteps) (src dst : GapResidueKey) :
    transitionMultiplicity bitLength oddSteps placed src dst = 0 := by
  simp [transitionMultiplicity, stateTransitions, h]

theorem kernelStep_eq_empty_of_not_lt
    {bitLength oddSteps placed : Nat}
    (h : ¬ placed < oddSteps) (stage : GapResidueStage) :
    kernelStep bitLength oddSteps placed stage = {} := by
  simp [kernelStep, stepStage, h]

theorem kernelStep_eq_toListFoldl
    (bitLength oddSteps placed : Nat) (stage : GapResidueStage) :
    kernelStep bitLength oddSteps placed stage =
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
  by_cases h : placed < oddSteps <;> simp [kernelStep, stepStage, h]

theorem kernelStep_getD_eq_transitionMultiplicityWeighted
    (bitLength oddSteps placed : Nat) (stage : GapResidueStage) (dst : GapResidueKey) :
    (kernelStep bitLength oddSteps placed stage).getD dst 0 =
      if placed < oddSteps then
        stageWeightedSum (fun key => transitionMultiplicity bitLength oddSteps placed key dst) stage
      else 0 := by
  unfold kernelStep stepStage
  by_cases hplaced : placed < oddSteps
  · simp [hplaced]
    rw [getD_foldl_entries_eq]
    simp
    rfl
  · simp [hplaced]

theorem kernelStep_getD_eq_of_equiv
    (bitLength oddSteps placed : Nat) {stage₁ stage₂ : GapResidueStage}
    (h : Std.HashMap.Equiv stage₁ stage₂) (dst : GapResidueKey) :
    (kernelStep bitLength oddSteps placed stage₁).getD dst 0 =
      (kernelStep bitLength oddSteps placed stage₂).getD dst 0 := by
  rw [kernelStep_getD_eq_transitionMultiplicityWeighted,
    kernelStep_getD_eq_transitionMultiplicityWeighted]
  by_cases hplaced : placed < oddSteps
  · simp [hplaced, stageWeightedSum_eq_of_equiv _ h]
  · simp [hplaced]

theorem totalCount_eq_kernelSigmas_last (bitLength oddSteps : Nat) :
    totalCount bitLength oddSteps =
      match (kernelSigmas bitLength oddSteps)[oddSteps]? with
      | some total => total
      | none => 0 := by
  rfl

end CollatzThreeAdic
