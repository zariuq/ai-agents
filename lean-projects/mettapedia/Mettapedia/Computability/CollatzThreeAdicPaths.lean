import Mathlib.Data.List.Count
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm
import Mettapedia.Computability.CollatzThreeAdicExact

/-!
# Path semantics for the exact 3-adic gap DP

## Informal theory

The exact DP of `CollatzThreeAdicExact` counts *admissible gap sequences*: a
sequence $(t_0,\dots,t_{k-1})$ of zero-gaps is admissible when the reverse
recurrence $A_{j+1} = (2^{t_j+1}A_j - 1)/3$ from $A_0 = 1$ stays integral,
avoids the dead class $3\mathbb{Z}$ while steps remain, respects the total
zero budget, and excludes the degenerate first step $(j,t)=(0,1)$.

This file makes that reading a theorem. `pathStates` enumerates the
admissible gap-prefix/end-state pairs; the key result is

  `exactStageWeightedSum w (exactStageAt L k j) = pathWeight L k j w`

for *every* weight `w` — the DP stage is, as a weighted multiset of
end-states, exactly the multiset of path end-states. Specializing `w = 1`:

  `totalCount L k = (pathStates L k k).length`,

i.e. the DP total counts admissible gap sequences. Downstream (in private
manuscript-facing developments) each completed path is mapped injectively to
the bitstring it denotes, bounding `totalCount` by the cardinality of any
type that faithfully contains those strings.

The weight-generalized induction is the standard trick: the one-step claim
"stage `j+1` is the pushforward of stage `j`" becomes, in weighted form,
`⟨w, stage (j+1)⟩ = ⟨T^*w, stage j⟩` with `T^*w` the transition pushforward
`transWeightList`, and the induction closes by instantiating the hypothesis
at `T^*w`.
-/

namespace CollatzThreeAdic

/-- Admissible gap-path/end-state pairs after `placed` odd steps. -/
def pathStates (bitLength oddSteps : Nat) : Nat → List (List Nat × GapValueKey)
  | 0 => [([], { usedZeros := 0, value := 1 })]
  | j + 1 =>
      (pathStates bitLength oddSteps j).flatMap fun pk =>
        (exactStateTransitionsList bitLength oddSteps j pk.2).map fun tr =>
          (pk.1 ++ [tr.gap], tr.nextKey)

/-- Number of admissible gap sequences with `placed` odd steps. -/
def pathCount (bitLength oddSteps placed : Nat) : Nat :=
  (pathStates bitLength oddSteps placed).length

/-- Promoted-gap exponent sum `P_j = Σ_i (t_i + 1)` for a gap prefix. -/
def gapPromotedSum (p : List Nat) : Nat :=
  p.length + p.sum

/-- Scaled numerator of the finite `Φ`-sum.

If `Φ_j = Σ_{i < j} 3^i 2^{-P_{i+1}}`, then `gapPhiScaled p = 2^{P_j} Φ_j`.
This keeps the algebra entirely in `Nat`, which is exactly the form used by the
path-recursion identity below. -/
def gapPhiScaled : List Nat → Nat
  | [] => 0
  | _ :: p => 2 ^ gapPromotedSum p + 3 * gapPhiScaled p

/-- Appending one new gap adds one promoted digit and `gap` new zeros. -/
theorem gapPromotedSum_append_singleton (p : List Nat) (gap : Nat) :
    gapPromotedSum (p ++ [gap]) = gapPromotedSum p + (gap + 1) := by
  simp [gapPromotedSum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The scaled `Φ`-numerator satisfies the natural append recursion
`S(p ++ [g]) = 2^(g+1) S(p) + 3^|p|`. -/
theorem gapPhiScaled_append_singleton (p : List Nat) (gap : Nat) :
    gapPhiScaled (p ++ [gap]) = 2 ^ (gap + 1) * gapPhiScaled p + 3 ^ p.length := by
  induction p with
  | nil =>
      simp [gapPhiScaled, gapPromotedSum]
  | cons t p ih =>
      simp [gapPhiScaled, ih, gapPromotedSum, Nat.pow_add,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.left_distrib]
      ac_rfl

/-- Appending one gap also gives the corresponding power recursion for
`2 ^ gapPromotedSum`. -/
theorem pow_gapPromotedSum_append_singleton (p : List Nat) (gap : Nat) :
    2 ^ gapPromotedSum (p ++ [gap]) = 2 ^ (gapPromotedSum p + (gap + 1)) := by
  exact congrArg (fun n => 2 ^ n) (gapPromotedSum_append_singleton p gap)

/-- The promoted-gap append law in the multiplicative `2^P` form used by the
path-recursion proof. -/
theorem pow_gapPromotedSum_product_append_singleton (p : List Nat) (gap : Nat) :
    2 ^ (gap + 1) * 2 ^ gapPromotedSum p = 2 ^ gapPromotedSum (p ++ [gap]) := by
  calc
    2 ^ (gap + 1) * 2 ^ gapPromotedSum p
        = 2 ^ ((gap + 1) + gapPromotedSum p) := by
            rw [← Nat.pow_add]
    _ = 2 ^ (gapPromotedSum p + (gap + 1)) := by
          rw [Nat.add_comm]
    _ = 2 ^ gapPromotedSum (p ++ [gap]) := by
          exact (pow_gapPromotedSum_append_singleton p gap).symm

/-- Total `w`-weight of path end-states. -/
def pathWeight (bitLength oddSteps placed : Nat) (w : GapValueKey → Nat) : Nat :=
  ((pathStates bitLength oddSteps placed).map fun pk => w pk.2).sum

/-- One-step pushforward of a weight through the admissible transitions. -/
def transWeightList (bitLength oddSteps placed : Nat) (w : GapValueKey → Nat)
    (key : GapValueKey) : Nat :=
  ((exactStateTransitionsList bitLength oddSteps placed key).map fun tr => w tr.nextKey).sum

/-- Weighted mass of an exact stage. -/
def exactStageWeightedSum (w : GapValueKey → Nat) (stage : GapValueStage) : Nat :=
  stage.toList.foldl (fun acc entry => acc + entry.2 * w entry.1) 0

/-! ### Generic foldl/perm helpers (local copies; the analogues in
`CollatzThreeAdicExact` are `private`) -/

private theorem foldl_add_weighted_eq_sum_map
    (w : GapValueKey → Nat) (l : List (GapValueKey × Nat)) (init : Nat) :
    l.foldl (fun acc entry => acc + entry.2 * w entry.1) init =
      init + (l.map (fun entry => entry.2 * w entry.1)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (init := init + x.2 * w x.1)

private theorem sum_weighted_eq_of_perm
    (w : GapValueKey → Nat) {l₁ l₂ : List (GapValueKey × Nat)} (h : l₁.Perm l₂) :
    (l₁.map (fun entry => entry.2 * w entry.1)).sum =
      (l₂.map (fun entry => entry.2 * w entry.1)).sum := by
  simpa using List.Perm.sum_nat (h.map (fun entry => entry.2 * w entry.1))

private theorem insert_same_getD_equiv (stage : GapValueStage) (key : GapValueKey)
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

private theorem filter_eq_self_of_not_mem_key_eq (stage : GapValueStage) (key : GapValueKey)
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

theorem exactStageWeightedSum_eq_sum_map (w : GapValueKey → Nat) (stage : GapValueStage) :
    exactStageWeightedSum w stage =
      (stage.toList.map (fun entry => entry.2 * w entry.1)).sum := by
  simpa [exactStageWeightedSum] using foldl_add_weighted_eq_sum_map w stage.toList 0

theorem exactStageWeightedSum_exactStageInsertAdd
    (w : GapValueKey → Nat) (stage : GapValueStage) (key : GapValueKey) (count : Nat) :
    exactStageWeightedSum w (exactStageInsertAdd stage key count) =
      exactStageWeightedSum w stage + count * w key := by
  let old := stage.getD key 0
  by_cases hmem : key ∈ stage
  · have hpermOld : stage.toList.Perm
        ((key, old) :: stage.toList.filter (fun x => decide ¬ (key == x.1) = true)) := by
      exact (Std.HashMap.Equiv.toList_perm (insert_same_getD_equiv stage key hmem)).symm.trans
        (Std.HashMap.toList_insert_perm (m := stage) (k := key) (v := old))
    have hpermNew : (exactStageInsertAdd stage key count).toList.Perm
        ((key, old + count) :: stage.toList.filter (fun x => decide ¬ (key == x.1) = true)) := by
      unfold exactStageInsertAdd
      simpa [old] using
        (Std.HashMap.toList_insert_perm (m := stage) (k := key)
          (v := stage.getD key 0 + count))
    rw [exactStageWeightedSum_eq_sum_map, exactStageWeightedSum_eq_sum_map]
    rw [sum_weighted_eq_of_perm w hpermNew, sum_weighted_eq_of_perm w hpermOld]
    simp [old, Nat.add_assoc, Nat.add_comm, Nat.right_distrib]
  · have hpermNew : (exactStageInsertAdd stage key count).toList.Perm
        ((key, count) :: stage.toList) := by
      unfold exactStageInsertAdd
      simpa [Std.HashMap.getD_eq_fallback hmem,
        filter_eq_self_of_not_mem_key_eq stage key hmem] using
        (Std.HashMap.toList_insert_perm (m := stage) (k := key)
          (v := stage.getD key 0 + count))
    rw [exactStageWeightedSum_eq_sum_map]
    rw [sum_weighted_eq_of_perm w hpermNew]
    rw [exactStageWeightedSum_eq_sum_map]
    simp [Nat.add_comm]

private theorem exactStageWeightedSum_foldl_transitionList
    (w : GapValueKey → Nat) (trs : List GapValueTransition)
    (init : GapValueStage) (count : Nat) :
    exactStageWeightedSum w
        (trs.foldl (fun st tr => exactStageInsertAdd st tr.nextKey count) init) =
      exactStageWeightedSum w init +
        count * (trs.map fun tr => w tr.nextKey).sum := by
  induction trs generalizing init with
  | nil => simp
  | cons tr trs ih =>
      simp [List.foldl_cons, ih, exactStageWeightedSum_exactStageInsertAdd,
        Nat.mul_add, Nat.add_assoc]

private theorem exactStageWeightedSum_foldl_transitionArray
    (w : GapValueKey → Nat) (trs : Array GapValueTransition)
    (init : GapValueStage) (count : Nat) :
    exactStageWeightedSum w
        (trs.foldl (fun st tr => exactStageInsertAdd st tr.nextKey count) init) =
      exactStageWeightedSum w init +
        count * (trs.toList.map fun tr => w tr.nextKey).sum := by
  rw [← Array.foldl_toList
    (xs := trs) (f := fun st tr => exactStageInsertAdd st tr.nextKey count) (init := init)]
  exact exactStageWeightedSum_foldl_transitionList w trs.toList init count

private theorem foldl_add_transWeight_shift
    (bitLength oddSteps placed : Nat) (w : GapValueKey → Nat)
    (entries : List (GapValueKey × Nat)) (init : Nat) :
    entries.foldl
        (fun acc entry =>
          acc + entry.2 * transWeightList bitLength oddSteps placed w entry.1)
        init =
      init +
        entries.foldl
          (fun acc entry =>
            acc + entry.2 * transWeightList bitLength oddSteps placed w entry.1)
          0 := by
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      rw [List.foldl_cons, List.foldl_cons]
      rw [ih (init + entry.2 * transWeightList bitLength oddSteps placed w entry.1)]
      rw [ih (0 + entry.2 * transWeightList bitLength oddSteps placed w entry.1)]
      omega

private theorem exactStageWeightedSum_foldl_entries
    (bitLength oddSteps placed : Nat) (w : GapValueKey → Nat)
    (entries : List (GapValueKey × Nat)) (init : GapValueStage)
    (hplaced : placed < oddSteps) :
    exactStageWeightedSum w
        (entries.foldl
          (fun next entry =>
            (exactStateTransitions bitLength oddSteps placed entry.1).foldl
              (fun st tr => exactStageInsertAdd st tr.nextKey entry.2) next)
          init) =
      exactStageWeightedSum w init +
        entries.foldl
          (fun acc entry =>
            acc + entry.2 * transWeightList bitLength oddSteps placed w entry.1)
          0 := by
  induction entries generalizing init with
  | nil => simp
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      rw [ih]
      rw [exactStageWeightedSum_foldl_transitionArray]
      have htoList :
          (exactStateTransitions bitLength oddSteps placed entry.1).toList =
            exactStateTransitionsList bitLength oddSteps placed entry.1 := by
        rw [exactStateTransitions_eq_toArray_exactStateTransitionsList]
        simp [hplaced]
      rw [htoList]
      have hfold := foldl_add_transWeight_shift bitLength oddSteps placed w entries
        (0 + entry.2 * transWeightList bitLength oddSteps placed w entry.1)
      rw [hfold]
      simp only [transWeightList]
      omega

/-- Expanding `exactGapNextKey? = some next` yields the explicit one-step
reverse-Collatz update needed for the path semantics. -/
private theorem exactGapNextKey?_eq_some_pathSemantics
    {bitLength oddSteps placed : Nat} {key next : GapValueKey} {gap : Nat}
    (h : exactGapNextKey? bitLength oddSteps placed key gap = some next) :
    placed < oddSteps ∧
      next.usedZeros = key.usedZeros + gap ∧
      next.value = (2 ^ (gap + 1) * key.value - 1) / 3 ∧
      (2 ^ (gap + 1) * key.value - 1) % 3 = 0 := by
  unfold exactGapNextKey? at h
  dsimp only at h
  by_cases h1 : placed < oddSteps
  · rw [if_pos h1] at h
    by_cases h2 : gap ≤ exactGapUpper bitLength oddSteps key
    · rw [if_pos h2] at h
      by_cases h3 : ((2 ^ (gap + 1) * key.value - 1) % 3 == 0) = true
      · rw [if_pos h3] at h
        by_cases h4 : (!(placed == 0 && gap == 1)) = true
        · rw [if_pos h4] at h
          by_cases h5 : ((oddSteps - placed == 1) ||
              ((2 ^ (gap + 1) * key.value - 1) / 3 % 3 != 0)) = true
          · rw [if_pos h5] at h
            refine ⟨h1, ?_, ?_, ?_⟩
            · have hEq : next =
                  { usedZeros := key.usedZeros + gap
                    value := (2 ^ (gap + 1) * key.value - 1) / 3 } := by
                cases next
                cases h
                rfl
              cases hEq
              rfl
            · have hEq : next =
                  { usedZeros := key.usedZeros + gap
                    value := (2 ^ (gap + 1) * key.value - 1) / 3 } := by
                cases next
                cases h
                rfl
              cases hEq
              rfl
            · simpa using h3
          · rw [if_neg h5] at h
            simp at h
        · rw [if_neg h4] at h
          simp at h
      · rw [if_neg h3] at h
        simp at h
    · rw [if_neg h2] at h
      simp at h
  · rw [if_neg h1] at h
    simp at h

private theorem exactGapNextKey?_gap_ne_one_of_placed_zero
    {bitLength oddSteps : Nat} {key next : GapValueKey} {gap : Nat}
    (h : exactGapNextKey? bitLength oddSteps 0 key gap = some next) :
    gap ≠ 1 := by
  have hlt : 0 < oddSteps := by
    by_cases hodd : 0 < oddSteps
    · exact hodd
    · unfold exactGapNextKey? at h
      dsimp only at h
      rw [if_neg hodd] at h
      simp at h
  unfold exactGapNextKey? at h
  dsimp only at h
  rw [if_pos hlt] at h
  by_cases hgapLe : gap ≤ exactGapUpper bitLength oddSteps key
  · rw [if_pos hgapLe] at h
    by_cases hmod : ((2 ^ (gap + 1) * key.value - 1) % 3 == 0) = true
    · rw [if_pos hmod] at h
      by_cases hskip : (!(0 == 0 && gap == 1)) = true
      · have : gap ≠ 1 := by
          intro hgap
          subst hgap
          simp at hskip
        exact this
      · rw [if_neg hskip] at h
        simp at h
    · rw [if_neg hmod] at h
      simp at h
  · rw [if_neg hgapLe] at h
    simp at h

/-- Weighted-stage step formula: one DP step pushes the weight forward. -/
theorem exactStageWeightedSum_exactStepStage
    (bitLength oddSteps placed : Nat) (w : GapValueKey → Nat) (stage : GapValueStage) :
    exactStageWeightedSum w (exactStepStage bitLength oddSteps placed stage) =
      if placed < oddSteps then
        exactStageWeightedSum (transWeightList bitLength oddSteps placed w) stage
      else 0 := by
  unfold exactStepStage
  by_cases hplaced : placed < oddSteps
  · simp [hplaced]
    rw [exactStageWeightedSum_foldl_entries bitLength oddSteps placed w stage.toList _ hplaced]
    have hempty :
        exactStageWeightedSum w
          (Std.HashMap.emptyWithCapacity (stage.size * 2 + 1) : GapValueStage) = 0 := by
      simp [exactStageWeightedSum]
    rw [hempty]
    rw [exactStageWeightedSum_eq_sum_map]
    rw [foldl_add_weighted_eq_sum_map
      (transWeightList bitLength oddSteps placed w) stage.toList 0]
    simp
  · simp [hplaced, exactStageWeightedSum]

/-! ### The path/stage correspondence -/

private theorem sum_map_flatMap_nat {α β : Type}
    (l : List α) (f : α → List β) (g : β → Nat) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem pathWeight_succ
    (bitLength oddSteps placed : Nat) (w : GapValueKey → Nat) :
    pathWeight bitLength oddSteps (placed + 1) w =
      pathWeight bitLength oddSteps placed
        (transWeightList bitLength oddSteps placed w) := by
  unfold pathWeight
  show (((pathStates bitLength oddSteps placed).flatMap _).map _).sum = _
  rw [sum_map_flatMap_nat]
  congr 1
  apply List.map_congr_left
  intro pk _
  simp only [transWeightList, List.map_map]
  rfl

theorem exactStageWeightedSum_exactStageAt_eq_pathWeight
    (bitLength oddSteps : Nat) :
    ∀ placed (w : GapValueKey → Nat),
      exactStageWeightedSum w (exactStageAt bitLength oddSteps placed) =
        pathWeight bitLength oddSteps placed w := by
  intro placed
  induction placed with
  | zero =>
      intro w
      rw [exactStageAt_zero]
      rw [exactStageWeightedSum_exactStageInsertAdd]
      simp [exactStageWeightedSum, pathWeight, pathStates]
  | succ placed ih =>
      intro w
      rw [exactStageAt_succ]
      rw [exactStageWeightedSum_exactStepStage]
      by_cases hplaced : placed < oddSteps
      · simp only [hplaced, if_pos]
        rw [ih (transWeightList bitLength oddSteps placed w)]
        exact (pathWeight_succ bitLength oddSteps placed w).symm
      · have hnil : ∀ key : GapValueKey,
            exactStateTransitionsList bitLength oddSteps placed key = [] := by
          intro key
          unfold exactStateTransitionsList
          apply List.filterMap_eq_nil_iff.mpr
          intro gap _
          simp [exactGapNextKey?, hplaced]
        have hzero : pathWeight bitLength oddSteps (placed + 1) w = 0 := by
          unfold pathWeight
          show (((pathStates bitLength oddSteps placed).flatMap _).map _).sum = _
          rw [sum_map_flatMap_nat]
          have hconst : ∀ (l : List (List Nat × GapValueKey)),
              (l.map fun _ => (0 : Nat)).sum = 0 := by
            intro l
            induction l with
            | nil => simp
            | cons a l ih => simp
          simp only [hnil, List.map_nil, List.sum_nil]
          exact hconst _
        simp [hplaced, hzero]

/-! ### Exact gap-series semantics of admissible paths -/

/-- Every admissible path ends at a strictly positive exact value. -/
theorem pathStates_value_pos
    (bitLength oddSteps : Nat) :
    ∀ placed pk, pk ∈ pathStates bitLength oddSteps placed → 0 < pk.2.value := by
  intro placed
  induction placed with
  | zero =>
      intro pk hpk
      simp [pathStates] at hpk
      subst hpk
      decide
  | succ placed ih =>
      intro pk hpk
      simp only [pathStates, List.mem_flatMap, List.mem_map] at hpk
      rcases hpk with ⟨qk, hqk, tr, htr, rfl⟩
      rcases (mem_exactStateTransitionsList_iff bitLength oddSteps placed qk.2 tr).1 htr with
        ⟨_hgap, hnext⟩
      exact exactGapNextKey?_value_pos bitLength oddSteps placed qk.2 tr.nextKey tr.gap
        (ih qk hqk) hnext

/-- Every admissible gap path carries the exact scaled affine-series identity

`3^j A_j + gapPhiScaled(path) = 2^(gapPromotedSum(path))`.

This is the integral form of the finite `Φ`-identity
`A_j = 2^{P_j} (1 - Φ_j) / 3^j`. -/
theorem pathStates_gapSemantics
    (bitLength oddSteps : Nat) :
    ∀ placed pk, pk ∈ pathStates bitLength oddSteps placed →
      pk.1.length = placed ∧
      pk.2.usedZeros = pk.1.sum ∧
      3 ^ placed * pk.2.value + gapPhiScaled pk.1 = 2 ^ gapPromotedSum pk.1 := by
  intro placed
  induction placed with
  | zero =>
      intro pk hpk
      simp [pathStates] at hpk
      subst hpk
      constructor
      · rfl
      constructor
      · rfl
      · simp [gapPhiScaled, gapPromotedSum]
  | succ placed ih =>
      intro pk hpk
      simp only [pathStates, List.mem_flatMap, List.mem_map] at hpk
      rcases hpk with ⟨qk, hqk, tr, htr, rfl⟩
      rcases ih qk hqk with ⟨hlen, hzeros, hphi⟩
      rcases (mem_exactStateTransitionsList_iff bitLength oddSteps placed qk.2 tr).1 htr with
        ⟨_hgap, hnext⟩
      rcases exactGapNextKey?_eq_some_pathSemantics hnext with
        ⟨_hplaced, hused, hvalue, hdiv⟩
      have hqval : 0 < qk.2.value := pathStates_value_pos bitLength oddSteps placed qk hqk
      refine ⟨by simp [hlen], by simp [hused, hzeros], ?_⟩
      rw [hvalue, gapPhiScaled_append_singleton, gapPromotedSum_append_singleton]
      have hmuldiv :
          3 * ((2 ^ (tr.gap + 1) * qk.2.value - 1) / 3) =
            2 ^ (tr.gap + 1) * qk.2.value - 1 := by
        exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hdiv)
      have hone_le :
          1 ≤ 2 ^ (tr.gap + 1) * qk.2.value := by
        have hpow : 0 < 2 ^ (tr.gap + 1) := Nat.two_pow_pos _
        exact Nat.succ_le_of_lt (Nat.mul_pos hpow hqval)
      have hsubadd :
          (2 ^ (tr.gap + 1) * qk.2.value - 1) + 1 =
            2 ^ (tr.gap + 1) * qk.2.value := by
        exact Nat.sub_add_cancel hone_le
      have hcombine :
          3 ^ placed * (2 ^ (tr.gap + 1) * qk.2.value - 1) + 3 ^ placed =
            3 ^ placed * (2 ^ (tr.gap + 1) * qk.2.value) := by
        calc
          3 ^ placed * (2 ^ (tr.gap + 1) * qk.2.value - 1) + 3 ^ placed
              = 3 ^ placed * (2 ^ (tr.gap + 1) * qk.2.value - 1) + 3 ^ placed * 1 := by
                  rw [Nat.mul_one]
          _ = 3 ^ placed * ((2 ^ (tr.gap + 1) * qk.2.value - 1) + 1) := by
                rw [← Nat.left_distrib]
          _ = 3 ^ placed * (2 ^ (tr.gap + 1) * qk.2.value) := by
                simp [hsubadd]
      have htail :
          2 ^ (tr.gap + 1) * (3 ^ placed * qk.2.value + gapPhiScaled qk.1) =
            2 ^ (gapPromotedSum qk.1 + (tr.gap + 1)) := by
        rw [hphi]
        calc
          2 ^ (tr.gap + 1) * 2 ^ gapPromotedSum qk.1
              = 2 ^ gapPromotedSum (qk.1 ++ [tr.gap]) := by
                  exact pow_gapPromotedSum_product_append_singleton qk.1 tr.gap
          _ = 2 ^ (gapPromotedSum qk.1 + (tr.gap + 1)) := by
                exact pow_gapPromotedSum_append_singleton qk.1 tr.gap
      calc
        3 ^ (placed + 1) * ((2 ^ (tr.gap + 1) * qk.2.value - 1) / 3) +
            (2 ^ (tr.gap + 1) * gapPhiScaled qk.1 + 3 ^ qk.1.length)
            = 3 ^ placed * (2 ^ (tr.gap + 1) * qk.2.value - 1) +
                (2 ^ (tr.gap + 1) * gapPhiScaled qk.1 + 3 ^ qk.1.length) := by
                  rw [Nat.pow_succ, Nat.mul_assoc, hmuldiv]
        _ = 2 ^ (tr.gap + 1) * (3 ^ placed * qk.2.value + gapPhiScaled qk.1) := by
              rw [hlen]
              calc
                3 ^ placed * (2 ^ (tr.gap + 1) * qk.2.value - 1) +
                    (2 ^ (tr.gap + 1) * gapPhiScaled qk.1 + 3 ^ placed)
                    = (3 ^ placed * (2 ^ (tr.gap + 1) * qk.2.value - 1) + 3 ^ placed) +
                        2 ^ (tr.gap + 1) * gapPhiScaled qk.1 := by
                          ac_rfl
                _ = 3 ^ placed * (2 ^ (tr.gap + 1) * qk.2.value) +
                        2 ^ (tr.gap + 1) * gapPhiScaled qk.1 := by
                          rw [hcombine]
                _ = 2 ^ (tr.gap + 1) * (3 ^ placed * qk.2.value) +
                        2 ^ (tr.gap + 1) * gapPhiScaled qk.1 := by
                          ac_rfl
                _ = 2 ^ (tr.gap + 1) * (3 ^ placed * qk.2.value + gapPhiScaled qk.1) := by
                          rw [Nat.mul_add]
        _ = 2 ^ (gapPromotedSum qk.1 + (tr.gap + 1)) := htail

/-- Completed admissible paths satisfy the final scaled congruence

`gapPhiScaled(path) ≡ 2^(gapPromotedSum(path)) [MOD 3^k]`.

This is the integral congruence form of the finite `Φ_k ≡ 1 (mod 3^k)` target
that later analytic lower-bound work is meant to exploit. -/
theorem pathStates_final_congruence
    {bitLength oddSteps : Nat} {pk : List Nat × GapValueKey}
    (hpk : pk ∈ pathStates bitLength oddSteps oddSteps) :
    gapPhiScaled pk.1 ≡ 2 ^ gapPromotedSum pk.1 [MOD 3 ^ oddSteps] := by
  rcases pathStates_gapSemantics bitLength oddSteps oddSteps pk hpk with ⟨_hlen, _hzeros, hphi⟩
  have hle : gapPhiScaled pk.1 ≤ 2 ^ gapPromotedSum pk.1 := by
    omega
  rw [Nat.modEq_iff_dvd' hle]
  exact ⟨pk.2.value, by omega⟩

/-- Every admissible path respects the global zero budget. -/
theorem pathStates_zeroBudget
    (bitLength oddSteps : Nat) :
    ∀ placed pk, pk ∈ pathStates bitLength oddSteps placed →
      pk.1.sum ≤ bitLength - oddSteps := by
  intro placed
  induction placed with
  | zero =>
      intro pk hpk
      simp [pathStates] at hpk
      subst hpk
      simp
  | succ placed ih =>
      intro pk hpk
      simp only [pathStates, List.mem_flatMap, List.mem_map] at hpk
      rcases hpk with ⟨qk, hqk, tr, htr, rfl⟩
      have hbudget : qk.1.sum ≤ bitLength - oddSteps := ih qk hqk
      rcases pathStates_gapSemantics bitLength oddSteps placed qk hqk with ⟨_hlen, hzeros, _hphi⟩
      rcases (mem_exactStateTransitionsList_iff bitLength oddSteps placed qk.2 tr).1 htr with
        ⟨hgaplt, _hnext⟩
      have hgaple : tr.gap ≤ bitLength - oddSteps - qk.1.sum := by
        have : tr.gap ≤ exactGapUpper bitLength oddSteps qk.2 := Nat.lt_succ_iff.mp hgaplt
        simpa [exactGapUpper, hzeros] using this
      simp
      omega

theorem pathStates_head_ne_one
    (bitLength oddSteps : Nat) :
    ∀ placed pk, pk ∈ pathStates bitLength oddSteps placed →
      placed = 0 ∨ pk.1.head? ≠ some 1 := by
  intro placed
  induction placed with
  | zero =>
      intro pk hpk
      left
      rfl
  | succ placed ih =>
      intro pk hpk
      simp only [pathStates, List.mem_flatMap, List.mem_map] at hpk
      rcases hpk with ⟨qk, hqk, tr, htr, rfl⟩
      rcases (mem_exactStateTransitionsList_iff bitLength oddSteps placed qk.2 tr).1 htr with
        ⟨_hgap, hnext⟩
      cases placed with
      | zero =>
          right
          have hgapne : tr.gap ≠ 1 :=
            exactGapNextKey?_gap_ne_one_of_placed_zero hnext
          have hqnil : qk.1 = [] := by
            rcases pathStates_gapSemantics bitLength oddSteps 0 qk hqk with ⟨hlen, _, _⟩
            cases qk with
            | mk q key =>
                simp at hlen
                simp [hlen]
          simpa [hqnil] using hgapne
      | succ placed' =>
          right
          have hqhead : qk.1.head? ≠ some 1 := by
            rcases ih qk hqk with h0 | hhead
            · omega
            · exact hhead
          have hqnil : qk.1 ≠ [] := by
            intro hnil
            rcases pathStates_gapSemantics bitLength oddSteps (placed' + 1) qk hqk with ⟨hlen, _, _⟩
            simp [hnil] at hlen
          have hheadEq : (qk.1 ++ [tr.gap]).head? = qk.1.head? := by
            cases hq : qk.1 with
            | nil => cases hqnil hq
            | cons x xs => simp
          simpa [hheadEq] using hqhead

private theorem head?_append_singleton_of_ne_nil {α : Type} {q : List α} (hq : q ≠ []) (a : α) :
    (q ++ [a]).head? = q.head? := by
  cases q with
  | nil => cases hq rfl
  | cons x xs => simp

private theorem mem_pathStates_of_exactSemantics
    (bitLength oddSteps : Nat) :
    ∀ placed p value,
      p.length = placed →
      placed ≤ oddSteps →
      p.sum ≤ bitLength - oddSteps →
      (placed = 0 ∨ p.head? ≠ some 1) →
      0 < value →
      3 ^ placed * value + gapPhiScaled p = 2 ^ gapPromotedSum p →
      (placed = oddSteps ∨ value % 3 ≠ 0) →
      ∃ key, (p, key) ∈ pathStates bitLength oddSteps placed ∧
        key.usedZeros = p.sum ∧ key.value = value := by
  intro placed p
  induction p using List.reverseRecOn generalizing placed with
  | nil =>
      intro value hlen hplaced _hbudget _hskip _hvalue hphi _hkeep
      have hplaced0 : placed = 0 := by simpa using hlen.symm
      subst placed
      have hvalue1 : value = 1 := by
        simpa [gapPhiScaled, gapPromotedSum] using hphi
      refine ⟨{ usedZeros := 0, value := 1 }, ?_, ?_, ?_⟩
      · simp [pathStates]
      · simp
      · simp [hvalue1]
  | append_singleton q gap ih =>
      intro value hlen hplaced hbudget hskip hvalue hphi hkeep
      have hlenq : q.length + 1 = placed := by simpa using hlen
      have hbudget' : q.sum + gap ≤ bitLength - oddSteps := by
        simpa using hbudget
      have hbudgetq : q.sum ≤ bitLength - oddSteps := by
        exact le_trans (Nat.le_add_right q.sum gap) hbudget'
      have hskipP : (q ++ [gap]).head? ≠ some 1 := by
        cases hskip with
        | inl h0 => omega
        | inr h => exact h
      have hskipq : q.length = 0 ∨ q.head? ≠ some 1 := by
        by_cases hqnil : q = []
        · left
          simp [hqnil]
        · right
          intro hhead
          apply hskipP
          simpa [head?_append_singleton_of_ne_nil hqnil gap] using hhead
      have hltPlaced : q.length < oddSteps := by
        omega
      have hphi' :
          3 ^ (q.length + 1) * value +
              (2 ^ (gap + 1) * gapPhiScaled q + 3 ^ q.length) =
            2 ^ (gap + 1) * 2 ^ gapPromotedSum q := by
        have hphi0 :
            3 ^ (q.length + 1) * value + gapPhiScaled (q ++ [gap]) =
              2 ^ gapPromotedSum (q ++ [gap]) := by
          simpa [hlenq] using hphi
        simpa [gapPhiScaled_append_singleton, pow_gapPromotedSum_product_append_singleton]
          using hphi0
      have hsum_lt :
          2 ^ (gap + 1) * gapPhiScaled q + 3 ^ q.length <
            2 ^ (gap + 1) * 2 ^ gapPromotedSum q := by
        have hpos : 0 < 3 ^ (q.length + 1) * value := by
          exact Nat.mul_pos (Nat.pow_pos (by decide : 0 < 3)) hvalue
        calc
          2 ^ (gap + 1) * gapPhiScaled q + 3 ^ q.length
              < 3 ^ (q.length + 1) * value +
                  (2 ^ (gap + 1) * gapPhiScaled q + 3 ^ q.length) := by
                    exact Nat.lt_add_of_pos_left hpos
          _ = 2 ^ (gap + 1) * 2 ^ gapPromotedSum q := hphi'
      have hmul_lt :
          2 ^ (gap + 1) * gapPhiScaled q <
            2 ^ (gap + 1) * 2 ^ gapPromotedSum q := by
        exact lt_of_lt_of_le
          (Nat.lt_add_of_pos_right (Nat.pow_pos (by decide : 0 < 3)))
          hsum_lt.le
      have hltPhi : gapPhiScaled q < 2 ^ gapPromotedSum q := by
        exact Nat.lt_of_mul_lt_mul_left hmul_lt
      let diff := 2 ^ gapPromotedSum q - gapPhiScaled q
      have hsub : gapPhiScaled q + diff = 2 ^ gapPromotedSum q := by
        dsimp [diff]
        rw [Nat.add_comm]
        exact Nat.sub_add_cancel (Nat.le_of_lt hltPhi)
      have hbase :
          3 ^ (q.length + 1) * value + 3 ^ q.length =
            2 ^ (gap + 1) * diff := by
        have hcancel :
            3 ^ (q.length + 1) * value + 3 ^ q.length +
                2 ^ (gap + 1) * gapPhiScaled q =
              2 ^ (gap + 1) * diff + 2 ^ (gap + 1) * gapPhiScaled q := by
          calc
            3 ^ (q.length + 1) * value + 3 ^ q.length + 2 ^ (gap + 1) * gapPhiScaled q
                = 3 ^ (q.length + 1) * value +
                    (2 ^ (gap + 1) * gapPhiScaled q + 3 ^ q.length) := by
                      ac_rfl
            _ = 2 ^ (gap + 1) * (gapPhiScaled q + diff) := by
                  simpa [hsub, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                    using hphi'
            _ = 2 ^ (gap + 1) * diff + 2 ^ (gap + 1) * gapPhiScaled q := by
                  rw [Nat.mul_add]
                  ac_rfl
        exact Nat.add_right_cancel hcancel
      have hdiffEq :
          3 ^ q.length * (3 * value + 1) = 2 ^ (gap + 1) * diff := by
        calc
          3 ^ q.length * (3 * value + 1)
              = 3 ^ (q.length + 1) * value + 3 ^ q.length := by
                  calc
                    3 ^ q.length * (3 * value + 1)
                        = 3 ^ q.length * (3 * value) + 3 ^ q.length * 1 := by
                            rw [Nat.mul_add]
                    _ = (3 ^ q.length * 3) * value + 3 ^ q.length := by
                          rw [Nat.mul_assoc, Nat.mul_one]
                    _ = 3 ^ (q.length + 1) * value + 3 ^ q.length := by
                          rw [Nat.pow_succ, Nat.mul_comm]
          _ = 2 ^ (gap + 1) * diff := hbase
      have hcop23 : Nat.Coprime 2 3 := by decide
      have hcop2pow3pow : Nat.Coprime (2 ^ (gap + 1)) (3 ^ q.length) := by
        exact Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ hcop23)
      have hdvdNumProd : 2 ^ (gap + 1) ∣ (3 * value + 1) * 3 ^ q.length := by
        exact ⟨diff, by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdiffEq⟩
      have hdvdNum : 2 ^ (gap + 1) ∣ 3 * value + 1 := by
        exact (Nat.Coprime.dvd_mul_right hcop2pow3pow).mp hdvdNumProd
      have hdvdDiffProd : 3 ^ q.length ∣ 2 ^ (gap + 1) * diff := by
        exact ⟨3 * value + 1, by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdiffEq.symm⟩
      have hdvdDiff : 3 ^ q.length ∣ diff := by
        exact (Nat.Coprime.dvd_mul_left hcop2pow3pow.symm).mp hdvdDiffProd
      let prefixValue := diff / 3 ^ q.length
      have hprefixEq : 3 ^ q.length * prefixValue = diff := by
        dsimp [prefixValue]
        exact Nat.mul_div_cancel' hdvdDiff
      have hprefixMulEq : 2 ^ (gap + 1) * prefixValue = 3 * value + 1 := by
        have hmul :
            3 ^ q.length * (2 ^ (gap + 1) * prefixValue) =
              3 ^ q.length * (3 * value + 1) := by
          calc
            3 ^ q.length * (2 ^ (gap + 1) * prefixValue)
                = 2 ^ (gap + 1) * (3 ^ q.length * prefixValue) := by
                    ac_rfl
            _ = 2 ^ (gap + 1) * diff := by rw [hprefixEq]
            _ = 3 ^ q.length * (3 * value + 1) := hdiffEq.symm
        exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 3)) <| by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
      have hprefixPos : 0 < prefixValue := by
        apply Nat.pos_of_ne_zero
        intro hzero
        rw [hzero, Nat.mul_zero] at hprefixMulEq
        omega
      have hprefixPhi :
          3 ^ q.length * prefixValue + gapPhiScaled q = 2 ^ gapPromotedSum q := by
        calc
          3 ^ q.length * prefixValue + gapPhiScaled q = diff + gapPhiScaled q := by
            rw [hprefixEq]
          _ = 2 ^ gapPromotedSum q := by
            dsimp [diff]
            simpa [Nat.add_comm] using Nat.sub_add_cancel (Nat.le_of_lt hltPhi)
      have hprefixKeep : q.length = oddSteps ∨ prefixValue % 3 ≠ 0 := by
        right
        intro hmod
        have hdvdprefix : 3 ∣ prefixValue := Nat.dvd_of_mod_eq_zero hmod
        have hdvdprod : 3 ∣ 2 ^ (gap + 1) * prefixValue := dvd_mul_of_dvd_right hdvdprefix _
        have hnotdvd : ¬ 3 ∣ 3 * value + 1 := by
          intro hd
          rcases hd with ⟨m, hm⟩
          omega
        apply hnotdvd
        rw [← hprefixMulEq]
        exact hdvdprod
      rcases ih q.length prefixValue (by rfl) (by omega) hbudgetq hskipq hprefixPos hprefixPhi hprefixKeep
        with ⟨parentKey, hparent, hparentZeros, hparentValue⟩
      let childKey : GapValueKey := { usedZeros := (q ++ [gap]).sum, value := value }
      have hgapLe :
          gap ≤ exactGapUpper bitLength oddSteps parentKey := by
        rw [exactGapUpper, hparentZeros]
        omega
      have hnumEq : 2 ^ (gap + 1) * prefixValue - 1 = 3 * value := by
        omega
      have hskipLocal : (!(q.length == 0 && gap == 1)) = true := by
        by_cases hq0 : q.length = 0
        · have hqnil : q = [] := by
            cases q with
            | nil => rfl
            | cons x xs => simp at hq0
          have hgapne : gap ≠ 1 := by
            intro hg1
            apply hskipP
            simp [hqnil, hg1]
          simp [hq0, hgapne]
        · simp [hq0]
      have hkeepLocal :
          ((oddSteps - q.length == 1) ||
              (((2 ^ (gap + 1) * prefixValue - 1) / 3) % 3 != 0)) = true := by
        cases hkeep with
        | inl hlast =>
            have hrem : oddSteps - q.length = 1 := by omega
            simp [hrem, hnumEq]
        | inr hmod =>
            simp [hnumEq, hmod]
      have hnext :
          exactGapNextKey? bitLength oddSteps q.length parentKey gap = some childKey := by
        unfold exactGapNextKey?
        rw [if_pos hltPlaced]
        rw [if_pos hgapLe]
        have hmodZero : ((2 ^ (gap + 1) * parentKey.value - 1) % 3 == 0) = true := by
          rw [hparentValue, hnumEq]
          simp
        rw [if_pos hmodZero]
        rw [if_pos hskipLocal]
        have hdivEq' : (2 ^ (gap + 1) * prefixValue - 1) / 3 = value := by
          rw [hnumEq]
          simp
        have hkeepLocal' : (oddSteps - q.length == 1 || value % 3 != 0) = true := by
          simpa [hdivEq'] using hkeepLocal
        rw [hparentValue, hdivEq', hparentZeros]
        rw [if_pos hkeepLocal']
        simp [childKey]
      refine ⟨childKey, ?_, ?_, ?_⟩
      · rw [← hlenq, pathStates]
        simp only [List.mem_flatMap, List.mem_map]
        refine ⟨(q, parentKey), hparent, ?_⟩
        refine ⟨{ gap := gap, nextKey := childKey }, ?_, rfl⟩
        exact (mem_exactStateTransitionsList_iff bitLength oddSteps q.length parentKey
          { gap := gap, nextKey := childKey }).2
            ⟨Nat.lt_succ_iff.mpr hgapLe, hnext⟩
      · simp [childKey]
      · simp [childKey]

/-- Public list-level admissibility predicate for completed gap sequences. -/
def gapAdmissible (bitLength oddSteps : Nat) (p : List Nat) : Prop :=
  ∃ key, (p, key) ∈ pathStates bitLength oddSteps oddSteps

theorem gapAdmissible_length
    {bitLength oddSteps : Nat} {p : List Nat}
    (hadm : gapAdmissible bitLength oddSteps p) :
    p.length = oddSteps := by
  rcases hadm with ⟨key, hkey⟩
  rcases pathStates_gapSemantics bitLength oddSteps oddSteps (p, key) hkey with ⟨hlen, _, _⟩
  exact hlen

theorem gapAdmissible_zeroBudget
    {bitLength oddSteps : Nat} {p : List Nat}
    (hadm : gapAdmissible bitLength oddSteps p) :
    p.sum ≤ bitLength - oddSteps := by
  rcases hadm with ⟨key, hkey⟩
  exact pathStates_zeroBudget bitLength oddSteps oddSteps (p, key) hkey

theorem gapAdmissible_final_congruence
    {bitLength oddSteps : Nat} {p : List Nat}
    (hadm : gapAdmissible bitLength oddSteps p) :
    gapPhiScaled p ≡ 2 ^ gapPromotedSum p [MOD 3 ^ oddSteps] := by
  rcases hadm with ⟨key, hkey⟩
  simpa using (pathStates_final_congruence (bitLength := bitLength) (oddSteps := oddSteps)
    (pk := (p, key)) hkey)

theorem gapAdmissible_exactIdentity
    {bitLength oddSteps : Nat} {p : List Nat}
    (hadm : gapAdmissible bitLength oddSteps p) :
    ∃ value : Nat, 0 < value ∧
      3 ^ oddSteps * value + gapPhiScaled p = 2 ^ gapPromotedSum p := by
  rcases hadm with ⟨key, hkey⟩
  refine ⟨key.value, ?_, ?_⟩
  · exact pathStates_value_pos bitLength oddSteps oddSteps (p, key) hkey
  · rcases pathStates_gapSemantics bitLength oddSteps oddSteps (p, key) hkey with
      ⟨_hlen, _hzeros, hphi⟩
    simpa using hphi

theorem gapAdmissible_phi_lt
    {bitLength oddSteps : Nat} {p : List Nat}
    (hadm : gapAdmissible bitLength oddSteps p) :
    gapPhiScaled p < 2 ^ gapPromotedSum p := by
  rcases gapAdmissible_exactIdentity hadm with ⟨value, hvalue, hphi⟩
  have hpos : 0 < 3 ^ oddSteps * value := by
    exact Nat.mul_pos (Nat.pow_pos (by decide : 0 < 3)) hvalue
  calc
    gapPhiScaled p < 3 ^ oddSteps * value + gapPhiScaled p := Nat.lt_add_of_pos_left hpos
    _ = 2 ^ gapPromotedSum p := hphi

theorem gapAdmissible_head_ne_one
    {bitLength oddSteps : Nat} {p : List Nat}
    (hadm : gapAdmissible bitLength oddSteps p) :
    oddSteps = 0 ∨ p.head? ≠ some 1 := by
  rcases hadm with ⟨key, hkey⟩
  simpa using pathStates_head_ne_one bitLength oddSteps oddSteps (p, key) hkey

theorem gapAdmissible_of_exactIdentity_of_head_ne_one
    {bitLength oddSteps : Nat} {p : List Nat}
    (hlen : p.length = oddSteps)
    (hbudget : p.sum ≤ bitLength - oddSteps)
    (hskip : oddSteps = 0 ∨ p.head? ≠ some 1)
    (hphi : ∃ value : Nat, 0 < value ∧
      3 ^ oddSteps * value + gapPhiScaled p = 2 ^ gapPromotedSum p) :
    gapAdmissible bitLength oddSteps p := by
  rcases hphi with ⟨value, hvalue, hphi⟩
  rcases mem_pathStates_of_exactSemantics bitLength oddSteps oddSteps p value
      hlen (le_rfl) hbudget hskip hvalue hphi (Or.inl rfl)
    with ⟨key, hkey, _hzeros, _hvalue⟩
  exact ⟨key, hkey⟩

theorem gapAdmissible_of_final_congruence_of_lt_of_head_ne_one
    {bitLength oddSteps : Nat} {p : List Nat}
    (hlen : p.length = oddSteps)
    (hbudget : p.sum ≤ bitLength - oddSteps)
    (hskip : oddSteps = 0 ∨ p.head? ≠ some 1)
    (hlt : gapPhiScaled p < 2 ^ gapPromotedSum p)
    (hcong : gapPhiScaled p ≡ 2 ^ gapPromotedSum p [MOD 3 ^ oddSteps]) :
    gapAdmissible bitLength oddSteps p := by
  have hle : gapPhiScaled p ≤ 2 ^ gapPromotedSum p := Nat.le_of_lt hlt
  rw [Nat.modEq_iff_dvd' hle] at hcong
  rcases hcong with ⟨value, hEq⟩
  have hvaluePos : 0 < value := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero, Nat.mul_zero] at hEq
    exact (Nat.ne_of_gt (Nat.sub_pos_of_lt hlt)) hEq
  have hphi : 3 ^ oddSteps * value + gapPhiScaled p = 2 ^ gapPromotedSum p := by
    omega
  exact gapAdmissible_of_exactIdentity_of_head_ne_one hlen hbudget hskip
    ⟨value, hvaluePos, hphi⟩

def gapFinalSemantics (bitLength oddSteps : Nat) (p : List Nat) : Prop :=
  p.length = oddSteps ∧
  p.sum ≤ bitLength - oddSteps ∧
  (oddSteps = 0 ∨ p.head? ≠ some 1) ∧
  gapPhiScaled p < 2 ^ gapPromotedSum p ∧
  gapPhiScaled p ≡ 2 ^ gapPromotedSum p [MOD 3 ^ oddSteps]

instance instDecidableGapFinalSemantics (bitLength oddSteps : Nat) (p : List Nat) :
    Decidable (gapFinalSemantics bitLength oddSteps p) := by
  unfold gapFinalSemantics
  infer_instance

theorem gapAdmissible_iff_finalSemantics
    {bitLength oddSteps : Nat} {p : List Nat} :
    gapAdmissible bitLength oddSteps p ↔ gapFinalSemantics bitLength oddSteps p := by
  constructor
  · intro hadm
    exact ⟨gapAdmissible_length hadm, gapAdmissible_zeroBudget hadm,
      gapAdmissible_head_ne_one hadm, gapAdmissible_phi_lt hadm,
      gapAdmissible_final_congruence hadm⟩
  · rintro ⟨hlen, hbudget, hskip, hlt, hcong⟩
    exact gapAdmissible_of_final_congruence_of_lt_of_head_ne_one
      hlen hbudget hskip hlt hcong

/-- The exact end-key of an admissible gap path is uniquely determined by the
gap list itself. -/
theorem pathStates_key_determined
    {bitLength oddSteps placed : Nat}
    {pk pk' : List Nat × GapValueKey}
    (hpk : pk ∈ pathStates bitLength oddSteps placed)
    (hpk' : pk' ∈ pathStates bitLength oddSteps placed)
    (hfst : pk.1 = pk'.1) :
    pk = pk' := by
  rcases pathStates_gapSemantics bitLength oddSteps placed pk hpk with ⟨_hlen, hzeros, hphi⟩
  rcases pathStates_gapSemantics bitLength oddSteps placed pk' hpk' with ⟨_hlen', hzeros', hphi'⟩
  have hused : pk.2.usedZeros = pk'.2.usedZeros := by
    rw [hzeros, hzeros', hfst]
  have hmul : 3 ^ placed * pk.2.value = 3 ^ placed * pk'.2.value := by
    rw [hfst] at hphi
    omega
  have hpowpos : 0 < 3 ^ placed := by
    exact Nat.pow_pos (by decide : 0 < 3)
  have hvalue : pk.2.value = pk'.2.value := Nat.eq_of_mul_eq_mul_left hpowpos hmul
  have hkey : pk.2 = pk'.2 := by
    cases hk : pk.2
    cases hk' : pk'.2
    simp [GapValueKey.mk.injEq] at hused hvalue ⊢
    refine ⟨?_, ?_⟩
    · simpa [hk, hk'] using hused
    · simpa [hk, hk'] using hvalue
  exact Prod.ext hfst hkey

theorem gapAdmissible_key_unique
    {bitLength oddSteps : Nat} {p : List Nat} {key key' : GapValueKey}
    (hkey : (p, key) ∈ pathStates bitLength oddSteps oddSteps)
    (hkey' : (p, key') ∈ pathStates bitLength oddSteps oddSteps) :
    key = key' := by
  exact congrArg Prod.snd (pathStates_key_determined hkey hkey' rfl)

theorem map_gap_exactStateTransitionsList
    (bitLength oddSteps placed : Nat) (key : GapValueKey) :
    (exactStateTransitionsList bitLength oddSteps placed key).map (·.gap) =
      (List.range (exactGapUpper bitLength oddSteps key + 1)).filterMap
        (fun gap => (exactGapNextKey? bitLength oddSteps placed key gap).map (fun _ => gap)) := by
  unfold exactStateTransitionsList
  rw [List.map_filterMap]
  congr 1
  funext gap
  rw [Option.map_map]
  rfl

theorem nodup_gaps_exactStateTransitionsList
    (bitLength oddSteps placed : Nat) (key : GapValueKey) :
    ((exactStateTransitionsList bitLength oddSteps placed key).map (·.gap)).Nodup := by
  rw [List.nodup_iff_pairwise_ne, map_gap_exactStateTransitionsList, List.pairwise_filterMap]
  refine (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp ?_
  intro a a' hne b hb b' hb'
  have ha : b = a := by
    rcases Option.map_eq_some_iff.mp hb with ⟨x, _, rfl⟩
    rfl
  have ha' : b' = a' := by
    rcases Option.map_eq_some_iff.mp hb' with ⟨x, _, rfl⟩
    rfl
  omega

theorem nodup_exactStateTransitionsList
    (bitLength oddSteps placed : Nat) (key : GapValueKey) :
    (exactStateTransitionsList bitLength oddSteps placed key).Nodup :=
  (nodup_gaps_exactStateTransitionsList bitLength oddSteps placed key).of_map

private theorem nodup_flatMap_aux {α β : Type} {l : List α} {f : α → List β}
    (hl : l.Nodup)
    (hf : ∀ a ∈ l, (f a).Nodup)
    (hdisj : ∀ a ∈ l, ∀ a' ∈ l, a ≠ a' → ∀ b, b ∈ f a → b ∈ f a' → False) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.nodup_append]
      rcases List.nodup_cons.mp hl with ⟨hnotmem, hl'⟩
      refine ⟨hf a (by simp), ?_, ?_⟩
      · exact ih hl'
          (fun a' ha' => hf a' (by simp [ha']))
          (fun a₁ h₁ a₂ h₂ => hdisj a₁ (by simp [h₁]) a₂ (by simp [h₂]))
      · intro b hb b' hb' hEq
        subst hEq
        rcases List.mem_flatMap.mp hb' with ⟨a', ha', hba'⟩
        have hne : a ≠ a' := fun hEq' => hnotmem (hEq' ▸ ha')
        exact hdisj a (by simp) a' (by simp [ha']) hne b hb hba'

theorem nodup_pathStates (bitLength oddSteps : Nat) :
    ∀ placed, (pathStates bitLength oddSteps placed).Nodup := by
  intro placed
  induction placed with
  | zero => simp [pathStates]
  | succ placed ih =>
      rw [pathStates]
      refine nodup_flatMap_aux ih ?_ ?_
      · intro pk _
        refine List.Nodup.map_on ?_ (nodup_exactStateTransitionsList bitLength oddSteps placed pk.2)
        intro tr htr tr' htr' hEq
        simp only [Prod.mk.injEq] at hEq
        rcases hEq with ⟨hpath, hkeyEq⟩
        have hgap : tr.gap = tr'.gap := by
          have := List.append_cancel_left hpath
          simpa using this
        cases tr
        cases tr'
        simp_all
      · intro pk hpk pk' hpk' hne b hb hb'
        rcases List.mem_map.mp hb with ⟨tr, _, rfl⟩
        rcases List.mem_map.mp hb' with ⟨tr', _, hEq⟩
        have hfst : pk'.1 ++ [tr'.gap] = pk.1 ++ [tr.gap] := by
          have := congrArg Prod.fst hEq
          simpa using this
        have hlen : pk'.1.length = pk.1.length := by
          rcases pathStates_gapSemantics bitLength oddSteps placed pk hpk with ⟨h1, _, _⟩
          rcases pathStates_gapSemantics bitLength oddSteps placed pk' hpk' with ⟨h2, _, _⟩
          rw [h1, h2]
        have hparents : pk'.1 = pk.1 :=
          (List.append_inj hfst hlen).1
        exact hne (pathStates_key_determined hpk hpk' hparents.symm)

/-- The list of admissible gap prefixes, forgetting the deterministic end key. -/
def admissibleGapPrefixes (bitLength oddSteps : Nat) (placed : Nat) : List (List Nat) :=
  (pathStates bitLength oddSteps placed).map Prod.fst

theorem mem_admissibleGapPrefixes_iff
    {bitLength oddSteps placed : Nat} {p : List Nat} :
    p ∈ admissibleGapPrefixes bitLength oddSteps placed ↔
      ∃ key, (p, key) ∈ pathStates bitLength oddSteps placed := by
  unfold admissibleGapPrefixes
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨pk, hpk, hfst⟩
    rcases pk with ⟨p', key⟩
    simp at hfst
    subst hfst
    exact ⟨key, hpk⟩
  · rintro ⟨key, hkey⟩
    exact List.mem_map.mpr ⟨(p, key), hkey, rfl⟩

theorem nodup_admissibleGapPrefixes (bitLength oddSteps placed : Nat) :
    (admissibleGapPrefixes bitLength oddSteps placed).Nodup := by
  unfold admissibleGapPrefixes
  refine List.Nodup.map_on ?_ (nodup_pathStates bitLength oddSteps placed)
  intro pk hpk pk' hpk' hfst
  exact pathStates_key_determined hpk hpk' hfst

theorem gapAdmissible_iff_mem_admissibleGapPrefixes
    {bitLength oddSteps : Nat} {p : List Nat} :
    gapAdmissible bitLength oddSteps p ↔
      p ∈ admissibleGapPrefixes bitLength oddSteps oddSteps := by
  constructor
  · rintro ⟨key, hkey⟩
    exact (mem_admissibleGapPrefixes_iff).2 ⟨key, hkey⟩
  · intro hmem
    exact (mem_admissibleGapPrefixes_iff).1 hmem

/-! ### The counting payoff: the DP total counts admissible gap sequences -/

theorem pathCount_eq_length_admissibleGapPrefixes
    (bitLength oddSteps placed : Nat) :
    pathCount bitLength oddSteps placed =
      (admissibleGapPrefixes bitLength oddSteps placed).length := by
  unfold pathCount admissibleGapPrefixes
  simp

/-- Coefficient count by total internal zeros among completed admissible gap
prefixes. This is the exact combinatorial coefficient surface behind the
bit-length diagonal counts. -/
def admissibleGapZeroCount (bitLength oddSteps zeros : Nat) : Nat :=
  (admissibleGapPrefixes bitLength oddSteps oddSteps).countP
    (fun p => p.sum == zeros)

theorem admissibleGapZeroCount_eq_length_filter
    (bitLength oddSteps zeros : Nat) :
    admissibleGapZeroCount bitLength oddSteps zeros =
      ((admissibleGapPrefixes bitLength oddSteps oddSteps).filter
        (fun p => p.sum == zeros)).length := by
  unfold admissibleGapZeroCount
  rw [List.countP_eq_length_filter]

theorem admissibleGapZeroCount_eq_zero_of_lt
    {bitLength oddSteps zeros : Nat}
    (hlt : bitLength - oddSteps < zeros) :
    admissibleGapZeroCount bitLength oddSteps zeros = 0 := by
  rw [admissibleGapZeroCount_eq_length_filter]
  have hnil :
      (admissibleGapPrefixes bitLength oddSteps oddSteps).filter
        (fun p => p.sum == zeros) = [] := by
    apply List.filter_eq_nil_iff.2
    intro p hp
    have hadm :
        gapAdmissible bitLength oddSteps p := by
      exact (gapAdmissible_iff_mem_admissibleGapPrefixes).2 hp
    have hbudget : p.sum ≤ bitLength - oddSteps :=
      gapAdmissible_zeroBudget hadm
    have hne : p.sum ≠ zeros := by
      omega
    simp [hne]
  simp [hnil]

/-- The multiset of total internal-zero counts of completed admissible gap
prefixes. -/
def admissibleGapZeroSums (bitLength oddSteps : Nat) : List Nat :=
  (admissibleGapPrefixes bitLength oddSteps oddSteps).map List.sum

theorem admissibleGapZeroCount_eq_count
    (bitLength oddSteps zeros : Nat) :
    admissibleGapZeroCount bitLength oddSteps zeros =
      (admissibleGapZeroSums bitLength oddSteps).count zeros := by
  unfold admissibleGapZeroCount admissibleGapZeroSums
  rw [List.count_eq_countP, List.countP_map]
  rfl

/-- All gap lists of a fixed length with exact prescribed total sum. -/
def gapListsWithSum : Nat → Nat → List (List Nat)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | len + 1, zeros =>
      (List.range (zeros + 1)).flatMap fun gap =>
        (gapListsWithSum len (zeros - gap)).map fun p => gap :: p

theorem mem_gapListsWithSum_iff
    {len zeros : Nat} {p : List Nat} :
    p ∈ gapListsWithSum len zeros ↔ p.length = len ∧ p.sum = zeros := by
  induction len generalizing zeros p with
  | zero =>
      cases zeros with
      | zero =>
          cases p <;> simp [gapListsWithSum]
      | succ zeros =>
          cases p <;> simp [gapListsWithSum]
  | succ len ih =>
      constructor
      · intro hp
        simp only [gapListsWithSum, List.mem_flatMap, List.mem_map] at hp
        rcases hp with ⟨gap, hgap, tail, htail, rfl⟩
        rcases (ih.mp htail) with ⟨hlen, hsum⟩
        have hgapLe : gap ≤ zeros := Nat.lt_succ_iff.mp (List.mem_range.mp hgap)
        constructor
        · simp [hlen]
        · simp [hsum, Nat.add_sub_of_le hgapLe]
      · intro hp
        cases p with
        | nil =>
            simpa using hp.1
        | cons gap tail =>
            have hgapLe : gap ≤ zeros := by
              have hsum : gap + tail.sum = zeros := by simpa using hp.2
              omega
            have hmemGap : gap ∈ List.range (zeros + 1) := by
              simpa [List.mem_range] using Nat.lt_succ_iff.mpr hgapLe
            have htailLen : tail.length = len := by
              simpa using hp.1
            have htailSum : tail.sum = zeros - gap := by
              have hsum : gap + tail.sum = zeros := by simpa using hp.2
              omega
            have hmemTail : tail ∈ gapListsWithSum len (zeros - gap) := by
              exact ih.mpr ⟨htailLen, htailSum⟩
            exact List.mem_flatMap.mpr
              ⟨gap, hmemGap, List.mem_map.mpr ⟨tail, hmemTail, rfl⟩⟩

theorem nodup_gapListsWithSum (len zeros : Nat) :
    (gapListsWithSum len zeros).Nodup := by
  induction len generalizing zeros with
  | zero =>
      cases zeros <;> simp [gapListsWithSum]
  | succ len ih =>
      unfold gapListsWithSum
      refine nodup_flatMap_aux (by simpa using (List.nodup_range : (List.range (zeros + 1)).Nodup)) ?_ ?_
      · intro gap hgap
        refine List.Nodup.map_on ?_ (ih (zeros - gap))
        intro p hp p' hp' hEq
        exact (List.cons.inj hEq).2
      · intro gap hgap gap' hgap' hne b hb hb'
        rcases List.mem_map.mp hb with ⟨tail, htail, rfl⟩
        rcases List.mem_map.mp hb' with ⟨tail', htail', hEq⟩
        exact hne ((List.cons.inj hEq.symm).1)

/-- Fixed-sum completed gap lists satisfying the final semantic condition. -/
def finalSemanticsGapPrefixes (bitLength oddSteps zeros : Nat) : List (List Nat) :=
  (gapListsWithSum oddSteps zeros).filter (fun p => decide (gapFinalSemantics bitLength oddSteps p))

theorem mem_finalSemanticsGapPrefixes_iff
    {bitLength oddSteps zeros : Nat} {p : List Nat} :
    p ∈ finalSemanticsGapPrefixes bitLength oddSteps zeros ↔
      p.length = oddSteps ∧ p.sum = zeros ∧ gapFinalSemantics bitLength oddSteps p := by
  unfold finalSemanticsGapPrefixes
  constructor
  · intro hp
    rcases List.mem_filter.mp hp with ⟨hmem, hsem⟩
    rcases (mem_gapListsWithSum_iff.mp hmem) with ⟨hlen, hsum⟩
    exact ⟨hlen, hsum, by simpa using hsem⟩
  · rintro ⟨hlen, hsum, hsem⟩
    refine List.mem_filter.mpr ?_
    exact ⟨(mem_gapListsWithSum_iff.mpr ⟨hlen, hsum⟩), by simpa using hsem⟩

theorem nodup_finalSemanticsGapPrefixes (bitLength oddSteps zeros : Nat) :
    (finalSemanticsGapPrefixes bitLength oddSteps zeros).Nodup := by
  unfold finalSemanticsGapPrefixes
  exact (nodup_gapListsWithSum oddSteps zeros).filter _

theorem admissibleGapZeroCount_eq_length_finalSemanticsGapPrefixes
    (bitLength oddSteps zeros : Nat) :
    admissibleGapZeroCount bitLength oddSteps zeros =
      (finalSemanticsGapPrefixes bitLength oddSteps zeros).length := by
  rw [admissibleGapZeroCount_eq_length_filter]
  have hnodupLeft :
      ((admissibleGapPrefixes bitLength oddSteps oddSteps).filter
        (fun p => p.sum == zeros)).Nodup :=
    (nodup_admissibleGapPrefixes bitLength oddSteps oddSteps).filter _
  have hnodupRight :
      (finalSemanticsGapPrefixes bitLength oddSteps zeros).Nodup :=
    nodup_finalSemanticsGapPrefixes bitLength oddSteps zeros
  have hperm : List.Perm
      ((admissibleGapPrefixes bitLength oddSteps oddSteps).filter
        (fun p => p.sum == zeros))
      (finalSemanticsGapPrefixes bitLength oddSteps zeros) := by
    apply (List.perm_ext_iff_of_nodup hnodupLeft hnodupRight).2
    intro p
    constructor
    · intro hp
      rcases List.mem_filter.mp hp with ⟨hmem, hsumEq⟩
      have hadm : gapAdmissible bitLength oddSteps p :=
        (gapAdmissible_iff_mem_admissibleGapPrefixes).2 hmem
      have hsem : gapFinalSemantics bitLength oddSteps p :=
        (gapAdmissible_iff_finalSemantics).1 hadm
      have hsum : p.sum = zeros := by
        simpa using hsumEq
      exact (mem_finalSemanticsGapPrefixes_iff).2 ⟨hsem.1, hsum, hsem⟩
    · intro hp
      rcases (mem_finalSemanticsGapPrefixes_iff.mp hp) with ⟨_hlen, hsum, hsem⟩
      have hadm : gapAdmissible bitLength oddSteps p :=
        (gapAdmissible_iff_finalSemantics).2 hsem
      have hmem : p ∈ admissibleGapPrefixes bitLength oddSteps oddSteps :=
        (gapAdmissible_iff_mem_admissibleGapPrefixes).1 hadm
      exact List.mem_filter.mpr ⟨hmem, by simp [hsum]⟩
  simpa using hperm.length_eq

theorem mem_admissibleGapZeroSums_lt_bound
    {bitLength oddSteps zeros : Nat}
    (hmem : zeros ∈ admissibleGapZeroSums bitLength oddSteps) :
    zeros ≤ bitLength - oddSteps := by
  unfold admissibleGapZeroSums at hmem
  rcases List.mem_map.mp hmem with ⟨p, hp, hsum⟩
  have hadm : gapAdmissible bitLength oddSteps p :=
    (gapAdmissible_iff_mem_admissibleGapPrefixes).2 hp
  have hbudget := gapAdmissible_zeroBudget hadm
  rw [← hsum]
  exact hbudget

private theorem sum_map_const_one {α : Type} (l : List α) :
    (l.map fun _ => (1 : Nat)).sum = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Nat.add_comm]

theorem exactStageMass_exactStageAt_eq_pathCount
    (bitLength oddSteps placed : Nat) :
    exactStageMass (exactStageAt bitLength oddSteps placed) =
      pathCount bitLength oddSteps placed := by
  have hsw :
      exactStageWeightedSum (fun _ => 1) (exactStageAt bitLength oddSteps placed) =
        exactStageMass (exactStageAt bitLength oddSteps placed) := by
    rw [exactStageWeightedSum_eq_sum_map, exactStageMass_eq_sum_map_snd]
    simp
  have hpw :
      pathWeight bitLength oddSteps placed (fun _ => 1) =
        pathCount bitLength oddSteps placed := by
    unfold pathWeight pathCount
    exact sum_map_const_one _
  rw [← hsw, ← hpw]
  exact exactStageWeightedSum_exactStageAt_eq_pathWeight bitLength oddSteps placed _

/-- The public residue-DP total equals the number of admissible gap sequences:
the DP is, provably, a counter of reverse-Collatz paths. -/
theorem totalCount_eq_pathCount (bitLength oddSteps : Nat) :
    totalCount bitLength oddSteps = pathCount bitLength oddSteps oddSteps := by
  rw [← exactTotalCount_eq_totalCount, exactTotalCount_eq_exactStageMass_exactStageAt]
  exact exactStageMass_exactStageAt_eq_pathCount bitLength oddSteps oddSteps

theorem totalCount_eq_length_admissibleGapPrefixes
    (bitLength oddSteps : Nat) :
    totalCount bitLength oddSteps =
      (admissibleGapPrefixes bitLength oddSteps oddSteps).length := by
  rw [totalCount_eq_pathCount, pathCount_eq_length_admissibleGapPrefixes]

theorem admissibleGapZeroCount_le_totalCount
    (bitLength oddSteps zeros : Nat) :
    admissibleGapZeroCount bitLength oddSteps zeros ≤ totalCount bitLength oddSteps := by
  rw [admissibleGapZeroCount_eq_length_filter, totalCount_eq_length_admissibleGapPrefixes]
  exact List.length_filter_le _ _

/-! ### Degenerate regime: more odd steps than bits -/

theorem exactStateTransitionsList_seed_eq_nil_of_lt
    {bitLength oddSteps : Nat} (hlt : bitLength < oddSteps) :
    exactStateTransitionsList bitLength oddSteps 0
      ({ usedZeros := 0, value := 1 } : GapValueKey) = [] := by
  unfold exactStateTransitionsList
  apply List.filterMap_eq_nil_iff.mpr
  intro gap hgap
  have hupper : exactGapUpper bitLength oddSteps
      ({ usedZeros := 0, value := 1 } : GapValueKey) = 0 := by
    unfold exactGapUpper
    omega
  rw [List.mem_range, hupper] at hgap
  have hgap0 : gap = 0 := by omega
  subst hgap0
  unfold exactGapNextKey?
  dsimp only
  rw [if_pos (by omega : (0 : Nat) < oddSteps)]
  rw [if_pos (by rw [hupper] : (0 : Nat) ≤ exactGapUpper bitLength oddSteps _)]
  rw [if_neg (by decide : ¬((2 ^ (0 + 1) * 1 - 1) % 3 == 0) = true)]
  rfl

theorem pathStates_eq_nil_of_lt
    {bitLength oddSteps : Nat} (hlt : bitLength < oddSteps) :
    ∀ j, 1 ≤ j → pathStates bitLength oddSteps j = [] := by
  intro j
  induction j with
  | zero => omega
  | succ j ih =>
      intro _
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        simp [pathStates, exactStateTransitionsList_seed_eq_nil_of_lt hlt]
      · rw [pathStates, ih hj]
        rfl

/-- With more odd steps than bits, the DP counts nothing. -/
theorem totalCount_eq_zero_of_lt
    {bitLength oddSteps : Nat} (hlt : bitLength < oddSteps) :
    totalCount bitLength oddSteps = 0 := by
  rw [totalCount_eq_pathCount]
  unfold pathCount
  rw [pathStates_eq_nil_of_lt hlt oddSteps (by omega)]
  rfl

end CollatzThreeAdic
