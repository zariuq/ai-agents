import Mathlib.Logic.Equiv.Nat
import Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
import Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
import Mettapedia.Logic.MarkovLogicInfiniteWorldModel

/-!
# Infinite 2D Grid MLN in the Dobrushin Regime

The atom space is `Nat × Nat`: an unbounded rectangular lattice of Boolean
variables.  Each nearest-neighbour pair shares a weighted clause with log-weight
`w`.  A clause like `{neg (i,j), pos (i+1,j)}` couples the two nodes
**bidirectionally** at the Dobrushin level: flipping either node shifts the
other's conditional probability.  Energetically, however, this file models an
oriented ferromagnetic implication lattice, not the spin-flip-symmetric Ising
Hamiltonian.  The symmetric Ising encoding would add the reverse implication
clause for every edge.

Each interior node has four interacting neighbours — two horizontal, two
vertical — giving a Dobrushin row sum of `2|w|`.  The uniqueness budget is
therefore `2|w| < 1`, or equivalently `|w| < 1/2`.

This is the high-temperature (Dobrushin uniqueness) regime for a concrete
2D lattice MLN.

**Positive example.**  `w = 0.2` (odds multiplier `e^0.2 ≈ 1.22`).  Budget
`2 × 0.2 = 0.4 < 1`.  The probability at sensor `(15, 23)` is uniquely
determined, regardless of boundary conditions at infinity.

**Negative example.**  `w = 0.6`.  Budget `2 × 0.6 = 1.2 ≥ 1`.  This is outside
the Dobrushin regime: coexisting boundary-driven equilibria become possible and
the proved uniqueness theorem does not apply.
-/

namespace Mettapedia.Logic.MarkovLogicInfiniteGridExample

open scoped ENNReal
open MeasureTheory
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteFiniteVolume
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteExhaustion
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteCylinders
open Mettapedia.Logic.MarkovLogicInfiniteBoundaryStability
open Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldMeasures
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel

/-- Countable grid nodes. -/
abbrev GridNode := Nat × Nat

/-- The origin site used for the concrete phase-coexistence observable. -/
def gridOrigin : GridNode := (0, 0)

/-- All-plus boundary condition for zero-field grid finite-volume limits. -/
def gridPlusBoundary : BoundaryCondition GridNode := fun _ => true

/-- All-minus boundary condition for zero-field grid finite-volume limits. -/
def gridMinusBoundary : BoundaryCondition GridNode := fun _ => false

/-- Global finite query: the origin spin is up/true. -/
def gridOriginSpinUpQuery : ConstraintQuery GridNode :=
  [⟨gridOrigin, true⟩]

/-- Local one-site query: the origin spin is up/true. -/
def gridOriginSpinUpLocalQuery :
    LocalConstraintQuery GridNode ({gridOrigin} : Region GridNode) :=
  [⟨⟨gridOrigin, by simp [gridOrigin]⟩, true⟩]

/-- The local origin-spin query denotes exactly the singleton true-assignment
set on the origin cylinder. -/
theorem gridOriginSpinUpLocalConstraintSet_eq :
    Mettapedia.Logic.MarkovLogicInfiniteCylinders.localConstraintSet
      ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery =
      singletonTrueAssignmentSet gridOrigin := by
  ext x
  constructor
  · intro hx
    have hmem :
        (⟨⟨gridOrigin, by simp [gridOrigin]⟩, true⟩ :
          Sigma fun _ : RegionAtom GridNode ({gridOrigin} : Region GridNode) => Bool) ∈
            gridOriginSpinUpLocalQuery := by
      simp [gridOriginSpinUpLocalQuery]
    have h := hx _ hmem
    simpa [singletonTrueAssignmentSet] using h
  · intro hx c hc
    simp [gridOriginSpinUpLocalQuery] at hc
    rcases hc with rfl
    simpa [singletonTrueAssignmentSet] using hx

/-- The global origin-spin event is the same cylinder event used by the local
DLR/Walley readout. -/
theorem gridOriginSpinUpEvent_eq_cylinder :
    infiniteQueryEvent gridOriginSpinUpQuery =
      MeasureTheory.cylinder ({gridOrigin} : Region GridNode)
        (singletonTrueAssignmentSet gridOrigin) := by
  ext ω
  simp [infiniteQueryEvent, gridOriginSpinUpQuery, satisfiesConstraints,
    MeasureTheory.mem_cylinder, singletonTrueAssignmentSet, gridOrigin]

/-- The local and global presentations of the origin-spin event are the same
measurable cylinder. -/
theorem gridOriginSpinUpLocalQueryEvent_eq_global :
    localQueryEvent ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery =
      infiniteQueryEvent gridOriginSpinUpQuery := by
  rw [localQueryEvent_eq_cylinder]
  rw [gridOriginSpinUpLocalConstraintSet_eq]
  rw [gridOriginSpinUpEvent_eq_cylinder]

/-- Clause ids for the infinite 2D grid. -/
inductive GridClauseId where
  | prior : Nat → Nat → GridClauseId
  | horizontal : Nat → Nat → GridClauseId
  | vertical : Nat → Nat → GridClauseId
deriving DecidableEq

/-- Soft bias on a single grid node. -/
def gridPriorClause (i j : Nat) : GroundClause GridNode :=
  {Literal.pos (i, j)}

/-- Horizontal nearest-neighbour influence. -/
def gridHorizontalClause (i j : Nat) : GroundClause GridNode :=
  {Literal.neg (i, j), Literal.pos (i + 1, j)}

/-- Vertical nearest-neighbour influence. -/
def gridVerticalClause (i j : Nat) : GroundClause GridNode :=
  {Literal.neg (i, j), Literal.pos (i, j + 1)}

/-- Underlying clause attached to a grid clause id. -/
def gridClause : GridClauseId → GroundClause GridNode
  | .prior i j => gridPriorClause i j
  | .horizontal i j => gridHorizontalClause i j
  | .vertical i j => gridVerticalClause i j

@[simp] theorem gridPriorClause_atoms (i j : Nat) :
    (gridPriorClause i j).atoms = ({(i, j)} : Finset GridNode) := by
  ext a
  simp [gridPriorClause, GroundClause.atoms, Literal.atom]

@[simp] theorem gridHorizontalClause_atoms (i j : Nat) :
    (gridHorizontalClause i j).atoms = ({(i, j), (i + 1, j)} : Finset GridNode) := by
  ext a
  simp [gridHorizontalClause, GroundClause.atoms, Literal.atom]

@[simp] theorem gridVerticalClause_atoms (i j : Nat) :
    (gridVerticalClause i j).atoms = ({(i, j), (i, j + 1)} : Finset GridNode) := by
  ext a
  simp [gridVerticalClause, GroundClause.atoms, Literal.atom]

/-- Finite clause support for a finite grid region. -/
noncomputable def gridRegionSupport (Λ : Region GridNode) : Finset GridClauseId :=
  (Λ.image (fun p => GridClauseId.prior p.1 p.2)) ∪
    ((Λ.image (fun p => GridClauseId.horizontal p.1 p.2)) ∪
      (((Λ.image fun p => (Nat.pred p.1, p.2)).image
          (fun p => GridClauseId.horizontal p.1 p.2)) ∪
        ((Λ.image (fun p => GridClauseId.vertical p.1 p.2)) ∪
          (((Λ.image fun p => (p.1, Nat.pred p.2)).image
              (fun p => GridClauseId.vertical p.1 p.2))))))

theorem gridRegionSupport_sound
    {Λ : Region GridNode} {j : GridClauseId}
    (hj : j ∈ gridRegionSupport Λ) :
    clauseTouchesRegion (gridClause j) Λ := by
  rw [gridRegionSupport] at hj
  rcases Finset.mem_union.mp hj with hprior | hrest
  · rcases Finset.mem_image.mp hprior with ⟨p, hpΛ, rfl⟩
    refine ⟨p, ?_, hpΛ⟩
    simp [gridClause]
  · rcases Finset.mem_union.mp hrest with hhorOut | hrest
    · rcases Finset.mem_image.mp hhorOut with ⟨p, hpΛ, rfl⟩
      refine ⟨p, ?_, hpΛ⟩
      simp [gridClause]
    · rcases Finset.mem_union.mp hrest with hhorIn | hrest
      · rcases Finset.mem_image.mp hhorIn with ⟨p, hp, rfl⟩
        rcases Finset.mem_image.mp hp with ⟨a, haΛ, hpred⟩
        by_cases hzero : a.1 = 0
        · rcases a with ⟨i, j⟩
          simp at hzero
          subst hzero
          have hp0 : p = (0, j) := by
            simpa using hpred.symm
          subst hp0
          refine ⟨(0, j), ?_, by simpa using haΛ⟩
          simp [gridClause]
        · rcases a with ⟨i, j⟩
          have hi_pos : 0 < i := Nat.pos_of_ne_zero hzero
          have hpEq : p = (Nat.pred i, j) := by
            simpa using hpred.symm
          subst hpEq
          refine ⟨(i, j), ?_, by simpa using haΛ⟩
          have hmem : (i, j) = (Nat.pred i + 1, j) := by
            exact congrArg (fun n => (n, j)) (Nat.succ_pred_eq_of_pos hi_pos).symm
          simpa [gridClause, gridHorizontalClause_atoms] using Or.inr hmem
      · rcases Finset.mem_union.mp hrest with hvertOut | hvertIn
        · rcases Finset.mem_image.mp hvertOut with ⟨p, hpΛ, rfl⟩
          refine ⟨p, ?_, hpΛ⟩
          simp [gridClause]
        · rcases Finset.mem_image.mp hvertIn with ⟨p, hp, rfl⟩
          rcases Finset.mem_image.mp hp with ⟨a, haΛ, hpred⟩
          by_cases hzero : a.2 = 0
          · rcases a with ⟨i, j⟩
            simp at hzero
            subst hzero
            have hp0 : p = (i, 0) := by
              simpa using hpred.symm
            subst hp0
            refine ⟨(i, 0), ?_, by simpa using haΛ⟩
            simp [gridClause]
          · rcases a with ⟨i, j⟩
            have hj_pos : 0 < j := Nat.pos_of_ne_zero hzero
            have hpEq : p = (i, Nat.pred j) := by
              simpa using hpred.symm
            subst hpEq
            refine ⟨(i, j), ?_, by simpa using haΛ⟩
            have hmem : (i, j) = (i, Nat.pred j + 1) := by
              exact congrArg (Prod.mk i) (Nat.succ_pred_eq_of_pos hj_pos).symm
            simpa [gridClause, gridVerticalClause_atoms] using Or.inr hmem

theorem gridRegionSupport_complete
    {Λ : Region GridNode} {j : GridClauseId}
    (hj : clauseTouchesRegion (gridClause j) Λ) :
    j ∈ gridRegionSupport Λ := by
  rcases j with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = (i, j) := by
      simpa [gridClause] using haAtoms
    subst a
    rw [gridRegionSupport]
    exact Finset.mem_union.mpr <| Or.inl <|
      Finset.mem_image.mpr ⟨(i, j), haΛ, rfl⟩
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = (i, j) ∨ a = (i + 1, j) := by
      simpa [gridClause] using haAtoms
    rw [gridRegionSupport]
    rcases ha with haEq | haNext
    · have hmem : (i, j) ∈ Λ := by simpa [haEq] using haΛ
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_image.mpr ⟨(i, j), hmem, rfl⟩
    · have hpredmem : (Nat.pred (i + 1), j) ∈ Finset.image (fun p => (Nat.pred p.1, p.2)) Λ :=
        Finset.mem_image.mpr ⟨(i + 1, j), by simpa [haNext] using haΛ, rfl⟩
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_image.mpr ⟨(Nat.pred (i + 1), j), hpredmem, by simp⟩
  · rcases hj with ⟨a, haAtoms, haΛ⟩
    have ha : a = (i, j) ∨ a = (i, j + 1) := by
      simpa [gridClause] using haAtoms
    rw [gridRegionSupport]
    rcases ha with haEq | haNext
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_union.mpr <| Or.inl <|
              Finset.mem_image.mpr ⟨(i, j), by simpa [haEq] using haΛ, rfl⟩
    · have hpredmem : (i, Nat.pred (j + 1)) ∈ Finset.image (fun p => (p.1, Nat.pred p.2)) Λ :=
        Finset.mem_image.mpr ⟨(i, j + 1), by simpa [haNext] using haΛ, rfl⟩
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_union.mpr <| Or.inr <|
              Finset.mem_image.mpr ⟨(i, Nat.pred (j + 1)), hpredmem, by simp⟩

/-- Square-box exhaustion of the countable grid. -/
def gridExhaustion : RegionExhaustion GridNode where
  region n := (Finset.range (n + 1)).product (Finset.range (n + 1))
  monotone := by
    intro m n hmn a ha
    rcases Finset.mem_product.mp ha with ⟨hi, hj⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr <| lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.succ_le_succ hmn),
       Finset.mem_range.mpr <| lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.succ_le_succ hmn)⟩
  exhaustive := by
    intro a
    rcases a with ⟨i, j⟩
    refine ⟨max i j, Finset.mem_product.mpr ?_⟩
    constructor
    · exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_max_left i j) (Nat.lt_succ_self (max i j)))
    · exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_max_right i j) (Nat.lt_succ_self (max i j)))

/-- Classical 2D oriented-grid MLN with uniform external field `h` and
interaction weight `w`.  The zero-field specialization is the unbiased
plus/minus boundary target for this oriented lattice; a fully symmetric Ising
target would add reverse edge clauses. -/
noncomputable def gridClassicalSpecWithField (h w : ℝ) :
    ClassicalInfiniteGroundMLNSpec GridNode GridClauseId where
  clause := gridClause
  logWeight j := match j with
    | .prior _ _ => h
    | .horizontal _ _ => w
    | .vertical _ _ => w
  regionSupport := gridRegionSupport
  regionSupport_sound := fun hj => gridRegionSupport_sound hj
  regionSupport_complete := fun hj => gridRegionSupport_complete hj

@[simp] theorem gridClassicalSpecWithField_clause
    (h w : ℝ) (j : GridClauseId) :
    (gridClassicalSpecWithField h w).clause j = gridClause j := rfl

@[simp] theorem gridClassicalSpecWithField_logWeight_prior
    (h w : ℝ) (i j : Nat) :
    (gridClassicalSpecWithField h w).logWeight (GridClauseId.prior i j) = h := rfl

@[simp] theorem gridClassicalSpecWithField_logWeight_horizontal
    (h w : ℝ) (i j : Nat) :
    (gridClassicalSpecWithField h w).logWeight (GridClauseId.horizontal i j) = w := rfl

@[simp] theorem gridClassicalSpecWithField_logWeight_vertical
    (h w : ℝ) (i j : Nat) :
    (gridClassicalSpecWithField h w).logWeight (GridClauseId.vertical i j) = w := rfl

@[simp] theorem gridClassicalSpecWithField_regionSupport
    (h w : ℝ) (Λ : Region GridNode) :
    (gridClassicalSpecWithField h w).regionSupport Λ = gridRegionSupport Λ := rfl

/-- The originally-used biased grid MLN.  Its single-site prior is useful for
positive finite examples, but it is not the unbiased plus/minus boundary target
for phase coexistence. -/
noncomputable def gridClassicalSpec (w : ℝ) :
    ClassicalInfiniteGroundMLNSpec GridNode GridClauseId :=
  gridClassicalSpecWithField (Real.log 2) w

/-- Zero-field 2D oriented-grid MLN: the unbiased plus/minus boundary target for
a future low-temperature coexistence proof. -/
noncomputable def gridZeroFieldClassicalSpec (w : ℝ) :
    ClassicalInfiniteGroundMLNSpec GridNode GridClauseId :=
  gridClassicalSpecWithField 0 w

/-- The 2D nearest-neighbour grid has Dobrushin row sum at most `2 * |w|`,
uniformly in the external field.  The field clauses touch only one site, so
they do not contribute to pairwise Dobrushin influence. -/
theorem gridClassicalSpecWithField_uniformSmallTotalInfluence
    (hField : ℝ) {w : ℝ} (hbudget : 2 * |w| < 1) :
    (gridClassicalSpecWithField hField w).PaperUniformSmallTotalInfluence := by
  refine ⟨2 * |w|, by positivity, hbudget, ?_⟩
  intro a
  rcases a with ⟨i, j⟩
  have hrow :
      Finset.sum ((gridClassicalSpecWithField hField w).atomInteractionNeighborhood (i, j))
        (fun b => (gridClassicalSpecWithField hField w).pairwiseDobrushinCoefficient (i, j) b) =
        (1 / 2 : ℝ) * (gridClassicalSpecWithField hField w).atomTotalInfluence (i, j) := by
    rw [(gridClassicalSpecWithField hField w).atomTotalInfluence_eq_sum_pairwiseInfluence]
    simp [ClassicalInfiniteGroundMLNSpec.pairwiseDobrushinCoefficient, Finset.mul_sum]
  rw [hrow]
  have hprior_zero :
      (gridClassicalSpecWithField hField w).clauseInfluenceContribution (GridClauseId.prior i j) = 0 := by
    apply (gridClassicalSpecWithField hField w).clauseInfluenceContribution_eq_zero_of_card_le_one
    simp [gridClassicalSpecWithField, gridClause, gridPriorClause_atoms]
  by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
  · subst hi0; subst hj0
    have hsupp00 :
        (gridClassicalSpecWithField hField w).regionSupport ({(0, 0)} : Finset GridNode) =
          ({GridClauseId.prior 0 0, GridClauseId.horizontal 0 0,
            GridClauseId.vertical 0 0} : Finset GridClauseId) := by
      ext k
      cases k <;> simp [gridClassicalSpecWithField, gridRegionSupport]
    have htot :
        (gridClassicalSpecWithField hField w).atomTotalInfluence (0, 0) = 2 * |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp00]
      simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
        gridClassicalSpecWithField, gridClause, gridHorizontalClause_atoms, gridVerticalClause_atoms]
      ring_nf
    rw [htot]
    nlinarith [abs_nonneg w]
  · subst hi0
    have hjpred_ne : Nat.pred j ≠ j := by
      exact Nat.ne_of_lt (Nat.pred_lt hj0)
    have hsupp0j :
        (gridClassicalSpecWithField hField w).regionSupport ({(0, j)} : Finset GridNode) =
          ({GridClauseId.prior 0 j, GridClauseId.horizontal 0 j,
            GridClauseId.vertical 0 j, GridClauseId.vertical 0 (Nat.pred j)} :
              Finset GridClauseId) := by
      ext k
      cases k <;> simp [gridClassicalSpecWithField, gridRegionSupport]
    have hsumv0j :
        ({GridClauseId.vertical 0 j, GridClauseId.vertical 0 (Nat.pred j)} :
            Finset GridClauseId).sum
          (fun x => (gridClassicalSpecWithField hField w).clauseInfluenceContribution x) =
          |w| + |w| := by
      rw [Finset.sum_pair]
      · simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
          gridClassicalSpecWithField, gridClause]
      · intro h
        simp at h
        exact hjpred_ne h.symm
    have htot :
        (gridClassicalSpecWithField hField w).atomTotalInfluence (0, j) = 3 * |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsupp0j]
      rw [Finset.sum_insert]
      · rw [hprior_zero, zero_add, Finset.sum_insert]
        · rw [hsumv0j]
          simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
            gridClassicalSpecWithField, gridClause]
          ring_nf
        · simp
      · simp
    rw [htot]
    nlinarith [abs_nonneg w]
  · subst hj0
    have hipred_ne : Nat.pred i ≠ i := by
      exact Nat.ne_of_lt (Nat.pred_lt hi0)
    have hsuppi0 :
        (gridClassicalSpecWithField hField w).regionSupport ({(i, 0)} : Finset GridNode) =
          ({GridClauseId.prior i 0, GridClauseId.horizontal i 0,
            GridClauseId.horizontal (Nat.pred i) 0, GridClauseId.vertical i 0} :
              Finset GridClauseId) := by
      ext k
      cases k <;> simp [gridClassicalSpecWithField, gridRegionSupport, or_comm]
    have hsumresti0 :
        ({GridClauseId.horizontal (Nat.pred i) 0, GridClauseId.vertical i 0} :
            Finset GridClauseId).sum
          (fun x => (gridClassicalSpecWithField hField w).clauseInfluenceContribution x) =
          |w| + |w| := by
      rw [Finset.sum_pair]
      · simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
          gridClassicalSpecWithField, gridClause]
      · intro h
        cases h
    have htot :
        (gridClassicalSpecWithField hField w).atomTotalInfluence (i, 0) = 3 * |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsuppi0]
      rw [Finset.sum_insert]
      · rw [hprior_zero, zero_add, Finset.sum_insert]
        · rw [hsumresti0]
          simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
            gridClassicalSpecWithField, gridClause]
          ring_nf
        · intro h
          rcases Finset.mem_insert.mp h with h | h
          · injection h with h1 h2
            exact hipred_ne h1.symm
          · simp at h
      · simp
    rw [htot]
    nlinarith [abs_nonneg w]
  · have hipred_ne : Nat.pred i ≠ i := by
      exact Nat.ne_of_lt (Nat.pred_lt hi0)
    have hjpred_ne : Nat.pred j ≠ j := by
      exact Nat.ne_of_lt (Nat.pred_lt hj0)
    have hsuppij :
        (gridClassicalSpecWithField hField w).regionSupport ({(i, j)} : Finset GridNode) =
          ({GridClauseId.prior i j, GridClauseId.horizontal i j,
            GridClauseId.horizontal (Nat.pred i) j,
            GridClauseId.vertical i j, GridClauseId.vertical i (Nat.pred j)} :
              Finset GridClauseId) := by
      ext k
      cases k <;> simp [gridClassicalSpecWithField, gridRegionSupport, or_comm]
    have hsumvij :
        ({GridClauseId.vertical i j, GridClauseId.vertical i (Nat.pred j)} :
            Finset GridClauseId).sum
          (fun x => (gridClassicalSpecWithField hField w).clauseInfluenceContribution x) =
          |w| + |w| := by
      rw [Finset.sum_pair]
      · simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution,
          gridClassicalSpecWithField, gridClause]
      · intro h
        simp at h
        exact hjpred_ne h.symm
    have htot :
        (gridClassicalSpecWithField hField w).atomTotalInfluence (i, j) = 4 * |w| := by
      rw [ClassicalInfiniteGroundMLNSpec.atomTotalInfluence, hsuppij]
      rw [Finset.sum_insert]
      · rw [hprior_zero, zero_add, Finset.sum_insert]
        · rw [Finset.sum_insert]
          · rw [hsumvij]
            simp [ClassicalInfiniteGroundMLNSpec.clauseInfluenceContribution, gridClassicalSpecWithField,
              gridClause]
            ring_nf
          · simp
        · intro h
          rcases Finset.mem_insert.mp h with h | h
          · injection h with h1 h2
            exact hipred_ne h1.symm
          · simp at h
      · simp
    rw [htot]
    nlinarith [abs_nonneg w]

/-- The originally-used biased grid inherits the field-uniform Dobrushin
bound. -/
theorem gridClassicalSpec_uniformSmallTotalInfluence
    {w : ℝ} (hbudget : 2 * |w| < 1) :
    (gridClassicalSpec w).PaperUniformSmallTotalInfluence := by
  exact gridClassicalSpecWithField_uniformSmallTotalInfluence (Real.log 2) hbudget

/-- The zero-field oriented grid has the same Dobrushin uniqueness budget. -/
theorem gridZeroField_uniformSmallTotalInfluence
    {w : ℝ} (hbudget : 2 * |w| < 1) :
    (gridZeroFieldClassicalSpec w).PaperUniformSmallTotalInfluence := by
  exact gridClassicalSpecWithField_uniformSmallTotalInfluence 0 hbudget

/-- Existence for the infinite 2D grid MLN. -/
theorem exists_grid_fixedRegionCylinderDLR
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    ∃ μ : Measure (InfiniteWorld GridNode),
      ∃ _ : IsProbabilityMeasure μ,
        FixedRegionCylinderDLR
          (gridClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec μ := by
  simpa using
    (gridClassicalSpec w).exists_fixedRegionCylinderDLR_of_equiv
      gridExhaustion ξ (Equiv.prodEquivOfEquivNat (Equiv.refl Nat)).symm

/-- Existence for the zero-field infinite 2D grid MLN, the unbiased target for
the future low-temperature phase-coexistence theorem. -/
theorem exists_gridZeroField_fixedRegionCylinderDLR
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    ∃ μ : Measure (InfiniteWorld GridNode),
      ∃ _ : IsProbabilityMeasure μ,
        FixedRegionCylinderDLR
          (gridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec μ := by
  simpa using
    (gridZeroFieldClassicalSpec w).exists_fixedRegionCylinderDLR_of_equiv
      gridExhaustion ξ (Equiv.prodEquivOfEquivNat (Equiv.refl Nat)).symm

/-- The zero-field grid has at least one DLR completion, packaged in the
credal-bridge completion type. -/
theorem gridZeroField_dlrCompletion_nonempty
    (w : ℝ) :
    Nonempty (DLRCompletion (gridZeroFieldClassicalSpec w)) := by
  rcases exists_gridZeroField_fixedRegionCylinderDLR w (fun _ : GridNode => false) with
    ⟨μ, hμprob, hμdlr⟩
  exact ⟨⟨⟨μ, hμprob⟩, hμdlr⟩⟩

/-- A zero-field DLR completion selected from the finite-volume construction
with boundary `ξ`.  This is a noncomputable choice of the already-proved
cluster-point existence theorem; it does not assert extremality or phase
separation. -/
noncomputable def gridZeroFieldBoundaryCompletion
    (w : ℝ) (ξ : BoundaryCondition GridNode) :
    DLRCompletion (gridZeroFieldClassicalSpec w) := by
  classical
  let hExists := exists_gridZeroField_fixedRegionCylinderDLR w ξ
  let μ := Classical.choose hExists
  let hμExists := Classical.choose_spec hExists
  let hμprob := Classical.choose hμExists
  let hμdlr := Classical.choose_spec hμExists
  exact ⟨⟨μ, hμprob⟩, hμdlr⟩

/-- The zero-field completion selected from all-plus finite-volume boundary
conditions. -/
noncomputable def gridZeroFieldPlusBoundaryCompletion
    (w : ℝ) : DLRCompletion (gridZeroFieldClassicalSpec w) :=
  gridZeroFieldBoundaryCompletion w gridPlusBoundary

/-- The zero-field completion selected from all-minus finite-volume boundary
conditions. -/
noncomputable def gridZeroFieldMinusBoundaryCompletion
    (w : ℝ) : DLRCompletion (gridZeroFieldClassicalSpec w) :=
  gridZeroFieldBoundaryCompletion w gridMinusBoundary

/-- The local and global origin-spin probabilities agree for every zero-field
DLR completion. -/
theorem gridZeroField_originSpinUp_localQueryProb_eq_queryProb
    (w : ℝ) (μ : DLRCompletion (gridZeroFieldClassicalSpec w)) :
    dlrCompletionLocalQueryProb (gridZeroFieldClassicalSpec w)
        ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery μ =
      dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery μ := by
  rw [dlrCompletionQueryProb_eq_toReal_measure_infiniteQueryEvent]
  unfold dlrCompletionLocalQueryProb
  rw [gridOriginSpinUpLocalQueryEvent_eq_global]

/-- On the grid, the deterministic all-true state is not itself a
strictly-positive DLR completion.  The low-temperature plus phase has to be
constructed as a genuine Gibbs measure. -/
theorem grid_dirac_allTrue_not_fixedRegionCylinderDLR
    (w : ℝ) (a : GridNode) :
    ¬ FixedRegionCylinderDLR
      (gridClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (Measure.dirac (fun _ : GridNode => true)) := by
  exact (gridClassicalSpec w).dirac_allTrue_not_fixedRegionCylinderDLR a

/-- On the zero-field grid, the deterministic all-true state is not itself a
strictly-positive DLR completion. -/
theorem gridZeroField_dirac_allTrue_not_fixedRegionCylinderDLR
    (w : ℝ) (a : GridNode) :
    ¬ FixedRegionCylinderDLR
      (gridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (Measure.dirac (fun _ : GridNode => true)) := by
  exact (gridZeroFieldClassicalSpec w).dirac_allTrue_not_fixedRegionCylinderDLR a

/-- On the grid, the deterministic all-false state is not itself a
strictly-positive DLR completion.  The low-temperature minus phase has to be
constructed as a genuine Gibbs measure. -/
theorem grid_dirac_allFalse_not_fixedRegionCylinderDLR
    (w : ℝ) (a : GridNode) :
    ¬ FixedRegionCylinderDLR
      (gridClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (Measure.dirac (fun _ : GridNode => false)) := by
  exact (gridClassicalSpec w).dirac_allFalse_not_fixedRegionCylinderDLR a

/-- On the zero-field grid, the deterministic all-false state is not itself a
strictly-positive DLR completion. -/
theorem gridZeroField_dirac_allFalse_not_fixedRegionCylinderDLR
    (w : ℝ) (a : GridNode) :
    ¬ FixedRegionCylinderDLR
      (gridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (Measure.dirac (fun _ : GridNode => false)) := by
  exact (gridZeroFieldClassicalSpec w).dirac_allFalse_not_fixedRegionCylinderDLR a

/-- End-to-end uniqueness for the infinite 2D grid. -/
theorem grid_uniqueMeasure
    {w : ℝ} (hbudget : 2 * |w| < 1) :
    (gridClassicalSpec w).PaperUniqueMeasure :=
  (gridClassicalSpec w).paperUniformSmallTotalInfluence_implies_paperUniqueMeasure
    (gridClassicalSpec_uniformSmallTotalInfluence hbudget)

/-- End-to-end uniqueness for the zero-field infinite 2D grid in the
high-temperature Dobrushin regime. -/
theorem gridZeroField_uniqueMeasure
    {w : ℝ} (hbudget : 2 * |w| < 1) :
    (gridZeroFieldClassicalSpec w).PaperUniqueMeasure :=
  (gridZeroFieldClassicalSpec w).paperUniformSmallTotalInfluence_implies_paperUniqueMeasure
    (gridZeroField_uniformSmallTotalInfluence hbudget)

/-- End-to-end WM bridge uniqueness for the infinite 2D grid. -/
theorem grid_wmBridge_unique
    {w : ℝ}
    (hbudget : 2 * |w| < 1)
    (μ ν : ProbabilityMeasure (InfiniteWorld GridNode))
    (hμ : FixedRegionCylinderDLR
      (gridClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld GridNode)))
    (hν : FixedRegionCylinderDLR
      (gridClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld GridNode)))
    (q : ConstraintQuery GridNode) :
    (infiniteMLNMassSemantics (gridClassicalSpec w) μ hμ).queryProb q =
    (infiniteMLNMassSemantics (gridClassicalSpec w) ν hν).queryProb q :=
  infiniteMLN_queryStrength_unique_of_uniform
    (gridClassicalSpec w)
    (gridClassicalSpec_uniformSmallTotalInfluence hbudget)
    μ ν hμ hν q

/-- End-to-end WM bridge uniqueness for the zero-field infinite 2D grid:
below the Dobrushin threshold, every finite PLN/WM query has a single
completion-independent truth strength. -/
theorem gridZeroField_wmBridge_unique
    {w : ℝ}
    (hbudget : 2 * |w| < 1)
    (μ ν : ProbabilityMeasure (InfiniteWorld GridNode))
    (hμ : FixedRegionCylinderDLR
      (gridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld GridNode)))
    (hν : FixedRegionCylinderDLR
      (gridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld GridNode)))
    (q : ConstraintQuery GridNode) :
    (infiniteMLNMassSemantics (gridZeroFieldClassicalSpec w) μ hμ).queryProb q =
    (infiniteMLNMassSemantics (gridZeroFieldClassicalSpec w) ν hν).queryProb q :=
  infiniteMLN_queryStrength_unique_of_uniform
    (gridZeroFieldClassicalSpec w)
    (gridZeroField_uniformSmallTotalInfluence hbudget)
    μ ν hμ hν q

/-- High-temperature zero-field grid collapse at the DLR credal-envelope level:
under the Dobrushin budget, the lower and upper PLN/Walley readouts for every
finite query coincide. -/
theorem gridZeroField_queryEnvelope_precise_of_dobrushin
    {w : ℝ}
    (hbudget : 2 * |w| < 1)
    (q : ConstraintQuery GridNode) :
    infiniteMLNLowerQueryEnvelope (gridZeroFieldClassicalSpec w) q =
      infiniteMLNUpperQueryEnvelope (gridZeroFieldClassicalSpec w) q := by
  letI : Nonempty (DLRCompletion (gridZeroFieldClassicalSpec w)) :=
    gridZeroField_dlrCompletion_nonempty w
  exact infiniteMLN_queryEnvelope_precise_of_uniform
    (gridZeroFieldClassicalSpec w)
    (gridZeroField_uniformSmallTotalInfluence hbudget)
    q

/-- High-temperature zero-field collapse for the concrete origin-spin query
that will be used on the low-temperature strict-width side. -/
theorem gridZeroField_originSpinUp_queryEnvelope_precise_of_dobrushin
    {w : ℝ}
    (hbudget : 2 * |w| < 1) :
    infiniteMLNLowerQueryEnvelope
        (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery =
      infiniteMLNUpperQueryEnvelope
        (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery := by
  exact gridZeroField_queryEnvelope_precise_of_dobrushin hbudget gridOriginSpinUpQuery

/-- If the plus/minus boundary completions separate the origin-spin query, then
the zero-field grid has strict DLR width for that PLN query.  The remaining
low-temperature crown is precisely the separation hypothesis. -/
theorem gridZeroField_originSpinUp_strictWidth_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldPlusBoundaryCompletion w)) :
    dlrQueryHasStrictWidth (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery := by
  exact ⟨gridZeroFieldMinusBoundaryCompletion w,
    gridZeroFieldPlusBoundaryCompletion w, hsep⟩

/-- The same plus/minus separation gives strict width for the one-site local
cylinder presentation of the origin-spin observable. -/
theorem gridZeroField_originSpinUp_localQueryStrictWidth_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldPlusBoundaryCompletion w)) :
    dlrLocalQueryHasStrictWidth (gridZeroFieldClassicalSpec w)
      ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery := by
  refine ⟨gridZeroFieldMinusBoundaryCompletion w,
    gridZeroFieldPlusBoundaryCompletion w, ?_⟩
  simpa [gridZeroField_originSpinUp_localQueryProb_eq_queryProb] using hsep

/-- Plus/minus origin-spin separation forces a nontrivial scalar PLN/Walley
query envelope. -/
theorem gridZeroField_originSpinUp_queryEnvelope_nontrivial_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldPlusBoundaryCompletion w)) :
    infiniteMLNLowerQueryEnvelope (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery <
      infiniteMLNUpperQueryEnvelope (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery := by
  exact infiniteMLN_queryEnvelope_nontrivial_of_strictWidth_bounded
    (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
    (gridZeroField_originSpinUp_strictWidth_of_plusMinusBoundarySeparation hsep)

/-- Plus/minus origin-spin separation forces positive scalar PLN/Walley query
width. -/
theorem gridZeroField_originSpinUp_queryEnvelopeWidth_pos_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldPlusBoundaryCompletion w)) :
    0 < infiniteMLNQueryEnvelopeWidth
      (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery := by
  exact infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth
    (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
    (gridZeroField_originSpinUp_strictWidth_of_plusMinusBoundarySeparation hsep)

/-- Plus/minus origin-spin separation refutes completion-independent
determination of the scalar PLN query. -/
theorem gridZeroField_originSpinUp_not_queryDetermined_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldPlusBoundaryCompletion w)) :
    ¬ dlrQueryDetermined (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery := by
  exact not_dlrQueryDetermined_of_strictWidth
    (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
    (gridZeroField_originSpinUp_strictWidth_of_plusMinusBoundarySeparation hsep)

/-- Plus/minus origin-spin separation gives positive width in the concrete
binary query-outcome credal set read by PLN. -/
theorem gridZeroField_originSpinUp_queryOutcomeCredalSet_width_pos_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldPlusBoundaryCompletion w)) :
    0 < Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.credalEnvelopeWidth
      (dlrQueryOutcomeCredalSet (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery)
      (Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal.PrecisePrevision.FiniteWeights.atomGamble true) := by
  exact dlrQueryOutcomeCredalSet_true_atom_width_pos_of_queryStrictWidth
    (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
    (gridZeroField_originSpinUp_strictWidth_of_plusMinusBoundarySeparation hsep)

/-- Plus/minus origin-spin separation drops the scalar PLN confidence coordinate
below one. -/
theorem gridZeroField_originSpinUp_queryEnvelopeWidthComplement_lt_one_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldPlusBoundaryCompletion w)) :
    infiniteMLNQueryEnvelopeWidthComplement
      (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery < 1 := by
  have hpos :=
    gridZeroField_originSpinUp_queryEnvelopeWidth_pos_of_plusMinusBoundarySeparation hsep
  unfold infiniteMLNQueryEnvelopeWidthComplement
  linarith

/-- Plus/minus origin-spin separation forces positive width for the local
one-site cylinder envelope. -/
theorem gridZeroField_originSpinUp_localQueryEnvelopeWidth_pos_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldPlusBoundaryCompletion w)) :
    0 < dlrLocalQueryEnvelopeWidth (gridZeroFieldClassicalSpec w)
      ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery := by
  exact dlrLocalQueryEnvelopeWidth_pos_of_localQueryStrictWidth
    (gridZeroFieldClassicalSpec w) ({gridOrigin} : Region GridNode)
    gridOriginSpinUpLocalQuery
    (gridZeroField_originSpinUp_localQueryStrictWidth_of_plusMinusBoundarySeparation hsep)

/-- Plus/minus origin-spin separation drops the local one-site cylinder
confidence coordinate below one. -/
theorem gridZeroField_originSpinUp_localQueryEnvelopeWidthComplement_lt_one_of_plusMinusBoundarySeparation
    {w : ℝ}
    (hsep :
      dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldMinusBoundaryCompletion w) <
        dlrCompletionQueryProb (gridZeroFieldClassicalSpec w) gridOriginSpinUpQuery
          (gridZeroFieldPlusBoundaryCompletion w)) :
    dlrLocalQueryEnvelopeWidthComplement (gridZeroFieldClassicalSpec w)
      ({gridOrigin} : Region GridNode) gridOriginSpinUpLocalQuery < 1 := by
  exact dlrLocalQueryEnvelopeWidthComplement_lt_one_of_localQueryStrictWidth
    (gridZeroFieldClassicalSpec w) ({gridOrigin} : Region GridNode)
    gridOriginSpinUpLocalQuery
    (gridZeroField_originSpinUp_localQueryStrictWidth_of_plusMinusBoundarySeparation hsep)

/-- Quantitative local boundary-insensitivity for finite 2D-grid queries. -/
theorem grid_localQueryDiscrepancy_le_geometric
    {w : ℝ}
    (hbudget : 2 * |w| < 1)
    (μ ν : ProbabilityMeasure (InfiniteWorld GridNode))
    (hμ : FixedRegionCylinderDLR
      (gridClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld GridNode)))
    (hν : FixedRegionCylinderDLR
      (gridClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld GridNode)))
    (Δ : Region GridNode)
    (q : LocalConstraintQuery GridNode Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ n : ℕ,
        (gridClassicalSpec w).finiteRegionLocalQueryDiscrepancy μ ν Δ q
          ≤ 2 * (Δ.card : ℝ) * C ^ n := by
  exact finiteRegionLocalQueryDiscrepancy_le_geometric_of_uniformSmallTotalInfluence
    (M := gridClassicalSpec w)
    (gridClassicalSpec_uniformSmallTotalInfluence hbudget)
    μ ν hμ hν Δ q

/-- Quantitative local boundary-insensitivity for zero-field finite 2D-grid
queries in the high-temperature regime. -/
theorem gridZeroField_localQueryDiscrepancy_le_geometric
    {w : ℝ}
    (hbudget : 2 * |w| < 1)
    (μ ν : ProbabilityMeasure (InfiniteWorld GridNode))
    (hμ : FixedRegionCylinderDLR
      (gridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (μ : Measure (InfiniteWorld GridNode)))
    (hν : FixedRegionCylinderDLR
      (gridZeroFieldClassicalSpec w).toStrictlyPositiveInfiniteGroundMLNSpec
      (ν : Measure (InfiniteWorld GridNode)))
    (Δ : Region GridNode)
    (q : LocalConstraintQuery GridNode Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ C < 1 ∧
      ∀ n : ℕ,
        (gridZeroFieldClassicalSpec w).finiteRegionLocalQueryDiscrepancy μ ν Δ q
          ≤ 2 * (Δ.card : ℝ) * C ^ n := by
  exact finiteRegionLocalQueryDiscrepancy_le_geometric_of_uniformSmallTotalInfluence
    (M := gridZeroFieldClassicalSpec w)
    (gridZeroField_uniformSmallTotalInfluence hbudget)
    μ ν hμ hν Δ q

end Mettapedia.Logic.MarkovLogicInfiniteGridExample
