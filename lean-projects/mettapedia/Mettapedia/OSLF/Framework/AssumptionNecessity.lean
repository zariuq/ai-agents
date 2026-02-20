import Mettapedia.OSLF.Framework.PiRhoCanonicalBridge

/-!
# Assumption-Necessity Counterexamples

Counterexamples and non-finiteness witnesses used to justify why selected
global assumptions in endpoint wrappers remain explicit.
-/

namespace Mettapedia.OSLF.Framework.AssumptionNecessity

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.PiRhoCanonicalBridge
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

abbrev AtomSem := Mettapedia.OSLF.Formula.AtomSem
abbrev OSLFFormula := Mettapedia.OSLF.Formula.OSLFFormula

/-- A fixed base pattern for explicit star-image witnesses. -/
def basePat : Pattern := .bvar 0

/-- Syntactic zero process marker used by SC nil-laws. -/
def zeroPat : Pattern := .apply "PZero" []

/-- Recursively add right-`PZero` wrappers via bag syntax. -/
def addRightZeroNest : Nat → Pattern
  | 0 => basePat
  | n + 1 => .collection .hashBag [addRightZeroNest n, zeroPat] none

/-- Depth counter for `addRightZeroNest`. -/
def rightZeroDepth : Pattern → Nat
  | .bvar 0 => 0
  | .collection .hashBag [p, .apply "PZero" []] none => rightZeroDepth p + 1
  | _ => 0

theorem rightZeroDepth_addRightZeroNest (n : Nat) :
    rightZeroDepth (addRightZeroNest n) = n := by
  induction n with
  | zero =>
      simp [addRightZeroNest, rightZeroDepth, basePat]
  | succ n ih =>
      simp [addRightZeroNest, rightZeroDepth, zeroPat, ih]

theorem addRightZeroNest_injective : Function.Injective addRightZeroNest := by
  intro n m h
  have hd : rightZeroDepth (addRightZeroNest n) = rightZeroDepth (addRightZeroNest m) :=
    congrArg rightZeroDepth h
  simpa [rightZeroDepth_addRightZeroNest] using hd

/-- Source with a direct DROP reduction to `basePat`. -/
def dropSource : Pattern := .apply "PDrop" [.apply "NQuote" [basePat]]

theorem base_sc_addRightZeroNest : ∀ n, StructuralCongruence basePat (addRightZeroNest n)
  | 0 => StructuralCongruence.refl basePat
  | n + 1 =>
      StructuralCongruence.trans basePat (addRightZeroNest n) (addRightZeroNest (n + 1))
        (base_sc_addRightZeroNest n)
        (by
          simpa [addRightZeroNest] using
            (StructuralCongruence.symm _ _
              (StructuralCongruence.par_nil_right (addRightZeroNest n))))

def dropSource_reduces_to_addRightZeroNest (n : Nat) :
    Reduces dropSource (addRightZeroNest n) :=
  Reduces.equiv
    (p' := dropSource) (q' := basePat)
    (StructuralCongruence.refl dropSource)
    (by simpa [dropSource, basePat] using (Reduces.drop (p := basePat)))
    (by simpa using base_sc_addRightZeroNest n)

theorem dropSource_coreStar_to_addRightZeroNest (n : Nat) :
    rhoCoreStarRel dropSource (addRightZeroNest n) := by
  exact ⟨ReducesStar.single (dropSource_reduces_to_addRightZeroNest n)⟩

theorem dropSource_derivedStar_to_addRightZeroNest (n : Nat) :
    rhoDerivedStarRel dropSource (addRightZeroNest n) := by
  exact ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu.ReducesStar.toDerived
    (ReducesStar.single (dropSource_reduces_to_addRightZeroNest n))⟩

theorem infinite_image_rhoCoreStarRel_dropSource :
    Set.Infinite {q : Pattern | rhoCoreStarRel dropSource q} := by
  let f : Nat → Pattern := addRightZeroNest
  have hInfRange : Set.Infinite (Set.range f) :=
    Set.infinite_range_of_injective addRightZeroNest_injective
  have hSubset : Set.range f ⊆ {q : Pattern | rhoCoreStarRel dropSource q} := by
    intro q hq
    rcases hq with ⟨n, rfl⟩
    exact dropSource_coreStar_to_addRightZeroNest n
  exact hInfRange.mono hSubset

theorem infinite_image_rhoDerivedStarRel_dropSource :
    Set.Infinite {q : Pattern | rhoDerivedStarRel dropSource q} := by
  let f : Nat → Pattern := addRightZeroNest
  have hInfRange : Set.Infinite (Set.range f) :=
    Set.infinite_range_of_injective addRightZeroNest_injective
  have hSubset : Set.range f ⊆ {q : Pattern | rhoDerivedStarRel dropSource q} := by
    intro q hq
    rcases hq with ⟨n, rfl⟩
    exact dropSource_derivedStar_to_addRightZeroNest n
  exact hInfRange.mono hSubset

/-- Concrete witness: the core-star endpoint relation is not globally image-finite. -/
theorem rhoCoreStarRel_not_imageFinite :
    ∃ p : Pattern, ¬ Set.Finite {q : Pattern | rhoCoreStarRel p q} := by
  refine ⟨dropSource, ?_⟩
  exact infinite_image_rhoCoreStarRel_dropSource.not_finite

/-- Concrete witness: the derived-star endpoint relation is not globally image-finite. -/
theorem rhoDerivedStarRel_not_imageFinite :
    ∃ p : Pattern, ¬ Set.Finite {q : Pattern | rhoDerivedStarRel p q} := by
  refine ⟨dropSource, ?_⟩
  exact infinite_image_rhoDerivedStarRel_dropSource.not_finite

/-- Therefore global `hImageFinite` assumptions for star-level HM wrappers are
not automatically dischargeable for all states. -/
theorem not_global_hImageFinite_rhoCoreStarRel :
    ¬ (∀ p : Pattern, Set.Finite {q : Pattern | rhoCoreStarRel p q}) := by
  intro h
  rcases rhoCoreStarRel_not_imageFinite with ⟨p, hp⟩
  exact hp (h p)

/-- Therefore global `hImageFinite` assumptions for derived-star HM wrappers are
not automatically dischargeable for all states. -/
theorem not_global_hImageFinite_rhoDerivedStarRel :
    ¬ (∀ p : Pattern, Set.Finite {q : Pattern | rhoDerivedStarRel p q}) := by
  intro h
  rcases rhoDerivedStarRel_not_imageFinite with ⟨p, hp⟩
  exact hp (h p)

def relAll : Pattern → Pattern → Prop := fun _ _ => True
def relNone : Pattern → Pattern → Prop := fun _ _ => False

def atomAll : AtomSem := fun _ _ => True
def atomNone : AtomSem := fun _ _ => False

def witnessPat : Pattern := .bvar 0

/-- Counterexample pattern: dropping `hAtomAll` from global dia/box transfer
is unsound even when `◇⊤` holds everywhere. -/
theorem counterexample_hAtomAll_for_global_diaBox_transfer :
    ∃ (R : Pattern → Pattern → Prop) (I : AtomSem) (φ : OSLFFormula),
      EndpointDiaBoxFragment φ ∧
      (∀ p, Mettapedia.OSLF.Formula.sem R I (.dia .top) p) ∧
      ¬ (∀ p, Mettapedia.OSLF.Formula.sem R I φ p) := by
  refine ⟨relAll, atomNone, .atom "a", EndpointDiaBoxFragment.atom "a", ?_, ?_⟩
  · intro p
    exact ⟨p, trivial, trivial⟩
  · intro hall
    have hAt : Mettapedia.OSLF.Formula.sem relAll atomNone (.atom "a") witnessPat :=
      hall witnessPat
    simpa [atomNone] using hAt

/-- Counterexample pattern: dropping global `◇⊤` (`hDiaTopAll`) from the same
global transfer shape is unsound even when atoms are universally true. -/
theorem counterexample_hDiaTopAll_for_global_diaBox_transfer :
    ∃ (R : Pattern → Pattern → Prop) (I : AtomSem) (φ : OSLFFormula),
      EndpointDiaBoxFragment φ ∧
      (∀ a p, I a p) ∧
      ¬ (∀ p, Mettapedia.OSLF.Formula.sem R I φ p) := by
  refine ⟨relNone, atomAll, .dia .top,
    EndpointDiaBoxFragment.dia EndpointDiaBoxFragment.top, ?_, ?_⟩
  · intro _a _p
    trivial
  · intro hall
    have hDia : Mettapedia.OSLF.Formula.sem relNone atomAll (.dia .top) witnessPat :=
      hall witnessPat
    rcases hDia with ⟨_q, hstep, _hTop⟩
    exact hstep

def commLiftSeed : Pattern := .apply "NQuote" [basePat]

def commLiftBody : Pattern := .apply "PDrop" [.bvar 0]

def commLiftPred : Pattern → Prop := fun u => u = commLiftBody

theorem commLift_body_subst_eq_pathSem_h :
    Mettapedia.OSLF.MeTTaIL.Substitution.commSubst commLiftBody basePat =
      pathSem rhoCalc pdropArrow.toPath commLiftSeed := by
  native_decide

theorem commLift_body_subst_ne_pathSem_gcomp_h :
    Mettapedia.OSLF.MeTTaIL.Substitution.commSubst commLiftBody basePat ≠
      pathSem rhoCalc (nquoteArrow.toPath.comp pdropArrow.toPath) commLiftSeed := by
  native_decide

/-- Concrete necessity witness: `commDiWitnessLifting` is not derivable in full
generality from syntax alone (without an explicit lifting/package assumption). -/
theorem not_commDiWitnessLifting_rho_example :
    ¬ commDiWitnessLifting rhoCalc rhoProc commLiftSeed basePat commLiftPred := by
  intro hLift
  have hEx :=
    hLift
      (g := nquoteArrow.toPath)
      (h := pdropArrow.toPath)
      (u := commLiftBody)
      commLift_body_subst_eq_pathSem_h
      rfl
  rcases hEx with ⟨u', hu'Eq, hu'Pred⟩
  have hu' : u' = commLiftBody := hu'Pred
  subst hu'
  exact commLift_body_subst_ne_pathSem_gcomp_h hu'Eq

/-- Therefore the generic COMM/pathSem-lifting assumptions in BC transfer
lemmas cannot be dropped in full generality. -/
theorem commDiWitnessLifting_not_derivable_globally :
    ∃ (lang : LanguageDef) (s : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort lang)
      (seed q : Pattern) (φ : Pattern → Prop),
      ¬ commDiWitnessLifting lang s seed q φ := by
  exact ⟨rhoCalc, rhoProc, commLiftSeed, basePat, commLiftPred,
    not_commDiWitnessLifting_rho_example⟩

end Mettapedia.OSLF.Framework.AssumptionNecessity
