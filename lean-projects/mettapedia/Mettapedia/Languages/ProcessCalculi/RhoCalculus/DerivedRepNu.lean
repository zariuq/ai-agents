import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MultiStep

/-!
# Derived Operational Layer for Replication/Restriction Wrappers

This module keeps canonical one-step semantics in
`RhoCalculus/Reduction.lean` and adds a separate derived layer with explicit
administrative operational rules used by higher-level encodings.

Core policy:
- `Reduction.Reduces` remains canonical.
- `ReducesDerived` extends it (currently with `rep_unfold`).
- Bridge lemmas provide adequacy (`core -> derived`) and transport back to
  core for core-compatible derived traces.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-- Derived one-step operational relation.

`core` embeds canonical reduction steps.
`rep_unfold` adds the administrative replication unfolding step.
-/
inductive ReducesDerived : Pattern → Pattern → Type where
  | core {p q : Pattern} : p ⇝ q → ReducesDerived p q
  | rep_unfold {p : Pattern} :
      ReducesDerived (.apply "PReplicate" [p])
                     (.collection .hashBag [p, .apply "PReplicate" [p]] none)
  | par {p q : Pattern} {rest : List Pattern} :
      ReducesDerived p q →
      ReducesDerived (.collection .hashBag (p :: rest) none)
                     (.collection .hashBag (q :: rest) none)
  | par_any {p q : Pattern} {before after : List Pattern} :
      ReducesDerived p q →
      ReducesDerived (.collection .hashBag (before ++ [p] ++ after) none)
                     (.collection .hashBag (before ++ [q] ++ after) none)
  | par_set {p q : Pattern} {rest : List Pattern} :
      ReducesDerived p q →
      ReducesDerived (.collection .hashSet (p :: rest) none)
                     (.collection .hashSet (q :: rest) none)
  | par_set_any {p q : Pattern} {before after : List Pattern} :
      ReducesDerived p q →
      ReducesDerived (.collection .hashSet (before ++ [p] ++ after) none)
                     (.collection .hashSet (before ++ [q] ++ after) none)

infix:50 " ⇝ᵈ " => ReducesDerived

/-- Derived reflexive-transitive closure. -/
inductive ReducesDerivedStar : Pattern → Pattern → Type where
  | refl (p : Pattern) : ReducesDerivedStar p p
  | step {p q r : Pattern} : p ⇝ᵈ q → ReducesDerivedStar q r → ReducesDerivedStar p r

notation:20 p " ⇝ᵈ* " q => ReducesDerivedStar p q

namespace ReducesDerivedStar

/-- Single derived step as a derived star trace. -/
def single {p q : Pattern} (h : p ⇝ᵈ q) : p ⇝ᵈ* q :=
  .step h (.refl q)

/-- Transitivity of derived star closure. -/
noncomputable def trans {p q r : Pattern} (h₁ : p ⇝ᵈ* q) (h₂ : q ⇝ᵈ* r) : p ⇝ᵈ* r := by
  induction h₁ with
  | refl => exact h₂
  | step h hs ih => exact .step h (ih h₂)

/-- Lift a derived-star trace through head-position parallel bag context. -/
noncomputable def par {p q : Pattern} {rest : List Pattern}
    (h : p ⇝ᵈ* q) :
    (.collection .hashBag (p :: rest) none) ⇝ᵈ*
      (.collection .hashBag (q :: rest) none) := by
  induction h with
  | refl p =>
      exact .refl (.collection .hashBag (p :: rest) none)
  | step h₁ hs ih =>
      exact .step (.par h₁) ih

/-- Lift a derived-star trace through arbitrary-position parallel bag context. -/
noncomputable def par_any {p q : Pattern} {before after : List Pattern}
    (h : p ⇝ᵈ* q) :
    (.collection .hashBag (before ++ [p] ++ after) none) ⇝ᵈ*
      (.collection .hashBag (before ++ [q] ++ after) none) := by
  induction h with
  | refl p =>
      exact .refl (.collection .hashBag (before ++ [p] ++ after) none)
  | step h₁ hs ih =>
      exact .step (.par_any h₁) ih

/-- Lift a derived-star trace through head-position set context. -/
noncomputable def par_set {p q : Pattern} {rest : List Pattern}
    (h : p ⇝ᵈ* q) :
    (.collection .hashSet (p :: rest) none) ⇝ᵈ*
      (.collection .hashSet (q :: rest) none) := by
  induction h with
  | refl p =>
      exact .refl (.collection .hashSet (p :: rest) none)
  | step h₁ hs ih =>
      exact .step (.par_set h₁) ih

/-- Lift a derived-star trace through arbitrary-position set context. -/
noncomputable def par_set_any {p q : Pattern} {before after : List Pattern}
    (h : p ⇝ᵈ* q) :
    (.collection .hashSet (before ++ [p] ++ after) none) ⇝ᵈ*
      (.collection .hashSet (before ++ [q] ++ after) none) := by
  induction h with
  | refl p =>
      exact .refl (.collection .hashSet (before ++ [p] ++ after) none)
  | step h₁ hs ih =>
      exact .step (.par_set_any h₁) ih

end ReducesDerivedStar

/-! ## Administrative Trace Helpers -/

/-- One-step replication unfolding as a derived-star trace. -/
def rep_unfold_single (p : Pattern) :
    (.apply "PReplicate" [p]) ⇝ᵈ*
      (.collection .hashBag [p, .apply "PReplicate" [p]] none) :=
  ReducesDerivedStar.single ReducesDerived.rep_unfold

/-- Replication unfolding lifted into arbitrary bag context. -/
noncomputable def rep_unfold_par_any {before after : List Pattern} (p : Pattern) :
    (.collection .hashBag (before ++ [.apply "PReplicate" [p]] ++ after) none) ⇝ᵈ*
      (.collection .hashBag
        (before ++ [.collection .hashBag [p, .apply "PReplicate" [p]] none] ++ after) none) :=
  ReducesDerivedStar.par_any (h := rep_unfold_single p)

/-! ## Core/Derived Bridge -/

/-- Core one-step reduction embeds into derived one-step reduction. -/
def Reduces.toDerived {p q : Pattern} (h : p ⇝ q) : p ⇝ᵈ q :=
  .core h

/-- Core star trace embeds into derived star trace. -/
noncomputable def ReducesStar.toDerived {p q : Pattern} (h : p ⇝* q) : p ⇝ᵈ* q := by
  induction h with
  | refl p => exact .refl p
  | step h hs ih => exact .step (.core h) ih

/-- A derived trace is core-compatible when every step came from `core`. -/
inductive CoreCompatible : {p q : Pattern} → (p ⇝ᵈ* q) → Type where
  | refl (p : Pattern) : CoreCompatible (.refl p)
  | step {p q r : Pattern} (h : p ⇝ q) (hs : q ⇝ᵈ* r) :
      CoreCompatible hs →
      CoreCompatible (.step (.core h) hs)

/-- The derived trace produced from a core star trace is core-compatible. -/
noncomputable def ReducesStar.toDerivedCoreCompatible {p q : Pattern} (h : p ⇝* q) :
    CoreCompatible (ReducesStar.toDerived h) := by
  induction h with
  | refl p =>
      simpa [ReducesStar.toDerived] using (CoreCompatible.refl p)
  | step h hs ih =>
      simpa [ReducesStar.toDerived] using (CoreCompatible.step h _ ih)

/-- Transport a core-compatible derived trace back to canonical core star. -/
noncomputable def CoreCompatible.toCore {p q : Pattern} {hs : p ⇝ᵈ* q}
    (hcc : CoreCompatible hs) : p ⇝* q := by
  induction hcc with
  | refl p => exact .refl p
  | step h hs hcc ih => exact .step h ih

/-! ## One-Step Conservativity on Core-Canonical Sources -/

/-- Detect whether a pattern uses derived administrative heads (`PReplicate`/`PNu`). -/
def hasDerivedHead : Pattern → Bool
  | .bvar _ => false
  | .fvar _ => false
  | .apply "PReplicate" _ => true
  | .apply "PNu" _ => true
  | .apply _ args => (args.map hasDerivedHead).any (fun b => b)
  | .lambda body => hasDerivedHead body
  | .multiLambda _ body => hasDerivedHead body
  | .subst body repl => hasDerivedHead body || hasDerivedHead repl
  | .collection _ elems _ => (elems.map hasDerivedHead).any (fun b => b)

/-- Core-canonical terms have no derived administrative heads. -/
def CoreCanonical (p : Pattern) : Prop := hasDerivedHead p = false

/-- Witness that a core reduction proof used a non-`equiv` constructor. -/
inductive IsDirectCore : {p q : Pattern} → (p ⇝ q) → Prop where
  | comm {n q p : Pattern} {rest : List Pattern} :
      IsDirectCore (@Reduces.comm n q p rest)
  | drop {p : Pattern} :
      IsDirectCore (@Reduces.drop p)
  | par {p q : Pattern} {rest : List Pattern} (h : p ⇝ q) :
      IsDirectCore (@Reduces.par p q rest h)
  | par_any {p q : Pattern} {before after : List Pattern} (h : p ⇝ q) :
      IsDirectCore (@Reduces.par_any p q before after h)
  | par_set {p q : Pattern} {rest : List Pattern} (h : p ⇝ q) :
      IsDirectCore (@Reduces.par_set p q rest h)
  | par_set_any {p q : Pattern} {before after : List Pattern} (h : p ⇝ q) :
      IsDirectCore (@Reduces.par_set_any p q before after h)

/-- Design boundary: `PReplicate` cannot reduce via any direct core constructor.
    If it reduces at all in core semantics, that proof necessarily uses `equiv`.
-/
theorem no_direct_core_step_from_PReplicate {p q : Pattern}
    (h : (.apply "PReplicate" [p]) ⇝ q) : ¬ IsDirectCore h := by
  intro hdir
  let aux (p0 : Pattern) :
      ∀ s q0, s = (.apply "PReplicate" [p0]) → (hred : s ⇝ q0) → IsDirectCore hred → False := by
    intro s q0 hs hred hdirect
    cases hdirect with
    | comm => simp at hs
    | drop => simp at hs
    | par _ => simp at hs
    | par_any _ => simp at hs
    | par_set _ => simp at hs
    | par_set_any _ => simp at hs
  exact aux p _ _ rfl h hdir

/-- Design boundary: `PNu` also cannot reduce via any direct core constructor.
    Any core reduction proof from `PNu` must pass through `equiv`.
-/
theorem no_direct_core_step_from_PNu {p q : Pattern}
    (h : (.apply "PNu" [p]) ⇝ q) : ¬ IsDirectCore h := by
  intro hdir
  let aux (p0 : Pattern) :
      ∀ s q0, s = (.apply "PNu" [p0]) → (hred : s ⇝ q0) → IsDirectCore hred → False := by
    intro s q0 hs hred hdirect
    cases hdirect with
    | comm => simp at hs
    | drop => simp at hs
    | par _ => simp at hs
    | par_any _ => simp at hs
    | par_set _ => simp at hs
    | par_set_any _ => simp at hs
  exact aux p _ _ rfl h hdir

/-- Any core step from `PReplicate` has an explicit `equiv` shell.
    This is the strongest fully-proved boundary theorem currently available. -/
theorem core_step_from_PReplicate_has_equiv_shell {p q : Pattern}
    (h : (.apply "PReplicate" [p]) ⇝ q) :
    ∃ p' q', ∃ _ : p' ⇝ q',
      StructuralCongruence (.apply "PReplicate" [p]) p' ∧ StructuralCongruence q' q := by
  let aux (p0 : Pattern) :
      ∀ s q0, s = (.apply "PReplicate" [p0]) → (hred : s ⇝ q0) →
        ∃ p' q', ∃ _ : p' ⇝ q',
          StructuralCongruence (.apply "PReplicate" [p0]) p' ∧ StructuralCongruence q' q0 := by
    intro s q0 hs hred
    induction hred generalizing p0 with
    | comm => simp at hs
    | drop => simp at hs
    | par h ih => simp at hs
    | par_any h ih => simp at hs
    | par_set h ih => simp at hs
    | par_set_any h ih => simp at hs
    | equiv hsc hmid hsc2 ih =>
      exact ⟨_, _, hmid, ⟨hs ▸ hsc, hsc2⟩⟩
  exact aux p _ _ rfl h

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu
