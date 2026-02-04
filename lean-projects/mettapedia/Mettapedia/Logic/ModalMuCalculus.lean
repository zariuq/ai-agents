import Mathlib.Algebra.Order.Quantale
import Mathlib.Order.FixedPoints

/-!
# Modal μ-Calculus

This file formalizes the Modal μ-Calculus, a powerful extension of modal logic
with fixed-point operators for reasoning about infinite behavior.

## Mathematical Foundation

Modal μ-calculus extends Hennessy-Milner Logic (HML) with:
- **Least fixed point**: μ X . φ (finite/inductive properties)
- **Greatest fixed point**: ν X . φ (infinite/coinductive properties)

This is the foundation for model checking and program verification.

## Connection to PLN

The modal μ-calculus provides a semantic foundation for Temporal PLN:
- Diamond/Box modalities correspond to PLN's Lead/Lag operators
- Fixed points capture temporal patterns (always, eventually, etc.)
- The embedding theorem (PLNModalBridge.lean) makes this precise

## References

[1] Todorov & Poulsen (2024). "Modal μ-Calculus for Free in Agda". TyDe '24
[2] Kozen (1983). "Results on the Propositional μ-Calculus"
[3] Bradfield & Stirling. "Modal μ-Calculi" (Handbook of Modal Logic)
-/

universe u v

namespace Mettapedia.Logic.ModalMuCalculus

/-! ## Formula Syntax

We use de Bruijn indices for fixed-point variable binding.
The index `n` tracks the number of bound variables in scope.
-/

/--
Modal μ-calculus formula syntax with de Bruijn indices.

The type parameter `Act : Type*` represents the set of actions/modalities.
The natural number index `n` tracks bound variable scope depth.
-/
inductive Formula (Act : Type*) : ℕ → Type _ where
  /-- Truth (⊤) -/
  | tt : Formula Act n
  /-- Falsehood (⊥) -/
  | ff : Formula Act n
  /-- Negation (¬φ) -/
  | neg : Formula Act n → Formula Act n
  /-- Conjunction (φ ∧ ψ) -/
  | conj : Formula Act n → Formula Act n → Formula Act n
  /-- Disjunction (φ ∨ ψ) -/
  | disj : Formula Act n → Formula Act n → Formula Act n
  /-- Diamond modality (⟨α⟩φ): "there exists an α-transition to a state satisfying φ" -/
  | diamond : Act → Formula Act n → Formula Act n
  /-- Box modality ([α]φ): "all α-transitions lead to states satisfying φ" -/
  | box : Act → Formula Act n → Formula Act n
  /-- Least fixed point (μ X . φ): binds a new variable -/
  | mu : Formula Act (n + 1) → Formula Act n
  /-- Greatest fixed point (ν X . φ): binds a new variable -/
  | nu : Formula Act (n + 1) → Formula Act n
  /-- Bound variable reference (de Bruijn index) -/
  | var : Fin n → Formula Act n
deriving Repr, DecidableEq

namespace Formula

variable {Act : Type*}

/-! ## Formula Constructors and Notation -/

/-- Implication (φ ⇒ ψ) defined as (¬φ ∨ ψ) -/
def impl (φ ψ : Formula Act n) : Formula Act n :=
  disj (neg φ) ψ

/-- Biconditional (φ ⇔ ψ) -/
def iff' (φ ψ : Formula Act n) : Formula Act n :=
  conj (impl φ ψ) (impl ψ φ)

/-! ## Weakening and Substitution

These operations are needed for fixed-point semantics.
-/

/-- Weaken a formula by adding a variable to the context -/
def weaken : Formula Act n → Formula Act (n + 1)
  | tt => tt
  | ff => ff
  | neg φ => neg (weaken φ)
  | conj φ ψ => conj (weaken φ) (weaken ψ)
  | disj φ ψ => disj (weaken φ) (weaken ψ)
  | diamond a φ => diamond a (weaken φ)
  | box a φ => box a (weaken φ)
  | mu φ => mu (weaken φ)  -- Note: this shifts indices correctly
  | nu φ => nu (weaken φ)
  | var i => var i.castSucc

/-- Substitute a formula for the outermost bound variable (index 0)
    `subst body replacement` replaces all occurrences of variable 0 in `body`
    with `replacement`, and decrements all other variable indices. -/
def subst (body : Formula Act (n + 1)) (replacement : Formula Act n) : Formula Act n :=
  match body with
  | tt => tt
  | ff => ff
  | neg φ => neg (subst φ replacement)
  | conj φ ψ => conj (subst φ replacement) (subst ψ replacement)
  | disj φ ψ => disj (subst φ replacement) (subst ψ replacement)
  | diamond a φ => diamond a (subst φ replacement)
  | box a φ => box a (subst φ replacement)
  | mu φ => mu (subst φ (weaken replacement))
  | nu φ => nu (subst φ (weaken replacement))
  | var i =>
      match i with
      | ⟨0, _⟩ => replacement
      | ⟨i' + 1, hi⟩ => var ⟨i', Nat.lt_of_succ_lt_succ hi⟩

/-! ### Substitution Properties

The substitution operation is structurally correct. Key properties can be proven
when needed for specific applications.
-/

/-- Substituting into variable 0 gives the replacement -/
theorem subst_var_zero (replacement : Formula Act n) :
    subst (var (0 : Fin (n + 1))) replacement = replacement := by
  unfold subst
  rfl

/-- Substituting into a successor variable decrements the index -/
theorem subst_var_succ (i : ℕ) (hi : i + 1 < n + 1) (replacement : Formula Act n) :
    subst (var ⟨i + 1, hi⟩) replacement = var ⟨i, Nat.lt_of_succ_lt_succ hi⟩ := by
  unfold subst
  rfl

/-! ### Positivity

A formula is positive in a variable if that variable only appears in positive
positions (not under an odd number of negations). This is crucial for the
Knaster-Tarski fixed-point theorem, which requires monotone functions.
-/

/-- Check if variable `i` appears only positively (in positive positions) in formula `φ`.
    The `polarity` parameter tracks whether we're under an odd number of negations. -/
def isPositiveIn (i : Fin n) (polarity : Bool := true) : Formula Act n → Bool
  | tt => true
  | ff => true
  | neg φ => isPositiveIn i (!polarity) φ
  | conj φ ψ => isPositiveIn i polarity φ && isPositiveIn i polarity ψ
  | disj φ ψ => isPositiveIn i polarity φ && isPositiveIn i polarity ψ
  | diamond _ φ => isPositiveIn i polarity φ
  | box _ φ => isPositiveIn i polarity φ
  | mu φ => isPositiveIn i.succ polarity φ
  | nu φ => isPositiveIn i.succ polarity φ
  | var j => j ≠ i || polarity

/-- A formula with one free variable is positive if variable 0 appears only positively -/
def isPositive (φ : Formula Act (n + 1)) : Bool :=
  isPositiveIn 0 true φ

/-! ## Hennessy-Milner Logic (HML) Fragment

The fixed-point-free fragment is called HML.
-/

/-- Check if a formula is in the HML fragment (no fixed points) -/
def isHML : Formula Act n → Bool
  | tt => true
  | ff => true
  | neg φ => isHML φ
  | conj φ ψ => isHML φ && isHML ψ
  | disj φ ψ => isHML φ && isHML ψ
  | diamond _ φ => isHML φ
  | box _ φ => isHML φ
  | mu _ => false
  | nu _ => false
  | var _ => true  -- Variables are HML (they appear in fixed-point bodies)

/-! ## Common Temporal Patterns

These are standard patterns expressible in modal μ-calculus.
-/

/-- Eventually φ (◇φ): there exists a path leading to φ
    EF φ = μ X . (φ ∨ ⟨·⟩X) -/
def eventually (a : Act) (φ : Formula Act 0) : Formula Act 0 :=
  mu (disj (weaken φ) (diamond a (var 0)))

/-- Always φ (□φ): on all paths, φ always holds
    AG φ = ν X . (φ ∧ [·]X) -/
def always (a : Act) (φ : Formula Act 0) : Formula Act 0 :=
  nu (conj (weaken φ) (box a (var 0)))

/-- Always eventually φ (□◇φ): φ holds infinitely often
    GF φ = ν Y . (μ X . (φ ∨ ⟨·⟩X)) ∧ [·]Y
    Note: nested fixed points require careful weakening -/
def alwaysEventually (a : Act) (φ : Formula Act 0) : Formula Act 0 :=
  -- Inner eventually: μ X . (φ ∨ ⟨a⟩X) at level 1
  let innerEv : Formula Act 1 := mu (disj (weaken (weaken φ)) (diamond a (var 0)))
  -- Outer always: ν Y . innerEv ∧ [a]Y
  nu (conj innerEv (box a (var 0)))

/-- Eventually always φ (◇□φ): φ eventually holds forever
    FG φ = μ Y . (ν X . (φ ∧ [·]X)) ∨ ⟨·⟩Y -/
def eventuallyAlways (a : Act) (φ : Formula Act 0) : Formula Act 0 :=
  -- Inner always: ν X . (φ ∧ [a]X) at level 1
  let innerAlw : Formula Act 1 := nu (conj (weaken (weaken φ)) (box a (var 0)))
  -- Outer eventually: μ Y . innerAlw ∨ ⟨a⟩Y
  mu (disj innerAlw (diamond a (var 0)))

/-! ## Formula Size and Complexity -/

/-- Size of a formula (number of constructors) -/
def size : Formula Act n → ℕ
  | tt => 1
  | ff => 1
  | neg φ => 1 + size φ
  | conj φ ψ => 1 + size φ + size ψ
  | disj φ ψ => 1 + size φ + size ψ
  | diamond _ φ => 1 + size φ
  | box _ φ => 1 + size φ
  | mu φ => 1 + size φ
  | nu φ => 1 + size φ
  | var _ => 1

/-- Alternation depth: maximum nesting of μ/ν with opposite polarity
    Simplified version that counts total fixed-point nesting -/
def altDepth : Formula Act n → ℕ
  | tt => 0
  | ff => 0
  | neg φ => altDepth φ
  | conj φ ψ => max (altDepth φ) (altDepth ψ)
  | disj φ ψ => max (altDepth φ) (altDepth ψ)
  | diamond _ φ => altDepth φ
  | box _ φ => altDepth φ
  | mu φ => 1 + altDepth φ
  | nu φ => 1 + altDepth φ
  | var _ => 0

end Formula

/-! ## Labeled Transition Systems

Standard model for modal μ-calculus semantics.
-/

/-- A labeled transition system (LTS) with states S and actions Act -/
structure LTS (S : Type*) (Act : Type*) where
  /-- Transition relation: (s, a, s') means state s transitions to s' via action a -/
  trans : S → Act → S → Prop
  /-- Set of final/accepting states (for some applications) -/
  final : Set S := Set.univ

namespace LTS

variable {S : Type*} {Act : Type*}

/-- The set of states reachable from s via action a -/
def successors (lts : LTS S Act) (s : S) (a : Act) : Set S :=
  { s' | lts.trans s a s' }

/-- The set of states from which s is reachable via action a -/
def predecessors (lts : LTS S Act) (s : S) (a : Act) : Set S :=
  { s' | lts.trans s' a s }

/-- Check if there exists an a-transition from s -/
def hasTransition (lts : LTS S Act) (s : S) (a : Act) : Prop :=
  ∃ s', lts.trans s a s'

/-- Deterministic LTS: at most one transition per (state, action) pair -/
def isDeterministic (lts : LTS S Act) : Prop :=
  ∀ s a s₁ s₂, lts.trans s a s₁ → lts.trans s a s₂ → s₁ = s₂

/-- Total LTS: at least one transition per (state, action) pair -/
def isTotal (lts : LTS S Act) : Prop :=
  ∀ s a, ∃ s', lts.trans s a s'

end LTS

/-! ## Boolean Satisfaction Semantics

Standard Boolean satisfaction for modal μ-calculus over an LTS.
This serves as the ground truth before lifting to quantale values.
-/

section BooleanSemantics

variable {S : Type*} {Act : Type*}

/-- Environment mapping bound variables to predicates on states -/
def Env (S : Type*) (n : ℕ) := Fin n → Set S

/-- Empty environment -/
def Env.empty : Env S 0 := Fin.elim0

/-- Extend environment with a new predicate -/
def Env.extend (ρ : Env S n) (P : Set S) : Env S (n + 1) :=
  fun i => if h : i.val = 0 then P else ρ ⟨i.val - 1, by omega⟩

/--
Boolean satisfaction relation for modal μ-calculus formulas.

`satisfies lts ρ φ s` means state `s` satisfies formula `φ` in LTS `lts`
with variable environment `ρ`.
-/
def satisfies (lts : LTS S Act) : Env S n → Formula Act n → S → Prop
  | _, Formula.tt, _ => True
  | _, Formula.ff, _ => False
  | ρ, Formula.neg φ, s => ¬ satisfies lts ρ φ s
  | ρ, Formula.conj φ ψ, s => satisfies lts ρ φ s ∧ satisfies lts ρ ψ s
  | ρ, Formula.disj φ ψ, s => satisfies lts ρ φ s ∨ satisfies lts ρ ψ s
  | ρ, Formula.diamond a φ, s => ∃ s' ∈ lts.successors s a, satisfies lts ρ φ s'
  | ρ, Formula.box a φ, s => ∀ s' ∈ lts.successors s a, satisfies lts ρ φ s'
  | ρ, Formula.mu φ, s =>
      -- Least fixed point: s is in the smallest set X such that
      -- ∀ t, t ∈ { u | satisfies lts (ρ.extend X) φ u } → t ∈ X
      ∀ X : Set S, (∀ t, satisfies lts (ρ.extend X) φ t → t ∈ X) → s ∈ X
  | ρ, Formula.nu φ, s =>
      -- Greatest fixed point: s is in some set X such that
      -- ∀ t ∈ X, satisfies lts (ρ.extend X) φ t
      ∃ X : Set S, s ∈ X ∧ ∀ t ∈ X, satisfies lts (ρ.extend X) φ t
  | ρ, Formula.var i, s => s ∈ ρ i

/-- The set of states satisfying a formula -/
def sat (lts : LTS S Act) (ρ : Env S n) (φ : Formula Act n) : Set S :=
  { s | satisfies lts ρ φ s }

/-! ## Properties of Satisfaction -/

/-- Diamond and box are duals -/
theorem diamond_box_dual (lts : LTS S Act) (ρ : Env S n) (a : Act) (φ : Formula Act n) (s : S) :
    satisfies lts ρ (Formula.diamond a φ) s ↔
    ¬ satisfies lts ρ (Formula.box a (Formula.neg φ)) s := by
  simp only [satisfies, LTS.successors, Set.mem_setOf_eq]
  constructor
  · intro ⟨s', htrans, hsat⟩ hall
    exact absurd hsat (hall s' htrans)
  · intro h
    push_neg at h
    exact h

/-- Box can be expressed via diamond -/
theorem box_as_neg_diamond_neg (lts : LTS S Act) (ρ : Env S n) (a : Act) (φ : Formula Act n) (s : S) :
    satisfies lts ρ (Formula.box a φ) s ↔
    ¬ satisfies lts ρ (Formula.diamond a (Formula.neg φ)) s := by
  simp only [satisfies, LTS.successors, Set.mem_setOf_eq]
  constructor
  · intro hall ⟨s', htrans, hnsat⟩
    exact hnsat (hall s' htrans)
  · intro h s' htrans
    by_contra hc
    exact h ⟨s', htrans, hc⟩

end BooleanSemantics

end Mettapedia.Logic.ModalMuCalculus
