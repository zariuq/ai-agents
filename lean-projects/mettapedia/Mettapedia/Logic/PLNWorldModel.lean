import Mettapedia.Logic.EvidenceClass
import Mettapedia.Logic.EvidenceQuantale

/-!
# PLN World Models (Posterior-State Interface)

This module defines a minimal interface for the **complete** (“distribution-passing”) PLN layer:

- A *world-model posterior state* `State` that can be revised by combining independent evidence
  sources (an `EvidenceType`, i.e. an additive commutative monoid).
- Query projections that extract **binary Evidence** (`n⁺, n⁻`) for arbitrary queries.

All truth-value notions (strength/weight/confidence/interval bounds) are **views** computed from
the extracted `Evidence`.  They are intentionally not part of the core interface.

This is the “WM judgment + query judgment” split:

- build/revise posterior states in `State`;
- answer queries by extracting evidence from the state.
-/

namespace Mettapedia.Logic.PLNWorldModel

open scoped ENNReal

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale

/-! ## Queries -/

/-- Standard PLN queries over a set of atoms: events/propositions and links/conditionals. -/
inductive PLNQuery (Atom : Type*) where
  /-- Evidence for an event/proposition. -/
  | prop : Atom → PLNQuery Atom
  /-- Evidence for a link/conditional. -/
  | link : Atom → Atom → PLNQuery Atom
  /-- Evidence for a conditional with multiple antecedents (conjunction). -/
  | linkCond : List Atom → Atom → PLNQuery Atom

/-! ## Interface -/

/-- A revisable posterior state supporting **additive** evidence-valued query extraction.

`State` is an `EvidenceType` (so revision is `+`), and queries extract `Evidence`.

The `evidence_add` law is the key commutation property:
extracting from revised states is the same as revising extracted evidence. -/
class WorldModel (State : Type*) (Query : Type*) [EvidenceType State] where
  /-- Extract binary evidence for a query. -/
  evidence : State → Query → Evidence
  /-- Extraction commutes with revision (`+`) in the world-model state. -/
  evidence_add : ∀ W₁ W₂ q, evidence (W₁ + W₂) q = evidence W₁ q + evidence W₂ q

namespace WorldModel

variable {State Query : Type*} [EvidenceType State] [WorldModel State Query]

/-! ## Generic views (derived, not stored) -/

/-- Posterior-mean probability view of a query (improper-prior strength). -/
noncomputable def queryStrength (W : State) (q : Query) : ℝ≥0∞ :=
  Evidence.toStrength (WorldModel.evidence (State := State) (Query := Query) W q)

/-- WTV view for a query, using the canonical `Evidence → WTV` map with prior size `κ`.
This is operational plumbing; the core state remains `Evidence`. -/
noncomputable def queryWTV (κ : ℝ≥0∞) (W : State) (q : Query) : PLNWeightTV.WTV :=
  Evidence.toWTV κ (WorldModel.evidence (State := State) (Query := Query) W q)

theorem evidence_add' (W₁ W₂ : State) (q : Query) :
    WorldModel.evidence (State := State) (Query := Query) (W₁ + W₂) q =
      WorldModel.evidence (State := State) (Query := Query) W₁ q +
        WorldModel.evidence (State := State) (Query := Query) W₂ q :=
  WorldModel.evidence_add (State := State) (Query := Query) W₁ W₂ q

end WorldModel

/-! ## WM calculus judgments (sequent-style spine) -/

/-- World-model judgment: a posterior state is derivable by revision. -/
inductive WMJudgment {State : Type*} [EvidenceType State] : State → Prop
  | axiom (W : State) : WMJudgment W
  | revise {W₁ W₂ : State} : WMJudgment W₁ → WMJudgment W₂ → WMJudgment (W₁ + W₂)

notation:50 "⊢wm " W => WMJudgment W

/-- Query judgment: extracted evidence for a query from a derivable state. -/
def WMQueryJudgment {State Query : Type*} [EvidenceType State] [WorldModel State Query]
    (W : State) (q : Query) (e : Evidence) : Prop :=
  WMJudgment W ∧ e = WorldModel.evidence (State := State) (Query := Query) W q

notation:50 "⊢q " W " ⇓ " q " ↦ " e => WMQueryJudgment W q e

namespace WMJudgment

variable {State Query : Type*} [EvidenceType State] [WorldModel State Query]

theorem query_of_axiom (W : State) (q : Query) :
    ⊢q W ⇓ q ↦ (WorldModel.evidence (State := State) (Query := Query) W q) := by
  exact ⟨WMJudgment.axiom W, rfl⟩

theorem query_revise {W₁ W₂ : State} {q : Query} {e₁ e₂ : Evidence} :
    (⊢q W₁ ⇓ q ↦ e₁) → (⊢q W₂ ⇓ q ↦ e₂) →
      (⊢q (W₁ + W₂) ⇓ q ↦ (e₁ + e₂)) := by
  intro h₁ h₂
  rcases h₁ with ⟨hW₁, rfl⟩
  rcases h₂ with ⟨hW₂, rfl⟩
  refine ⟨WMJudgment.revise hW₁ hW₂, ?_⟩
  simpa using
    (WorldModel.evidence_add' (State := State) (Query := Query) W₁ W₂ q).symm

end WMJudgment

/-! ## Context-indexed WM judgments -/

/-- Context-indexed WM judgment: a posterior state is derivable from a set of axiom states.

Unlike `WMJudgment` (where any state is derivable via `axiom`), `WMJudgmentCtx Γ W`
asserts that `W` is built only from states in `Γ` (via revision). This tightens the
trust boundary: only evidence from approved sources contributes to conclusions.

Use cases:
- **Provenance**: track which data sources contributed to a posterior
- **Trust boundaries**: restrict inferences to trusted evidence pools
- **Composition**: combine independently derived posteriors with `revise` -/
inductive WMJudgmentCtx {State : Type*} [EvidenceType State]
    (Γ : Set State) : State → Prop
  | base (W : State) (hW : W ∈ Γ) : WMJudgmentCtx Γ W
  | revise {W₁ W₂ : State} :
      WMJudgmentCtx Γ W₁ → WMJudgmentCtx Γ W₂ → WMJudgmentCtx Γ (W₁ + W₂)

notation:50 "⊢wm[" Γ "] " W => WMJudgmentCtx Γ W

/-- Query judgment under a context: extracted evidence from a state derivable in Γ. -/
def WMQueryJudgmentCtx {State Query : Type*} [EvidenceType State] [WorldModel State Query]
    (Γ : Set State) (W : State) (q : Query) (e : Evidence) : Prop :=
  WMJudgmentCtx Γ W ∧ e = WorldModel.evidence (State := State) (Query := Query) W q

notation:50 "⊢q[" Γ "] " W " ⇓ " q " ↦ " e => WMQueryJudgmentCtx Γ W q e

namespace WMJudgmentCtx

variable {State : Type*} [EvidenceType State]

/-- Monotonicity: enlarging the context preserves derivability. -/
theorem mono {Γ Δ : Set State} {W : State} (hSub : Γ ⊆ Δ)
    (h : ⊢wm[Γ] W) : ⊢wm[Δ] W := by
  induction h with
  | base W hW => exact .base W (hSub hW)
  | revise _ _ ih₁ ih₂ => exact .revise ih₁ ih₂

/-- The universal context recovers the original (context-free) judgment. -/
theorem of_univ {W : State} (h : ⊢wm W) : ⊢wm[Set.univ] W := by
  induction h with
  | «axiom» W => exact .base W (Set.mem_univ W)
  | revise _ _ ih₁ ih₂ => exact .revise ih₁ ih₂

/-- Every context-indexed derivation is also a context-free derivation. -/
theorem toWMJudgment {Γ : Set State} {W : State} (h : ⊢wm[Γ] W) : ⊢wm W := by
  induction h with
  | base W _ => exact .axiom W
  | revise _ _ ih₁ ih₂ => exact .revise ih₁ ih₂

/-- Context composition: revising states from different contexts yields a state
derivable from the union of contexts. -/
theorem union_revise {Γ₁ Γ₂ : Set State} {W₁ W₂ : State}
    (h₁ : ⊢wm[Γ₁] W₁) (h₂ : ⊢wm[Γ₂] W₂) :
    ⊢wm[Γ₁ ∪ Γ₂] (W₁ + W₂) :=
  .revise (mono Set.subset_union_left h₁) (mono Set.subset_union_right h₂)

variable {Query : Type*} [WorldModel State Query]

/-- Query from a context-indexed base state. -/
theorem query_of_base (Γ : Set State) (W : State) (hW : W ∈ Γ) (q : Query) :
    ⊢q[Γ] W ⇓ q ↦ (WorldModel.evidence (State := State) (Query := Query) W q) :=
  ⟨.base W hW, rfl⟩

/-- Query revision under contexts. -/
theorem query_revise {Γ : Set State} {W₁ W₂ : State} {q : Query} {e₁ e₂ : Evidence}
    (h₁ : ⊢q[Γ] W₁ ⇓ q ↦ e₁) (h₂ : ⊢q[Γ] W₂ ⇓ q ↦ e₂) :
    ⊢q[Γ] (W₁ + W₂) ⇓ q ↦ (e₁ + e₂) := by
  rcases h₁ with ⟨hW₁, rfl⟩
  rcases h₂ with ⟨hW₂, rfl⟩
  refine ⟨.revise hW₁ hW₂, ?_⟩
  simpa using
    (WorldModel.evidence_add' (State := State) (Query := Query) W₁ W₂ q).symm

end WMJudgmentCtx

/-! ## Multiset-indexed WM judgments (provenance-multiplicity-aware)

`WMJudgmentMulti` parallels `WMJudgmentCtx` but uses `Multiset State` instead of
`Set State`. This preserves provenance multiplicity: if the same CPT observation
is used twice (independently), the multiset `{|cpt, cpt|}` records both uses,
whereas `Set` would collapse to `{cpt}`.

Key design choices:
- `base` checks `W ∈ Γ` where `∈` is multiset membership
- `≤` (submultiset) replaces `⊆` for monotonicity
- `+` (multiset sum) replaces `∪` for composition
-/

/-- Multiset-indexed WM judgment: tracks provenance with multiplicity. -/
inductive WMJudgmentMulti {State : Type*} [EvidenceType State]
    (Γ : Multiset State) : State → Prop
  | base (W : State) (hW : W ∈ Γ) : WMJudgmentMulti Γ W
  | revise {W₁ W₂ : State} :
      WMJudgmentMulti Γ W₁ → WMJudgmentMulti Γ W₂ → WMJudgmentMulti Γ (W₁ + W₂)

notation:50 "⊢wmm[" Γ "] " W => WMJudgmentMulti Γ W

namespace WMJudgmentMulti

variable {State : Type*} [EvidenceType State]

/-- Monotonicity: enlarging the multiset (submultiset) preserves derivability. -/
theorem mono {Γ Δ : Multiset State} {W : State} (hSub : Γ ≤ Δ)
    (h : ⊢wmm[Γ] W) : ⊢wmm[Δ] W := by
  induction h with
  | base W hW => exact .base W (Multiset.mem_of_le hSub hW)
  | revise _ _ ih₁ ih₂ => exact .revise ih₁ ih₂

/-- Bridge to Set-based context: forget multiplicity. -/
theorem toCtx {Γ : Multiset State} {W : State} (h : ⊢wmm[Γ] W) :
    ⊢wm[{x | x ∈ Γ}] W := by
  induction h with
  | base W hW => exact .base W hW
  | revise _ _ ih₁ ih₂ => exact .revise ih₁ ih₂

/-- Every context-indexed (Multiset) derivation is also context-free. -/
theorem toWMJudgment {Γ : Multiset State} {W : State} (h : ⊢wmm[Γ] W) : ⊢wm W := by
  induction h with
  | base W _ => exact .axiom W
  | revise _ _ ih₁ ih₂ => exact .revise ih₁ ih₂

/-- Composition: revising states from different multiset contexts yields a state
derivable from the combined multiset. -/
theorem add_revise {Γ₁ Γ₂ : Multiset State} {W₁ W₂ : State}
    (h₁ : ⊢wmm[Γ₁] W₁) (h₂ : ⊢wmm[Γ₂] W₂) :
    ⊢wmm[Γ₁ + Γ₂] (W₁ + W₂) :=
  .revise (mono (Multiset.le_add_right Γ₁ Γ₂) h₁)
    (mono (Multiset.le_add_left Γ₂ Γ₁) h₂)

/-- A singleton multiset derives its sole element. -/
theorem singleton_derivable (W : State) : ⊢wmm[{W}] W :=
  .base W (Multiset.mem_singleton_self W)

/-- The sum of a nonempty multiset is derivable from it. -/
theorem sum_derivable (Γ : Multiset State) (hne : Γ ≠ 0) :
    ⊢wmm[Γ] Γ.sum := by
  induction Γ using Multiset.induction_on with
  | empty => exact absurd rfl hne
  | cons a s ih =>
    rw [Multiset.sum_cons]
    by_cases hs : s = 0
    · subst hs; simp; exact singleton_derivable a
    · exact .revise (.base a (Multiset.mem_cons_self a s))
        (mono (Multiset.le_cons_self s a) (ih hs))

end WMJudgmentMulti

/-! ## Standard prop/link wrappers (when `Query = PLNQuery Atom`) -/

namespace PLNQuery

variable {State Atom : Type*} [EvidenceType State] [WorldModel State (PLNQuery Atom)]

def propEvidence (W : State) (a : Atom) : Evidence :=
  WorldModel.evidence (State := State) (Query := PLNQuery Atom) W (.prop a)

def linkEvidence (W : State) (a b : Atom) : Evidence :=
  WorldModel.evidence (State := State) (Query := PLNQuery Atom) W (.link a b)

def linkCondEvidence (W : State) (as : List Atom) (b : Atom) : Evidence :=
  WorldModel.evidence (State := State) (Query := PLNQuery Atom) W (.linkCond as b)

noncomputable def propStrength (W : State) (a : Atom) : ℝ≥0∞ :=
  Evidence.toStrength (propEvidence (State := State) (Atom := Atom) W a)

noncomputable def linkStrength (W : State) (a b : Atom) : ℝ≥0∞ :=
  Evidence.toStrength (linkEvidence (State := State) (Atom := Atom) W a b)

noncomputable def propWTV (κ : ℝ≥0∞) (W : State) (a : Atom) : PLNWeightTV.WTV :=
  Evidence.toWTV κ (propEvidence (State := State) (Atom := Atom) W a)

noncomputable def linkWTV (κ : ℝ≥0∞) (W : State) (a b : Atom) : PLNWeightTV.WTV :=
  Evidence.toWTV κ (linkEvidence (State := State) (Atom := Atom) W a b)

theorem propEvidence_add (W₁ W₂ : State) (a : Atom) :
    propEvidence (State := State) (Atom := Atom) (W₁ + W₂) a =
      propEvidence (State := State) (Atom := Atom) W₁ a +
        propEvidence (State := State) (Atom := Atom) W₂ a := by
  simpa [propEvidence] using WorldModel.evidence_add' (State := State) (Query := PLNQuery Atom) W₁ W₂
    (.prop a)

theorem linkEvidence_add (W₁ W₂ : State) (a b : Atom) :
    linkEvidence (State := State) (Atom := Atom) (W₁ + W₂) a b =
      linkEvidence (State := State) (Atom := Atom) W₁ a b +
        linkEvidence (State := State) (Atom := Atom) W₂ a b := by
  simpa [linkEvidence] using WorldModel.evidence_add' (State := State) (Query := PLNQuery Atom) W₁ W₂
    (.link a b)

end PLNQuery

end Mettapedia.Logic.PLNWorldModel
