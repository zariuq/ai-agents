import Mettapedia.Languages.ProcessCalculi.PiCalculus.RhoEncoding
import Mettapedia.Languages.ProcessCalculi.PiCalculus.MultiStep
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MultiStep
import Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation

/-!
# Weak Bisimilarity Infrastructure for π→ρ Encoding

Buildable bisimulation layer for the active π→ρ development.

## Contents

- `RhoBisimilar`: Strong bisimilarity for ρ-calculus (Prop-valued)
- `WeakRestrictedBisim`: Weak N-restricted barbed bisimilarity (Lybech 2022)
- `forward_single_step`, `forward_multi_step`: wrappers over the proven RF fragment

## Notes

Forward simulation here is intentionally scoped to the restriction-free (RF)
fragment and reuses the proved theorems from `ForwardSimulation.lean`.
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Bisimulation for ρ-calculus -/

/-- Bisimulation for ρ-calculus processes (Prop-valued version).

    Two patterns are bisimilar if there exists a bisimulation relation
    relating them. Uses Nonempty to convert Type-valued Reduces to Prop. -/
def RhoBisimilar (p q : Pattern) : Prop :=
  ∃ R : Pattern → Pattern → Prop,
    (∀ p₁ q₁, R p₁ q₁ → R q₁ p₁) ∧  -- Symmetry
    (∀ p₁ q₁, R p₁ q₁ → ∀ p₂, Nonempty (Reduction.Reduces p₁ p₂) →
     ∃ q₂, Nonempty (Reduction.Reduces q₁ q₂) ∧ R p₂ q₂) ∧  -- Forward
    (∀ p₁ q₁, R p₁ q₁ → ∀ q₂, Nonempty (Reduction.Reduces q₁ q₂) →
     ∃ p₂, Nonempty (Reduction.Reduces p₁ p₂) ∧ R p₂ q₂) ∧  -- Backward
    R p q

notation:50 p " ∼ρ " q => RhoBisimilar p q

/-- Bisimilarity is reflexive. -/
theorem RhoBisimilar.refl (p : Pattern) : p ∼ρ p := by
  refine ⟨Eq, fun _ _ h => h.symm, ?_, ?_, rfl⟩
  · intro p₁ q₁ h p₂ hp₂; subst h; exact ⟨p₂, hp₂, rfl⟩
  · intro p₁ q₁ h q₂ hq₂; subst h; exact ⟨q₂, hq₂, rfl⟩

/-- Bisimilarity is symmetric. -/
theorem RhoBisimilar.symm {p q : Pattern} (h : p ∼ρ q) : q ∼ρ p := by
  obtain ⟨R, hR_sym, hR_fwd, hR_bwd, hR_pq⟩ := h
  exact ⟨R, hR_sym, hR_fwd, hR_bwd, hR_sym _ _ hR_pq⟩

/-- Bisimilarity is transitive. -/
theorem RhoBisimilar.trans {p q r : Pattern} (hpq : p ∼ρ q) (hqr : q ∼ρ r) : p ∼ρ r := by
  obtain ⟨R₁, hR₁_sym, hR₁_fwd, hR₁_bwd, hR₁_pq⟩ := hpq
  obtain ⟨R₂, hR₂_sym, hR₂_fwd, hR₂_bwd, hR₂_qr⟩ := hqr
  let S := fun a c => (∃ b, R₁ a b ∧ R₂ b c) ∨ (∃ b, R₂ a b ∧ R₁ b c)
  refine ⟨S, ?_, ?_, ?_, Or.inl ⟨q, hR₁_pq, hR₂_qr⟩⟩
  · intro a c hac
    rcases hac with ⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩
    · exact Or.inr ⟨b, hR₂_sym _ _ hbc, hR₁_sym _ _ hab⟩
    · exact Or.inl ⟨b, hR₁_sym _ _ hbc, hR₂_sym _ _ hab⟩
  · intro a c hac a' ha'
    rcases hac with ⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩
    · obtain ⟨b', hb', h₁⟩ := hR₁_fwd _ _ hab _ ha'
      obtain ⟨c', hc', h₂⟩ := hR₂_fwd _ _ hbc _ hb'
      exact ⟨c', hc', Or.inl ⟨b', h₁, h₂⟩⟩
    · obtain ⟨b', hb', h₂⟩ := hR₂_fwd _ _ hab _ ha'
      obtain ⟨c', hc', h₁⟩ := hR₁_fwd _ _ hbc _ hb'
      exact ⟨c', hc', Or.inr ⟨b', h₂, h₁⟩⟩
  · intro a c hac c' hc'
    rcases hac with ⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩
    · obtain ⟨b', hb', h₂⟩ := hR₂_bwd _ _ hbc _ hc'
      obtain ⟨a', ha', h₁⟩ := hR₁_bwd _ _ hab _ hb'
      exact ⟨a', ha', Or.inl ⟨b', h₁, h₂⟩⟩
    · obtain ⟨b', hb', h₁⟩ := hR₁_bwd _ _ hbc _ hc'
      obtain ⟨a', ha', h₂⟩ := hR₂_bwd _ _ hab _ hb'
      exact ⟨a', ha', Or.inr ⟨b', h₂, h₁⟩⟩

/-! ## Observability -/

/-- Observable output in ρ-calculus: P ⇓ n means P can output on name n. -/
def RhoObservableOutput (P : Pattern) (n : Pattern) : Prop :=
  ∃ q, (∃ ps, P = .collection .hashBag ps none ∧
              .apply "POutput" [n, q] ∈ ps) ∨
       (∃ P' ps, Nonempty (ReducesStar P P') ∧
                 P' = .collection .hashBag ps none ∧
                 .apply "POutput" [n, q] ∈ ps)

notation:50 P " ↓ρ " n => RhoObservableOutput P n

/-- SC-closed observable output: P has a barb modulo structural congruence. -/
def RhoObservableSC (P : Pattern) (n : Pattern) : Prop :=
  ∃ P', (P ≡ P') ∧ RhoObservableOutput P' n

/-- Immediate barbs imply SC-closed barbs (via SC.refl). -/
theorem RhoObservableSC.of_obs {P n : Pattern} (h : RhoObservableOutput P n) :
    RhoObservableSC P n :=
  ⟨P, .refl _, h⟩

/-! ## Weak N-Restricted Barbed Bisimilarity (Lybech 2022, p. 99)

Following Lybech: observations restricted to channels in N ⊆ fn(P).
Namespace machinery names (n++"_L", n++"_R") are NOT in fn(P),
so different namespace assignments preserve this bisimilarity. -/

/-- Weak N-restricted barbed bisimilarity.
    Two ρ-patterns are weakly bisimilar restricted to names in N if there exists
    a symmetric relation R such that:
    - R relates the two patterns
    - One-step reductions are matched by zero-or-more steps (weak)
    - Barbs on channels `.fvar x` for `x ∈ N` are preserved
    Reference: Lybech (2022), Definition of ≈N, page 99. -/
def WeakRestrictedBisim (N : Finset String) (p q : Pattern) : Prop :=
  ∃ R : Pattern → Pattern → Prop,
    (∀ p₁ q₁, R p₁ q₁ → R q₁ p₁) ∧
    (∀ p₁ q₁, R p₁ q₁ → ∀ p₂, Nonempty (Reduction.Reduces p₁ p₂) →
     ∃ q₂, Nonempty (ReducesStar q₁ q₂) ∧ R p₂ q₂) ∧
    (∀ p₁ q₁, R p₁ q₁ → ∀ x ∈ N,
     RhoObservableSC p₁ (.fvar x) → RhoObservableSC q₁ (.fvar x)) ∧
    R p q

notation:50 p " ≈{" N "}" q => WeakRestrictedBisim N p q

/-- WeakRestrictedBisim is reflexive. -/
theorem WeakRestrictedBisim.refl (N : Finset String) (p : Pattern) : p ≈{N} p := by
  refine ⟨Eq, fun _ _ h => h.symm, ?_, ?_, rfl⟩
  · intro p₁ q₁ h p₂ hp₂
    subst h; exact ⟨p₂, ⟨ReducesStar.step (Classical.choice hp₂) (.refl _)⟩, rfl⟩
  · intro p₁ q₁ h x _ hobs; subst h; exact hobs

/-- WeakRestrictedBisim is symmetric. -/
theorem WeakRestrictedBisim.symm {N : Finset String} {p q : Pattern}
    (h : p ≈{N} q) : q ≈{N} p := by
  obtain ⟨R, hR_sym, hR_fwd, hR_barb, hR_pq⟩ := h
  exact ⟨R, hR_sym, hR_fwd, hR_barb, hR_sym _ _ hR_pq⟩

/-- Lift one-step weak forward simulation to multi-step. -/
private theorem lift_star_forward
    {R : Pattern → Pattern → Prop}
    (hfwd : ∀ p₁ q₁, R p₁ q₁ → ∀ p₂, Nonempty (Reduction.Reduces p₁ p₂) →
            ∃ q₂, Nonempty (ReducesStar q₁ q₂) ∧ R p₂ q₂)
    {p q p' : Pattern} (h : R p q) (hstar : Nonempty (ReducesStar p p')) :
    ∃ q', Nonempty (ReducesStar q q') ∧ R p' q' := by
  obtain ⟨star⟩ := hstar
  induction star generalizing q with
  | refl => exact ⟨q, ⟨.refl _⟩, h⟩
  | @step _ pmid _ hred rest ih =>
    obtain ⟨qmid, hqmid_star, hR_mid⟩ := hfwd _ _ h _ ⟨hred⟩
    obtain ⟨q', hq'_star, hR'⟩ := ih hR_mid
    exact ⟨q', ⟨(Classical.choice hqmid_star).trans (Classical.choice hq'_star)⟩, hR'⟩

/-- WeakRestrictedBisim is transitive. -/
theorem WeakRestrictedBisim.trans {N : Finset String} {p q r : Pattern}
    (hpq : p ≈{N} q) (hqr : q ≈{N} r) : p ≈{N} r := by
  obtain ⟨R₁, hR₁_sym, hR₁_fwd, hR₁_barb, hR₁_pq⟩ := hpq
  obtain ⟨R₂, hR₂_sym, hR₂_fwd, hR₂_barb, hR₂_qr⟩ := hqr
  let S := fun a c => (∃ b, R₁ a b ∧ R₂ b c) ∨ (∃ b, R₂ a b ∧ R₁ b c)
  refine ⟨S, ?_, ?_, ?_, Or.inl ⟨q, hR₁_pq, hR₂_qr⟩⟩
  · intro a c hac
    rcases hac with ⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩
    · exact Or.inr ⟨b, hR₂_sym _ _ hbc, hR₁_sym _ _ hab⟩
    · exact Or.inl ⟨b, hR₁_sym _ _ hbc, hR₂_sym _ _ hab⟩
  · intro a c hac a' ha'
    rcases hac with ⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩
    · obtain ⟨b', hb'_star, hR₁'⟩ := hR₁_fwd _ _ hab _ ha'
      obtain ⟨c', hc'_star, hR₂'⟩ := lift_star_forward hR₂_fwd hbc hb'_star
      exact ⟨c', hc'_star, Or.inl ⟨b', hR₁', hR₂'⟩⟩
    · obtain ⟨b', hb'_star, hR₂'⟩ := hR₂_fwd _ _ hab _ ha'
      obtain ⟨c', hc'_star, hR₁'⟩ := lift_star_forward hR₁_fwd hbc hb'_star
      exact ⟨c', hc'_star, Or.inr ⟨b', hR₂', hR₁'⟩⟩
  · intro a c hac x hx hobs
    rcases hac with ⟨b, hab, hbc⟩ | ⟨b, hab, hbc⟩
    · exact hR₂_barb _ _ hbc x hx (hR₁_barb _ _ hab x hx hobs)
    · exact hR₁_barb _ _ hbc x hx (hR₂_barb _ _ hab x hx hobs)

/-- Monotonicity: restricting to fewer names preserves bisimilarity. -/
theorem WeakRestrictedBisim.mono {N N' : Finset String} {p q : Pattern}
    (h : p ≈{N} q) (hsub : N' ⊆ N) : p ≈{N'} q := by
  obtain ⟨R, hR_sym, hR_fwd, hR_barb, hR_pq⟩ := h
  exact ⟨R, hR_sym, hR_fwd, fun p₁ q₁ hr x hx => hR_barb p₁ q₁ hr x (hsub hx), hR_pq⟩

/-- ρ-SC implies weak restricted bisimilarity (for any N).
    SC processes have identical reduction behavior. -/
theorem WeakRestrictedBisim.of_SC {N : Finset String} {p q : Pattern}
    (h : p ≡ q) : p ≈{N} q := by
  refine ⟨fun a b => Nonempty (a ≡ b), ?_, ?_, ?_, ⟨h⟩⟩
  · intro p₁ q₁ ⟨hsc⟩; exact ⟨.symm _ _ hsc⟩
  · intro p₁ q₁ ⟨hsc⟩ p₂ ⟨hred⟩
    exact ⟨p₂, ⟨.step (Reduces.equiv (.symm _ _ hsc) hred (.refl _)) (.refl _)⟩, ⟨.refl _⟩⟩
  · intro p₁ q₁ ⟨hsc⟩ x _hx ⟨p₁', hsc_p, hobs⟩
    exact ⟨p₁', .trans _ _ _ (.symm _ _ hsc) hsc_p, hobs⟩

/-- Empty restriction: any two processes are bisimilar when nothing is observed. -/
theorem WeakRestrictedBisim.empty (p q : Pattern) : p ≈{∅} q := by
  refine ⟨fun _ _ => True, fun _ _ _ => trivial, ?_, ?_, trivial⟩
  · intro p₁ q₁ _ p₂ hp₂; exact ⟨q₁, ⟨.refl _⟩, trivial⟩
  · intro _ _ _ x hx; simp at hx

/-! ## Forward Simulation Wrappers (RF Fragment)

`ForwardSimulation.lean` proves the forward direction with no proof gaps for:
- single-step `ReducesRF`
- multi-step `MultiStepRF`
under explicit RF and COMM-safety hypotheses.
-/

/-- Forward simulation for one RF π-step. -/
theorem forward_single_step {P Q : Process}
    (h : ForwardSimulation.ReducesRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.CommSafe h) :
    ∀ (n v : String),
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ (T ≡ encode Q n v) :=
  ForwardSimulation.forward_single_step_rf h hrf hsafe

/-- Forward simulation for RF multi-step reduction. -/
theorem forward_multi_step {P Q : Process}
    (h : ForwardSimulation.MultiStepRF P Q)
    (hrf : ForwardSimulation.RestrictionFree P)
    (hsafe : ForwardSimulation.MultiCommSafe h) :
    ∀ (n v : String),
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ (T ≡ encode Q n v) :=
  ForwardSimulation.forward_multi_step_rf h hrf hsafe

end Mettapedia.Languages.ProcessCalculi.PiCalculus
