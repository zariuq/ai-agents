import Mettapedia.Languages.ProcessCalculi.PiCalculus.WeakBisim
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu

/-!
# Weak Bisimilarity over Derived ρ Steps

Derived counterpart to `WeakBisim.lean`, using `⇝ᵈ` / `⇝ᵈ*` as the operational
relation. This keeps non-core administrative traces (replication/ν helpers)
inside an explicit semantic layer.
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedRepNu
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Weak N-restricted barbed bisimilarity over derived ρ reductions. -/
def WeakRestrictedBisimD (N : Finset String) (p q : Pattern) : Prop :=
  ∃ R : Pattern → Pattern → Prop,
    (∀ p₁ q₁, R p₁ q₁ → R q₁ p₁) ∧
    (∀ p₁ q₁, R p₁ q₁ → ∀ p₂, Nonempty (p₁ ⇝ᵈ p₂) →
      ∃ q₂, Nonempty (q₁ ⇝ᵈ* q₂) ∧ R p₂ q₂) ∧
    (∀ p₁ q₁, R p₁ q₁ → ∀ x ∈ N,
      RhoObservableSC p₁ (.fvar x) → RhoObservableSC q₁ (.fvar x)) ∧
    R p q

notation:50 p " ≈ᵈ{" N "}" q => WeakRestrictedBisimD N p q

/-- Derived weak bisimilarity is reflexive. -/
theorem WeakRestrictedBisimD.refl (N : Finset String) (p : Pattern) : p ≈ᵈ{N} p := by
  refine ⟨Eq, fun _ _ h => h.symm, ?_, ?_, rfl⟩
  · intro p₁ q₁ h p₂ hp₂
    subst h
    exact ⟨p₂, ⟨ReducesDerivedStar.step (Classical.choice hp₂) (.refl _)⟩, rfl⟩
  · intro p₁ q₁ h x _ hobs
    subst h
    exact hobs

/-- Derived weak bisimilarity is symmetric. -/
theorem WeakRestrictedBisimD.symm {N : Finset String} {p q : Pattern}
    (h : p ≈ᵈ{N} q) : q ≈ᵈ{N} p := by
  obtain ⟨R, hR_sym, hR_fwd, hR_barb, hR_pq⟩ := h
  exact ⟨R, hR_sym, hR_fwd, hR_barb, hR_sym _ _ hR_pq⟩

/-- Lift one-step weak-forward simulation to derived multi-step. -/
private theorem lift_star_forward
    {R : Pattern → Pattern → Prop}
    (hfwd : ∀ p₁ q₁, R p₁ q₁ → ∀ p₂, Nonempty (p₁ ⇝ᵈ p₂) →
            ∃ q₂, Nonempty (q₁ ⇝ᵈ* q₂) ∧ R p₂ q₂)
    {p q p' : Pattern} (h : R p q) (hstar : Nonempty (p ⇝ᵈ* p')) :
    ∃ q', Nonempty (q ⇝ᵈ* q') ∧ R p' q' := by
  obtain ⟨star⟩ := hstar
  induction star generalizing q with
  | refl =>
    exact ⟨q, ⟨.refl _⟩, h⟩
  | @step _ pmid _ hred rest ih =>
    obtain ⟨qmid, hqmid_star, hR_mid⟩ := hfwd _ _ h _ ⟨hred⟩
    obtain ⟨q', hq'_star, hR'⟩ := ih hR_mid
    refine ⟨q', ?_, hR'⟩
    exact ⟨ReducesDerivedStar.trans (Classical.choice hqmid_star) (Classical.choice hq'_star)⟩

/-- Derived weak bisimilarity is transitive. -/
theorem WeakRestrictedBisimD.trans {N : Finset String} {p q r : Pattern}
    (hpq : p ≈ᵈ{N} q) (hqr : q ≈ᵈ{N} r) : p ≈ᵈ{N} r := by
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

/-- Monotonicity: restricting to fewer observed names preserves derived bisimilarity. -/
theorem WeakRestrictedBisimD.mono {N N' : Finset String} {p q : Pattern}
    (h : p ≈ᵈ{N} q) (hsub : N' ⊆ N) : p ≈ᵈ{N'} q := by
  obtain ⟨R, hR_sym, hR_fwd, hR_barb, hR_pq⟩ := h
  exact ⟨R, hR_sym, hR_fwd, fun p₁ q₁ hr x hx => hR_barb p₁ q₁ hr x (hsub hx), hR_pq⟩

/-- Derived SC bridge on the core-canonical fragment:
SC-equivalent core-canonical terms are derived-weakly bisimilar. -/
theorem WeakRestrictedBisimD.of_SC_coreCanonical {N : Finset String} {p q : Pattern}
    (hsc : p ≡ q) (hp : CoreCanonical p) : p ≈ᵈ{N} q := by
  have hq : CoreCanonical q := coreCanonical_of_SC hp hsc
  refine ⟨fun a b => Nonempty (a ≡ b) ∧ CoreCanonical a ∧ CoreCanonical b, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    rcases hab with ⟨⟨hab⟩, hca, hcb⟩
    exact ⟨⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.symm _ _ hab⟩, hcb, hca⟩
  · intro p₁ q₁ hab p₂ hp₂
    rcases hab with ⟨⟨hsc₁₂⟩, hc₁, _hc₂⟩
    rcases hp₂ with ⟨hstep⟩
    have hcore : Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces p₁ p₂ :=
      ReducesDerived.toCore_of_coreCanonical hc₁ hstep
    have hc₂ : CoreCanonical p₂ := coreCanonical_of_derived_step hc₁ hstep
    have hqcore : Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces q₁ p₂ :=
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction.Reduces.equiv
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.symm _ _ hsc₁₂)
        hcore
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _)
    exact ⟨p₂, ⟨ReducesDerivedStar.step (.core hqcore) (.refl p₂)⟩,
      ⟨⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.refl _⟩, hc₂, hc₂⟩⟩
  · intro p₁ q₁ hab x _hx hobs
    rcases hab with ⟨⟨hsc₁₂⟩, _hc₁, _hc₂⟩
    rcases hobs with ⟨p₁', hsc_p, hobs'⟩
    exact ⟨p₁',
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.trans _ _ _
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.symm _ _ hsc₁₂) hsc_p,
      hobs'⟩
  · exact ⟨⟨hsc⟩, hp, hq⟩

/-- Derived SC bridge (API alias):
SC-equivalent core-canonical terms are derived-weakly bisimilar. -/
theorem WeakRestrictedBisimD.of_SC {N : Finset String} {p q : Pattern}
    (hsc : p ≡ q) (hp : CoreCanonical p) : p ≈ᵈ{N} q :=
  WeakRestrictedBisimD.of_SC_coreCanonical hsc hp

/-- Right-side core-canonical variant of the derived SC bridge. -/
theorem WeakRestrictedBisimD.of_SC_rightCoreCanonical {N : Finset String} {p q : Pattern}
    (hsc : p ≡ q) (hq : CoreCanonical q) : p ≈ᵈ{N} q := by
  have hqp : q ≈ᵈ{N} p :=
    WeakRestrictedBisimD.of_SC
      (N := N)
      (p := q) (q := p)
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence.symm _ _ hsc)
      hq
  exact WeakRestrictedBisimD.symm hqp

/-- Empty observation set: all patterns are derived-weakly bisimilar. -/
theorem WeakRestrictedBisimD.empty (p q : Pattern) : p ≈ᵈ{∅} q := by
  refine ⟨fun _ _ => True, fun _ _ _ => trivial, ?_, ?_, trivial⟩
  · intro p₁ q₁ _ p₂ _hp₂
    exact ⟨q₁, ⟨.refl _⟩, trivial⟩
  · intro _ _ _ x hx
    simp at hx

end Mettapedia.Languages.ProcessCalculi.PiCalculus
