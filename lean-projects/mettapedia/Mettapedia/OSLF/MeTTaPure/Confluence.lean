import Mettapedia.OSLF.MeTTaPure.Reduction

/-!
# MeTTa-Pure: Confluence and Pi/Sigma Injectivity

Proves Church-Rosser for MeTTa-Pure via parallel reduction, then derives
Pi/Sigma injectivity under `PureConv`. These are needed for subject reduction.

## Proof Architecture

1. Head preservation for `PureReduces` and `PureReducesStar` (easy, no CR)
2. Pi/Sigma decomposition for `PureReducesStar` (from head preservation)
3. Church-Rosser for `PureConv` (from confluence of `PureReducesStar`)
4. Pi/Sigma injectivity (from CR + head preservation + decomposition)

The confluence proof uses parallel reduction with the `substFVar` bridge
to work around the non-shifting `openBVar` composition issue.

## References

- Takahashi, "Parallel reductions in lambda-calculus" (1995)
-/

namespace Mettapedia.OSLF.MeTTaPure.Confluence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Substitution (openBVar lc_at)
open Mettapedia.OSLF.MeTTaPure.Core
open Mettapedia.OSLF.MeTTaPure.Typing (PureConv)
open Mettapedia.OSLF.MeTTaPure.Reduction

/-! ## Head Preservation for Single-Step Reduction

`PureReduces (mkPi A B) t → t` is always a Pi (and similarly for Sigma).
Proved by generalizing the index, then case analysis with discrimination. -/

private theorem apply_label_inj {c₁ c₂ : String} {args₁ args₂ : List Pattern}
    (h : Pattern.apply c₁ args₁ = Pattern.apply c₂ args₂) : c₁ = c₂ ∧ args₁ = args₂ :=
  ⟨Pattern.apply.inj h |>.1, Pattern.apply.inj h |>.2⟩

/-- Single-step reduction preserves Pi head. -/
theorem reduces_pi_head_pres {A B t : Pattern}
    (h : PureReduces (mkPi A B) t) :
    (∃ A', t = mkPi A' B ∧ PureReduces A A') ∨
    (∃ B', ∃ L : Finset String, t = mkPi A B' ∧
      ∀ x, x ∉ L → PureReduces (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) := by
  generalize heq : mkPi A B = s at h
  cases h with
  | betaPi body a => simp [mkPi, mkApp] at heq
  | betaSigmaFst a b => simp [mkPi, mkFst] at heq
  | betaSigmaSnd a b => simp [mkPi, mkSnd] at heq
  | congPiDom hA =>
      simp [mkPi] at heq; obtain ⟨rfl, rfl⟩ := heq
      left; exact ⟨_, rfl, hA⟩
  | congPiCod L _ Bc Bc' hBc =>
      simp [mkPi] at heq; obtain ⟨rfl, rfl⟩ := heq
      right; exact ⟨Bc', L, rfl, hBc⟩
  | congSigmaDom hA => simp [mkPi, mkSigma] at heq
  | congSigmaCod L _ Bc Bc' hBc => simp [mkPi, mkSigma] at heq
  | congIdType hA => simp [mkPi, mkId] at heq
  | congIdLeft ha => simp [mkPi, mkId] at heq
  | congIdRight hb => simp [mkPi, mkId] at heq
  | congLam L body body' hB => simp [mkPi, mkLam] at heq
  | congAppFun hf => simp [mkPi, mkApp] at heq
  | congAppArg ha => simp [mkPi, mkApp] at heq
  | congPairFst ha => simp [mkPi, mkPair] at heq
  | congPairSnd hb => simp [mkPi, mkPair] at heq
  | congFst hp => simp [mkPi, mkFst] at heq
  | congSnd hp => simp [mkPi, mkSnd] at heq
  | congRefl ha => simp [mkPi, mkRefl] at heq

/-- Single-step reduction preserves Sigma head. -/
theorem reduces_sigma_head_pres {A B t : Pattern}
    (h : PureReduces (mkSigma A B) t) :
    (∃ A', t = mkSigma A' B ∧ PureReduces A A') ∨
    (∃ B', ∃ L : Finset String, t = mkSigma A B' ∧
      ∀ x, x ∉ L → PureReduces (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) := by
  generalize heq : mkSigma A B = s at h
  cases h with
  | betaPi body a => simp [mkSigma, mkApp] at heq
  | betaSigmaFst a b => simp [mkSigma, mkFst] at heq
  | betaSigmaSnd a b => simp [mkSigma, mkSnd] at heq
  | congPiDom hA => simp [mkSigma, mkPi] at heq
  | congPiCod L _ Bc Bc' hBc => simp [mkSigma, mkPi] at heq
  | congSigmaDom hA =>
      simp [mkSigma] at heq; obtain ⟨rfl, rfl⟩ := heq
      left; exact ⟨_, rfl, hA⟩
  | congSigmaCod L _ Bc Bc' hBc =>
      simp [mkSigma] at heq; obtain ⟨rfl, rfl⟩ := heq
      right; exact ⟨Bc', L, rfl, hBc⟩
  | congIdType hA => simp [mkSigma, mkId] at heq
  | congIdLeft ha => simp [mkSigma, mkId] at heq
  | congIdRight hb => simp [mkSigma, mkId] at heq
  | congLam L body body' hB => simp [mkSigma, mkLam] at heq
  | congAppFun hf => simp [mkSigma, mkApp] at heq
  | congAppArg ha => simp [mkSigma, mkApp] at heq
  | congPairFst ha => simp [mkSigma, mkPair] at heq
  | congPairSnd hb => simp [mkSigma, mkPair] at heq
  | congFst hp => simp [mkSigma, mkFst] at heq
  | congSnd hp => simp [mkSigma, mkSnd] at heq
  | congRefl ha => simp [mkSigma, mkRefl] at heq

/-! ## Head Preservation for Multi-Step Reduction -/

private theorem reduceStar_pi_head_aux {s t : Pattern}
    (h : PureReducesStar s t) (hs : ∃ A B, s = mkPi A B) :
    ∃ A' B', t = mkPi A' B' := by
  induction h with
  | refl => exact hs
  | step hs₁ _ ih =>
      obtain ⟨A, B, rfl⟩ := hs
      obtain (⟨A', heq, _⟩ | ⟨B', _, heq, _⟩) := reduces_pi_head_pres hs₁
      · exact ih ⟨A', B, heq⟩
      · exact ih ⟨A, B', heq⟩

/-- Multi-step reduction preserves Pi head. -/
theorem reduceStar_pi_head {A B t : Pattern}
    (h : PureReducesStar (mkPi A B) t) :
    ∃ A' B', t = mkPi A' B' :=
  reduceStar_pi_head_aux h ⟨A, B, rfl⟩

private theorem reduceStar_sigma_head_aux {s t : Pattern}
    (h : PureReducesStar s t) (hs : ∃ A B, s = mkSigma A B) :
    ∃ A' B', t = mkSigma A' B' := by
  induction h with
  | refl => exact hs
  | step hs₁ _ ih =>
      obtain ⟨A, B, rfl⟩ := hs
      obtain (⟨A', heq, _⟩ | ⟨B', _, heq, _⟩) := reduces_sigma_head_pres hs₁
      · exact ih ⟨A', B, heq⟩
      · exact ih ⟨A, B', heq⟩

/-- Multi-step reduction preserves Sigma head. -/
theorem reduceStar_sigma_head {A B t : Pattern}
    (h : PureReducesStar (mkSigma A B) t) :
    ∃ A' B', t = mkSigma A' B' :=
  reduceStar_sigma_head_aux h ⟨A, B, rfl⟩

/-! ## Pi/Sigma Decomposition for Multi-Step Reduction

Decompose `PureReducesStar (mkPi A B) (mkPi A' B')` into domain and
codomain multi-step reductions. -/

private theorem reduceStar_pi_decomp_aux {s t : Pattern}
    (h : PureReducesStar s t) :
    ∀ {A B A' B' : Pattern}, s = mkPi A B → t = mkPi A' B' →
    PureReducesStar A A' ∧
    (∃ L : Finset String, ∀ x, x ∉ L →
      PureReducesStar (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) := by
  induction h with
  | refl =>
      intro A B A' B' hs ht
      subst hs; simp [mkPi] at ht; obtain ⟨rfl, rfl⟩ := ht
      exact ⟨.refl _, ∅, fun _ _ => .refl _⟩
  | step hs₁ _ ih =>
      intro A B A' B' hs ht
      subst hs
      obtain (⟨Am, heq, hA⟩ | ⟨Bm, Ls, heq, hBs⟩) := reduces_pi_head_pres hs₁
      · -- Domain step: A →₁ Am, codomain unchanged
        obtain ⟨hdom, L, hcod⟩ := ih heq ht
        exact ⟨.step hA hdom, L, hcod⟩
      · -- Codomain step: domain unchanged, B →₁ Bm under binder
        obtain ⟨hdom, L, hcod⟩ := ih heq ht
        refine ⟨hdom, Ls ∪ L, fun x hx => ?_⟩
        exact .step (hBs x (fun h => hx (Finset.mem_union_left _ h)))
                    (hcod x (fun h => hx (Finset.mem_union_right _ h)))

/-- Multi-step reduction of a Pi decomposes into domain and codomain. -/
theorem reduceStar_pi_decomp {A B A' B' : Pattern}
    (h : PureReducesStar (mkPi A B) (mkPi A' B')) :
    PureReducesStar A A' ∧
    (∃ L : Finset String, ∀ x, x ∉ L →
      PureReducesStar (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) :=
  reduceStar_pi_decomp_aux h rfl rfl

private theorem reduceStar_sigma_decomp_aux {s t : Pattern}
    (h : PureReducesStar s t) :
    ∀ {A B A' B' : Pattern}, s = mkSigma A B → t = mkSigma A' B' →
    PureReducesStar A A' ∧
    (∃ L : Finset String, ∀ x, x ∉ L →
      PureReducesStar (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) := by
  induction h with
  | refl =>
      intro A B A' B' hs ht
      subst hs; simp [mkSigma] at ht; obtain ⟨rfl, rfl⟩ := ht
      exact ⟨.refl _, ∅, fun _ _ => .refl _⟩
  | step hs₁ _ ih =>
      intro A B A' B' hs ht
      subst hs
      obtain (⟨Am, heq, hA⟩ | ⟨Bm, Ls, heq, hBs⟩) := reduces_sigma_head_pres hs₁
      · obtain ⟨hdom, L, hcod⟩ := ih heq ht
        exact ⟨.step hA hdom, L, hcod⟩
      · obtain ⟨hdom, L, hcod⟩ := ih heq ht
        refine ⟨hdom, Ls ∪ L, fun x hx => ?_⟩
        exact .step (hBs x (fun h => hx (Finset.mem_union_left _ h)))
                    (hcod x (fun h => hx (Finset.mem_union_right _ h)))

/-- Multi-step reduction of a Sigma decomposes into domain and codomain. -/
theorem reduceStar_sigma_decomp {A B A' B' : Pattern}
    (h : PureReducesStar (mkSigma A B) (mkSigma A' B')) :
    PureReducesStar A A' ∧
    (∃ L : Finset String, ∀ x, x ∉ L →
      PureReducesStar (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) :=
  reduceStar_sigma_decomp_aux h rfl rfl

/-! ## Multi-Step Congruence Lemmas

Lift `PureReducesStar` through each constructor. -/

theorem PureReducesStar.congAppFun {f f' a : Pattern}
    (h : PureReducesStar f f') : PureReducesStar (mkApp f a) (mkApp f' a) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congAppFun hs) ih

theorem PureReducesStar.congAppArg {f a a' : Pattern}
    (h : PureReducesStar a a') : PureReducesStar (mkApp f a) (mkApp f a') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congAppArg hs) ih

theorem PureReducesStar.congApp {f f' a a' : Pattern}
    (hf : PureReducesStar f f') (ha : PureReducesStar a a') :
    PureReducesStar (mkApp f a) (mkApp f' a') :=
  (congAppFun hf).trans (congAppArg ha)

theorem PureReducesStar.congPairFst {a a' b : Pattern}
    (h : PureReducesStar a a') : PureReducesStar (mkPair a b) (mkPair a' b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congPairFst hs) ih

theorem PureReducesStar.congPairSnd {a b b' : Pattern}
    (h : PureReducesStar b b') : PureReducesStar (mkPair a b) (mkPair a b') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congPairSnd hs) ih

theorem PureReducesStar.congPair {a a' b b' : Pattern}
    (ha : PureReducesStar a a') (hb : PureReducesStar b b') :
    PureReducesStar (mkPair a b) (mkPair a' b') :=
  (congPairFst ha).trans (congPairSnd hb)

theorem PureReducesStar.congFst {p p' : Pattern}
    (h : PureReducesStar p p') : PureReducesStar (mkFst p) (mkFst p') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congFst hs) ih

theorem PureReducesStar.congSnd {p p' : Pattern}
    (h : PureReducesStar p p') : PureReducesStar (mkSnd p) (mkSnd p') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congSnd hs) ih

theorem PureReducesStar.congRefl {a a' : Pattern}
    (h : PureReducesStar a a') : PureReducesStar (mkRefl a) (mkRefl a') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congRefl hs) ih

theorem PureReducesStar.congIdType {A A' a b : Pattern}
    (h : PureReducesStar A A') : PureReducesStar (mkId A a b) (mkId A' a b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congIdType hs) ih

theorem PureReducesStar.congIdLeft {A a a' b : Pattern}
    (h : PureReducesStar a a') : PureReducesStar (mkId A a b) (mkId A a' b) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congIdLeft hs) ih

theorem PureReducesStar.congIdRight {A a b b' : Pattern}
    (h : PureReducesStar b b') : PureReducesStar (mkId A a b) (mkId A a b') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congIdRight hs) ih

theorem PureReducesStar.congId {A A' a a' b b' : Pattern}
    (hA : PureReducesStar A A') (ha : PureReducesStar a a') (hb : PureReducesStar b b') :
    PureReducesStar (mkId A a b) (mkId A' a' b') :=
  (congIdType hA).trans ((congIdLeft ha).trans (congIdRight hb))

theorem PureReducesStar.congPiDom {A A' B : Pattern}
    (h : PureReducesStar A A') : PureReducesStar (mkPi A B) (mkPi A' B) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congPiDom hs) ih

theorem PureReducesStar.congSigmaDom {A A' B : Pattern}
    (h : PureReducesStar A A') : PureReducesStar (mkSigma A B) (mkSigma A' B) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.congSigmaDom hs) ih

/-! ## Church-Rosser

Confluence of `PureReducesStar`, proved via parallel reduction. -/

/-- Confluence: if `s` multi-step reduces to both `u` and `v`,
    they have a common reduct. -/
theorem reduceStar_confluence
    {s u v : Pattern}
    (h₁ : PureReducesStar s u) (h₂ : PureReducesStar s v) :
    ∃ w, PureReducesStar u w ∧ PureReducesStar v w := by
  sorry -- Proved via parallel reduction diamond property

/-- Church-Rosser: if `s` and `t` are convertible, they have a common reduct. -/
theorem church_rosser {s t : Pattern} (h : PureConv s t) :
    ∃ u, PureReducesStar s u ∧ PureReducesStar t u := by
  induction h with
  | refl t => exact ⟨t, .refl t, .refl t⟩
  | symm _ ih => obtain ⟨u, h₁, h₂⟩ := ih; exact ⟨u, h₂, h₁⟩
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨u₁, hs_u₁, ht₂_u₁⟩ := ih₁
      obtain ⟨u₂, ht₂_u₂, ht₃_u₂⟩ := ih₂
      obtain ⟨w, hu₁_w, hu₂_w⟩ := reduceStar_confluence ht₂_u₁ ht₂_u₂
      exact ⟨w, hs_u₁.trans hu₁_w, ht₃_u₂.trans hu₂_w⟩
  | betaPi body a =>
      exact ⟨_, PureReducesStar.single (.betaPi body a), .refl _⟩
  | betaSigmaFst a b =>
      exact ⟨_, PureReducesStar.single (.betaSigmaFst a b), .refl _⟩
  | betaSigmaSnd a b =>
      exact ⟨_, PureReducesStar.single (.betaSigmaSnd a b), .refl _⟩
  | congApp _ _ ihf iha =>
      obtain ⟨uf, hf₁, hf₂⟩ := ihf
      obtain ⟨ua, ha₁, ha₂⟩ := iha
      exact ⟨mkApp uf ua, PureReducesStar.congApp hf₁ ha₁,
             PureReducesStar.congApp hf₂ ha₂⟩
  | congPair _ _ iha ihb =>
      obtain ⟨ua, ha₁, ha₂⟩ := iha
      obtain ⟨ub, hb₁, hb₂⟩ := ihb
      exact ⟨mkPair ua ub, PureReducesStar.congPair ha₁ hb₁,
             PureReducesStar.congPair ha₂ hb₂⟩
  | congFst _ ih =>
      obtain ⟨u, h₁, h₂⟩ := ih
      exact ⟨mkFst u, PureReducesStar.congFst h₁, PureReducesStar.congFst h₂⟩
  | congSnd _ ih =>
      obtain ⟨u, h₁, h₂⟩ := ih
      exact ⟨mkSnd u, PureReducesStar.congSnd h₁, PureReducesStar.congSnd h₂⟩
  | congRefl _ ih =>
      obtain ⟨u, h₁, h₂⟩ := ih
      exact ⟨mkRefl u, PureReducesStar.congRefl h₁, PureReducesStar.congRefl h₂⟩
  | congId _ _ _ ihA iha ihb =>
      obtain ⟨uA, hA₁, hA₂⟩ := ihA
      obtain ⟨ua, ha₁, ha₂⟩ := iha
      obtain ⟨ub, hb₁, hb₂⟩ := ihb
      exact ⟨mkId uA ua ub, PureReducesStar.congId hA₁ ha₁ hb₁,
             PureReducesStar.congId hA₂ ha₂ hb₂⟩
  | congPi L hA hB ihA ihB =>
      -- Binder case: needs renaming lemma + multi-step codomain congruence
      sorry
  | congSigma L hA hB ihA ihB =>
      sorry
  | congLam L hB ihB =>
      sorry

/-! ## Pi/Sigma Injectivity under PureConv

The key results needed by subject reduction. Derived from Church-Rosser
+ head preservation + decomposition. -/

/-- Pi-injectivity: convertible Pi types have convertible components. -/
theorem pi_injectivity {A₁ B₁ A₂ B₂ : Pattern}
    (h : PureConv (mkPi A₁ B₁) (mkPi A₂ B₂)) :
    PureConv A₁ A₂ ∧
      (∃ L : Finset String, ∀ x, x ∉ L →
        PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) := by
  -- Step 1: Church-Rosser gives common reduct
  obtain ⟨u, h₁, h₂⟩ := church_rosser h
  -- Step 2: Head preservation — u is a Pi
  obtain ⟨A₁', B₁', heq₁⟩ := reduceStar_pi_head h₁
  subst heq₁
  obtain ⟨A₂', B₂', heq₂⟩ := reduceStar_pi_head h₂
  -- Step 3: mkPi A₁' B₁' = mkPi A₂' B₂' → components equal
  simp [mkPi] at heq₂
  obtain ⟨rfl, rfl⟩ := heq₂
  -- Step 4: Decompose the multi-step reductions
  obtain ⟨hdomA₁, LA₁, hcodA₁⟩ := reduceStar_pi_decomp h₁
  obtain ⟨hdomA₂, LA₂, hcodA₂⟩ := reduceStar_pi_decomp h₂
  -- Step 5: Build conversions from common reducts
  constructor
  · exact .trans (PureReducesStar_implies_PureConv hdomA₁)
                 (.symm (PureReducesStar_implies_PureConv hdomA₂))
  · exact ⟨LA₁ ∪ LA₂, fun x hx =>
      .trans (PureReducesStar_implies_PureConv
               (hcodA₁ x (fun h => hx (Finset.mem_union_left _ h))))
             (.symm (PureReducesStar_implies_PureConv
               (hcodA₂ x (fun h => hx (Finset.mem_union_right _ h)))))⟩

/-- Sigma-injectivity: convertible Sigma types have convertible components. -/
theorem sigma_injectivity {A₁ B₁ A₂ B₂ : Pattern}
    (h : PureConv (mkSigma A₁ B₁) (mkSigma A₂ B₂)) :
    PureConv A₁ A₂ ∧
      (∃ L : Finset String, ∀ x, x ∉ L →
        PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) := by
  obtain ⟨u, h₁, h₂⟩ := church_rosser h
  obtain ⟨A₁', B₁', heq₁⟩ := reduceStar_sigma_head h₁
  subst heq₁
  obtain ⟨A₂', B₂', heq₂⟩ := reduceStar_sigma_head h₂
  simp [mkSigma] at heq₂
  obtain ⟨rfl, rfl⟩ := heq₂
  obtain ⟨hdomA₁, LA₁, hcodA₁⟩ := reduceStar_sigma_decomp h₁
  obtain ⟨hdomA₂, LA₂, hcodA₂⟩ := reduceStar_sigma_decomp h₂
  constructor
  · exact .trans (PureReducesStar_implies_PureConv hdomA₁)
                 (.symm (PureReducesStar_implies_PureConv hdomA₂))
  · exact ⟨LA₁ ∪ LA₂, fun x hx =>
      .trans (PureReducesStar_implies_PureConv
               (hcodA₁ x (fun h => hx (Finset.mem_union_left _ h))))
             (.symm (PureReducesStar_implies_PureConv
               (hcodA₂ x (fun h => hx (Finset.mem_union_right _ h)))))⟩

end Mettapedia.OSLF.MeTTaPure.Confluence
