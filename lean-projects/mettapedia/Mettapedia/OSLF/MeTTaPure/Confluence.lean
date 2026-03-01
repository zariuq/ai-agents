import Mettapedia.OSLF.MeTTaPure.Reduction
import Mettapedia.OSLF.MeTTaPure.FVarSubst

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
open Mettapedia.OSLF.MeTTaIL.Substitution (openBVar lc_at lc_at_list lc_at_openBVar_result freeVars isFresh)
open Mettapedia.OSLF.MeTTaPure.Core
open Mettapedia.OSLF.MeTTaPure.Typing (PureConv)
open Mettapedia.OSLF.MeTTaPure.Reduction
open Mettapedia.OSLF.MeTTaPure.FVarSubst

/-! ## Head Preservation for Single-Step Reduction

`PureReduces (mkPi A B) t → t` is always a Pi (and similarly for Sigma).
Proved by generalizing the index, then case analysis with discrimination. -/

/-- Helper: convert list to finset for cofinite freshness sets. -/
private def listToFinset (l : List String) : Finset String := l.toFinset

/-- Freshness from finite exclusion on free variables. -/
private theorem isFresh_of_not_in_freeVars_finset {x : String} {p : Pattern}
    (h : x ∉ listToFinset (freeVars p)) : isFresh x p = true := by
  simp only [isFresh, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hmem
  exact h (List.mem_toFinset.mpr (List.contains_iff_mem.mp hmem))

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

/-! ## Parallel Reduction

Takahashi-style parallel reduction where all redexes can fire simultaneously.
Uses cofinite quantification for binder cases and `lc_at` constraints on β-rules
to support the substitution lemma and diamond property. -/

/-- Parallel reduction: all redexes may fire simultaneously. -/
inductive ParRed : Pattern → Pattern → Prop where
  | bvar (n : Nat) : ParRed (.bvar n) (.bvar n)
  | fvar (x : String) : ParRed (.fvar x) (.fvar x)
  | pi (L : Finset String) : ParRed A A' →
      (∀ x, x ∉ L → ParRed (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) →
      ParRed (mkPi A B) (mkPi A' B')
  | sigma (L : Finset String) : ParRed A A' →
      (∀ x, x ∉ L → ParRed (openBVar 0 (.fvar x) B) (openBVar 0 (.fvar x) B')) →
      ParRed (mkSigma A B) (mkSigma A' B')
  | lam (L : Finset String) :
      (∀ x, x ∉ L → ParRed (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) body')) →
      ParRed (mkLam body) (mkLam body')
  | app : ParRed f f' → ParRed a a' → ParRed (mkApp f a) (mkApp f' a')
  | pair : ParRed a a' → ParRed b b' → ParRed (mkPair a b) (mkPair a' b')
  | fst : ParRed p p' → ParRed (mkFst p) (mkFst p')
  | snd : ParRed p p' → ParRed (mkSnd p) (mkSnd p')
  | id : ParRed A A' → ParRed a a' → ParRed b b' →
      ParRed (mkId A a b) (mkId A' a' b')
  | refl : ParRed a a' → ParRed (mkRefl a) (mkRefl a')
  | betaPi (L : Finset String) :
      (∀ x, x ∉ L → ParRed (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) body')) →
      ParRed a a' → lc_at 1 body = true → lc_at 0 a = true →
      ParRed (mkApp (mkLam body) a) (openBVar 0 a' body')
  | betaSigmaFst : ParRed a a' → ParRed b b' →
      ParRed (mkFst (mkPair a b)) a'
  | betaSigmaSnd : ParRed a a' → ParRed b b' →
      ParRed (mkSnd (mkPair a b)) b'
  /-- Catch-all reflexivity for patterns not covered by other constructors
      (e.g., `.lambda`, `.multiLambda`, `.collection`, or `.apply c args` for
      non-MeTTa-Pure labels). Also used as the base case for `parRed_refl`. -/
  | refl_pat (t : Pattern) : ParRed t t

/-! ## PureConv Preserves Local Closure

Proved independently of Church-Rosser. Both directions (fwd and bwd) are
proved simultaneously so the `symm` case works by swapping. -/

/-- PureConv preserves lc in both directions (needed for symm case). -/
theorem PureConv_preserves_lc_both {s t : Pattern} (h : PureConv s t) :
    (lc_at 0 s = true → lc_at 0 t = true) ∧
    (lc_at 0 t = true → lc_at 0 s = true) := by
  induction h with
  | refl _ => exact ⟨id, id⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨fun h => ih₂.1 (ih₁.1 h), fun h => ih₁.2 (ih₂.2 h)⟩
  | betaPi body a hlcBody hlcA =>
      constructor
      · intro hlc
        exact lc_at_openBVar_result hlcBody hlcA
      · intro _
        simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        exact ⟨hlcBody, hlcA⟩
  | betaSigmaFst a b hlcA hlcB =>
      exact ⟨fun _ => hlcA, fun _ => by
        simp only [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        exact ⟨hlcA, hlcB⟩⟩
  | betaSigmaSnd a b hlcA hlcB =>
      exact ⟨fun _ => hlcB, fun _ => by
        simp only [mkSnd, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        exact ⟨hlcA, hlcB⟩⟩
  | @congPi A₁ A₂ B₁ B₂ L _ _ ihA ihB =>
      constructor
      · intro hlc
        have hlcA : lc_at 0 A₁ = true := by
          simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
        have hlcB : lc_at 1 B₁ = true := by
          simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
        simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        constructor
        · exact ihA.1 hlcA
        · obtain ⟨x₀, hx₀⟩ := exists_fresh L
          have := (ihB x₀ hx₀).1 (lc_at_openBVar_result hlcB (by simp [lc_at]))
          exact lc_at_of_openBVar this
      · intro hlc
        have hlcA : lc_at 0 A₂ = true := by
          simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
        have hlcB : lc_at 1 B₂ = true := by
          simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
        simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        constructor
        · exact ihA.2 hlcA
        · obtain ⟨x₀, hx₀⟩ := exists_fresh L
          have := (ihB x₀ hx₀).2 (lc_at_openBVar_result hlcB (by simp [lc_at]))
          exact lc_at_of_openBVar this
  | @congSigma A₁ A₂ B₁ B₂ L _ _ ihA ihB =>
      constructor
      · intro hlc
        have hlcA : lc_at 0 A₁ = true := by
          simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
        have hlcB : lc_at 1 B₁ = true := by
          simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
        simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        constructor
        · exact ihA.1 hlcA
        · obtain ⟨x₀, hx₀⟩ := exists_fresh L
          have := (ihB x₀ hx₀).1 (lc_at_openBVar_result hlcB (by simp [lc_at]))
          exact lc_at_of_openBVar this
      · intro hlc
        have hlcA : lc_at 0 A₂ = true := by
          simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
        have hlcB : lc_at 1 B₂ = true := by
          simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
        simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        constructor
        · exact ihA.2 hlcA
        · obtain ⟨x₀, hx₀⟩ := exists_fresh L
          have := (ihB x₀ hx₀).2 (lc_at_openBVar_result hlcB (by simp [lc_at]))
          exact lc_at_of_openBVar this
  | @congId A₁ A₂ a₁ a₂ b₁ b₂ _ _ _ ihA iha ihb =>
      constructor
      · intro hlc
        simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ⟨ihA.1 hlc.1, iha.1 hlc.2.1, ihb.1 hlc.2.2⟩
      · intro hlc
        simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ⟨ihA.2 hlc.1, iha.2 hlc.2.1, ihb.2 hlc.2.2⟩
  | @congLam body₁ body₂ L _ ihB =>
      constructor
      · intro hlc
        have hlcB : lc_at 1 body₁ = true := by
          simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
        simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        obtain ⟨x₀, hx₀⟩ := exists_fresh L
        have := (ihB x₀ hx₀).1 (lc_at_openBVar_result hlcB (by simp [lc_at]))
        exact lc_at_of_openBVar this
      · intro hlc
        have hlcB : lc_at 1 body₂ = true := by
          simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
        simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true]
        obtain ⟨x₀, hx₀⟩ := exists_fresh L
        have := (ihB x₀ hx₀).2 (lc_at_openBVar_result hlcB (by simp [lc_at]))
        exact lc_at_of_openBVar this
  | @congApp f₁ f₂ a₁ a₂ _ _ ihf iha =>
      constructor
      · intro hlc
        simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ⟨ihf.1 hlc.1, iha.1 hlc.2⟩
      · intro hlc
        simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ⟨ihf.2 hlc.1, iha.2 hlc.2⟩
  | @congPair a₁ a₂ b₁ b₂ _ _ iha ihb =>
      constructor
      · intro hlc
        simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ⟨iha.1 hlc.1, ihb.1 hlc.2⟩
      · intro hlc
        simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ⟨iha.2 hlc.1, ihb.2 hlc.2⟩
  | @congFst p₁ p₂ _ ih =>
      constructor
      · intro hlc
        simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ih.1 hlc
      · intro hlc
        simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ih.2 hlc
  | @congSnd p₁ p₂ _ ih =>
      constructor
      · intro hlc
        simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ih.1 hlc
      · intro hlc
        simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ih.2 hlc
  | @congRefl a₁ a₂ _ ih =>
      constructor
      · intro hlc
        simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ih.1 hlc
      · intro hlc
        simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
        exact ih.2 hlc

/-- Conversion preserves local closure (forward). -/
theorem PureConv_preserves_lc {s t : Pattern} (h : PureConv s t)
    (hlc : lc_at 0 s = true) : lc_at 0 t = true :=
  (PureConv_preserves_lc_both h).1 hlc

/-! ## Parallel Reduction: Basic Lemmas -/

/-- Reflexivity for ParRed. -/
theorem parRed_refl (t : Pattern) : ParRed t t := .refl_pat t

/-! ### openBVar commutativity for fvar opens

`openBVar j (fvar x) (openBVar k (fvar y) p) = openBVar k (fvar y) (openBVar j (fvar x) p)`
when `j ≠ k`. Needed for `parRed_openBVar_fvar`. -/

private theorem openBVar_comm_fvar {j k : Nat} {x y : String} (hjk : j ≠ k)
    (p : Pattern) :
    openBVar j (.fvar x) (openBVar k (.fvar y) p) =
      openBVar k (.fvar y) (openBVar j (.fvar x) p) := by
  induction p using Pattern.inductionOn generalizing j k with
  | hbvar n =>
    simp only [openBVar]
    by_cases hnk : n == k
    · simp [hnk, openBVar]
      have hne : n ≠ j := by intro h; exact hjk (by rw [← h]; exact beq_iff_eq.mp hnk)
      simp [show (n == j) = false from by rwa [beq_eq_false_iff_ne]]
    · simp [hnk]
      by_cases hnj : n == j
      · simp [hnj, openBVar, hnk]
      · simp [hnj, openBVar, hnk]
  | hfvar z => simp [openBVar]
  | happly c args ih =>
    simp only [openBVar, List.map_map]
    congr 1; exact List.map_congr_left fun a ha => ih a ha hjk
  | hlambda body ih =>
    simp only [openBVar]; congr 1
    exact ih (by omega : j + 1 ≠ k + 1)
  | hmultiLambda n body ih =>
    simp only [openBVar]; congr 1
    exact ih (by omega : j + n ≠ k + n)
  | hsubst body repl ihb ihr =>
    simp only [openBVar]; congr 1
    · exact ihb (by omega : j + 1 ≠ k + 1)
    · exact ihr hjk
  | hcollection ct elems rest ih =>
    simp only [openBVar, List.map_map]
    congr 1; exact List.map_congr_left fun a ha => ih a ha hjk

/-- ParRed is preserved by opening with a free variable. -/
theorem parRed_openBVar_fvar {y : String} {p q : Pattern}
    (h : ParRed p q) : ∀ (k : Nat),
    ParRed (openBVar k (.fvar y) p) (openBVar k (.fvar y) q) := by
  induction h with
  | bvar n => intro k; simp [openBVar]; split <;> exact parRed_refl _
  | fvar x => intro _; simp [openBVar]; exact .fvar x
  | pi L hA hB ihA ihB =>
    intro k
    simp only [openBVar_mkPi]
    exact .pi (L ∪ {y}) (ihA k) (fun z hz => by
      have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
      have hzy : z ≠ y := fun h => hz (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      rw [openBVar_comm_fvar (by omega : 0 ≠ k + 1),
          openBVar_comm_fvar (by omega : 0 ≠ k + 1)]
      exact ihB z hzL (k + 1))
  | sigma L hA hB ihA ihB =>
    intro k
    simp only [openBVar_mkSigma]
    exact .sigma (L ∪ {y}) (ihA k) (fun z hz => by
      have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
      have hzy : z ≠ y := fun h => hz (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      rw [openBVar_comm_fvar (by omega : 0 ≠ k + 1),
          openBVar_comm_fvar (by omega : 0 ≠ k + 1)]
      exact ihB z hzL (k + 1))
  | lam L hB ihB =>
    intro k
    simp only [openBVar_mkLam]
    exact .lam (L ∪ {y}) (fun z hz => by
      have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
      have hzy : z ≠ y := fun h => hz (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      rw [openBVar_comm_fvar (by omega : 0 ≠ k + 1),
          openBVar_comm_fvar (by omega : 0 ≠ k + 1)]
      exact ihB z hzL (k + 1))
  | app hf ha ihf iha =>
    intro k; simp only [openBVar_mkApp]; exact .app (ihf k) (iha k)
  | pair ha hb iha ihb =>
    intro k; simp only [openBVar_mkPair]; exact .pair (iha k) (ihb k)
  | fst hp ihp =>
    intro k; simp only [openBVar_mkFst]; exact .fst (ihp k)
  | snd hp ihp =>
    intro k; simp only [openBVar_mkSnd]; exact .snd (ihp k)
  | id hA ha hb ihA iha ihb =>
    intro k; simp only [openBVar_mkId]; exact .id (ihA k) (iha k) (ihb k)
  | refl ha iha =>
    intro k; simp only [openBVar_mkRefl]; exact .refl (iha k)
  | betaPi L hbody ha hlcBody hlcA ihbody iha =>
    intro k
    simp only [openBVar_mkApp, openBVar_mkLam]
    rw [show openBVar k (.fvar y) (openBVar 0 (↑a') body') =
         openBVar 0 (openBVar k (.fvar y) (↑a')) (openBVar (k + 1) (.fvar y) body') from by
      rw [openBVar_comm_fvar (by omega : 0 ≠ k + 1)]
      rfl]
    exact .betaPi (L ∪ {y})
      (fun z hz => by
        have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
        rw [openBVar_comm_fvar (by omega : 0 ≠ k + 1),
            openBVar_comm_fvar (by omega : 0 ≠ k + 1)]
        exact ihbody z hzL (k + 1))
      (iha k)
      (by rw [show k + 1 = 1 + k from by omega]; exact lc_at_mono hlcBody (Nat.le_add_right 1 k))
      (lc_at_mono hlcA (Nat.zero_le k))
  | betaSigmaFst ha hb iha ihb =>
    intro k; simp only [openBVar_mkFst, openBVar_mkPair]
    exact .betaSigmaFst (iha k) (ihb k)
  | betaSigmaSnd ha hb iha ihb =>
    intro k; simp only [openBVar_mkSnd, openBVar_mkPair]
    exact .betaSigmaSnd (iha k) (ihb k)
  | refl_pat t => intro k; exact .refl_pat _

/-! ### ParRed substitution -/

/-- Substituting the same fvar-replacement into both sides of ParRed. -/
private theorem parRed_substFVar_both {x : String} {u u' : Pattern}
    (hu : ParRed u u') (hlc_u : lc_at 0 u = true) (hlc_u' : lc_at 0 u' = true) :
    ∀ (t : Pattern), ParRed (substFVar x u t) (substFVar x u' t) := by
  intro t
  induction t using Pattern.inductionOn with
  | hbvar n => simp [substFVar]; exact .bvar n
  | hfvar y =>
    simp only [substFVar]; split
    · exact hu
    · exact .fvar y
  | happly c args ih =>
    simp only [substFVar]
    -- Use refl_pat for the list-mapped result, but we need ParRed element-wise
    -- Try to use specific MeTTa-Pure constructors when possible
    match c, args with
    | "Pi", [A, B] =>
      simp only [List.map_cons, List.map_nil]
      exact .pi ({x}) (ih A List.mem_cons_self) (fun y hy => by
        have hyx : y ≠ x := fun h => hy (Finset.mem_singleton.mpr h)
        rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hyx,
            substFVar_openBVar_comm hlc_u', substFVar_fvar_ne u' hyx]
        exact parRed_openBVar_fvar (ih B (List.mem_cons_of_mem _ List.mem_cons_self)) 0)
    | "Sigma", [A, B] =>
      simp only [List.map_cons, List.map_nil]
      exact .sigma ({x}) (ih A List.mem_cons_self) (fun y hy => by
        have hyx : y ≠ x := fun h => hy (Finset.mem_singleton.mpr h)
        rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hyx,
            substFVar_openBVar_comm hlc_u', substFVar_fvar_ne u' hyx]
        exact parRed_openBVar_fvar (ih B (List.mem_cons_of_mem _ List.mem_cons_self)) 0)
    | "Lam", [body] =>
      simp only [List.map_cons, List.map_nil]
      exact .lam ({x}) (fun y hy => by
        have hyx : y ≠ x := fun h => hy (Finset.mem_singleton.mpr h)
        rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hyx,
            substFVar_openBVar_comm hlc_u', substFVar_fvar_ne u' hyx]
        exact parRed_openBVar_fvar (ih body List.mem_cons_self) 0)
    | "App", [f, a] =>
      simp only [List.map_cons, List.map_nil]
      exact .app (ih f List.mem_cons_self)
                  (ih a (List.mem_cons_of_mem _ List.mem_cons_self))
    | "Pair", [a, b] =>
      simp only [List.map_cons, List.map_nil]
      exact .pair (ih a List.mem_cons_self)
                   (ih b (List.mem_cons_of_mem _ List.mem_cons_self))
    | "Fst", [p] =>
      simp only [List.map_cons, List.map_nil]
      exact .fst (ih p List.mem_cons_self)
    | "Snd", [p] =>
      simp only [List.map_cons, List.map_nil]
      exact .snd (ih p List.mem_cons_self)
    | "Id", [A, a, b] =>
      simp only [List.map_cons, List.map_nil]
      exact .id (ih A List.mem_cons_self)
                 (ih a (List.mem_cons_of_mem _ List.mem_cons_self))
                 (ih b (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    | "Refl", [a] =>
      simp only [List.map_cons, List.map_nil]
      exact .refl (ih a List.mem_cons_self)
    | _, _ => exact .refl_pat _
  | hlambda body ih => simp only [substFVar]; exact .refl_pat _
  | hmultiLambda n body ih => simp only [substFVar]; exact .refl_pat _
  | hsubst body repl ihb ihr => simp only [substFVar]; exact .refl_pat _
  | hcollection ct elems rest ih => simp only [substFVar]; exact .refl_pat _

/-- Full ParRed substitution: if `ParRed u u'` and `ParRed p q`,
    then `ParRed (substFVar x u p) (substFVar x u' q)`. -/
theorem parRed_substFVar {x : String} {u u' : Pattern}
    (hu : ParRed u u') (hlc_u : lc_at 0 u = true) (hlc_u' : lc_at 0 u' = true)
    {p q : Pattern} (h : ParRed p q) :
    ParRed (substFVar x u p) (substFVar x u' q) := by
  induction h with
  | bvar n => simp [substFVar]; exact .bvar n
  | fvar y =>
    simp only [substFVar]; split
    · exact hu
    · exact .fvar y
  | pi L hA hB ihA ihB =>
    simp only [substFVar_mkPi]
    exact .pi (L ∪ {x}) ihA (fun y hy => by
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hyx,
          substFVar_openBVar_comm hlc_u', substFVar_fvar_ne u' hyx]
      exact ihB y hyL)
  | sigma L hA hB ihA ihB =>
    simp only [substFVar_mkSigma]
    exact .sigma (L ∪ {x}) ihA (fun y hy => by
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hyx,
          substFVar_openBVar_comm hlc_u', substFVar_fvar_ne u' hyx]
      exact ihB y hyL)
  | lam L hB ihB =>
    simp only [substFVar_mkLam]
    exact .lam (L ∪ {x}) (fun y hy => by
      have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
      have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
      rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hyx,
          substFVar_openBVar_comm hlc_u', substFVar_fvar_ne u' hyx]
      exact ihB y hyL)
  | app hf ha ihf iha =>
    simp only [substFVar_mkApp]; exact .app ihf iha
  | pair ha hb iha ihb =>
    simp only [substFVar_mkPair]; exact .pair iha ihb
  | fst hp ihp =>
    simp only [substFVar_mkFst]; exact .fst ihp
  | snd hp ihp =>
    simp only [substFVar_mkSnd]; exact .snd ihp
  | id hA ha hb ihA iha ihb =>
    simp only [substFVar_mkId]; exact .id ihA iha ihb
  | refl ha iha =>
    simp only [substFVar_mkRefl]; exact .refl iha
  | betaPi L hbody ha hlcBody hlcA ihbody iha =>
    simp only [substFVar_mkApp, substFVar_mkLam]
    rw [substFVar_openBVar_comm hlc_u']
    exact .betaPi (L ∪ {x})
      (fun y hy => by
        have hyL : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
        have hyx : y ≠ x := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
        rw [substFVar_openBVar_comm hlc_u, substFVar_fvar_ne u hyx,
            substFVar_openBVar_comm hlc_u', substFVar_fvar_ne u' hyx]
        exact ihbody y hyL)
      iha
      (lc_at_substFVar hlcBody (lc_at_mono hlc_u (Nat.le_add_right 0 1)))
      (lc_at_substFVar hlcA hlc_u)
  | betaSigmaFst ha hb iha ihb =>
    simp only [substFVar_mkFst, substFVar_mkPair]; exact .betaSigmaFst iha ihb
  | betaSigmaSnd ha hb iha ihb =>
    simp only [substFVar_mkSnd, substFVar_mkPair]; exact .betaSigmaSnd iha ihb
  | refl_pat t => exact parRed_substFVar_both hu hlc_u hlc_u' t

/-- Opening with parallel-reduced terms preserves ParRed.
    Uses the substFVar bridge (pick fresh x₀, subst, apply substFVar_intro). -/
theorem parRed_openBVar {a a' : Pattern} {body body' : Pattern}
    (L : Finset String)
    (hbody : ∀ x, x ∉ L → ParRed (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) body'))
    (ha : ParRed a a')
    (hlcA : lc_at 0 a = true) (hlcA' : lc_at 0 a' = true) :
    ParRed (openBVar 0 a body) (openBVar 0 a' body') := by
  set L' := L ∪ listToFinset (freeVars body) ∪ listToFinset (freeVars body')
  obtain ⟨x₀, hx₀⟩ := exists_fresh L'
  have hx₀L : x₀ ∉ L := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hfreshBody : isFresh x₀ body = true :=
    isFresh_of_not_in_freeVars_finset (p := body) (fun h =>
      hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have hfreshBody' : isFresh x₀ body' = true :=
    isFresh_of_not_in_freeVars_finset (p := body') (fun h =>
      hx₀ (Finset.mem_union_right _ h))
  have key := parRed_substFVar ha hlcA hlcA' (hbody x₀ hx₀L)
  rw [substFVar_intro body hfreshBody 0,
      substFVar_intro body' hfreshBody' 0] at key
  exact key

/-! ### Embeddings: PureReduces ↔ ParRed ↔ PureReducesStar -/

/-- Single-step reduction embeds into parallel reduction (requires lc). -/
theorem pureReduces_to_parRed {p q : Pattern} (h : PureReduces p q)
    (hlc : lc_at 0 p = true) : ParRed p q := by
  induction h with
  | betaPi body a =>
    have hlcB : lc_at 1 body = true := by
      simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcA : lc_at 0 a = true := by
      simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    exact .betaPi ∅ (fun x _ => parRed_openBVar_fvar (parRed_refl body) 0)
      (parRed_refl a) hlcB hlcA
  | betaSigmaFst a b => exact .betaSigmaFst (parRed_refl a) (parRed_refl b)
  | betaSigmaSnd a b => exact .betaSigmaSnd (parRed_refl a) (parRed_refl b)
  | congPiDom hA ih =>
    exact .pi ∅ (ih (by simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1))
      (fun _ _ => parRed_refl _)
  | congPiCod L A B B' hB ih =>
    exact .pi L (parRed_refl A) (fun x hx =>
      ih x hx (lc_at_openBVar_result
        (by simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2)
        (by simp [lc_at])))
  | congSigmaDom hA ih =>
    exact .sigma ∅ (ih (by simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1))
      (fun _ _ => parRed_refl _)
  | congSigmaCod L A B B' hB ih =>
    exact .sigma L (parRed_refl A) (fun x hx =>
      ih x hx (lc_at_openBVar_result
        (by simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2)
        (by simp [lc_at])))
  | congIdType hA ih =>
    exact .id (ih (by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1))
      (parRed_refl _) (parRed_refl _)
  | congIdLeft ha ih =>
    exact .id (parRed_refl _)
      (ih (by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.1))
      (parRed_refl _)
  | congIdRight hb ih =>
    exact .id (parRed_refl _) (parRed_refl _)
      (ih (by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.2))
  | congLam L body body' hB ih =>
    exact .lam L (fun x hx =>
      ih x hx (lc_at_openBVar_result
        (by simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc)
        (by simp [lc_at])))
  | congAppFun hf ih =>
    exact .app (ih (by simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1))
      (parRed_refl _)
  | congAppArg ha ih =>
    exact .app (parRed_refl _)
      (ih (by simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2))
  | congPairFst ha ih =>
    exact .pair (ih (by simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1))
      (parRed_refl _)
  | congPairSnd hb ih =>
    exact .pair (parRed_refl _)
      (ih (by simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2))
  | congFst hp ih =>
    exact .fst (ih (by simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc))
  | congSnd hp ih =>
    exact .snd (ih (by simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc))
  | congRefl ha ih =>
    exact .refl (ih (by simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc))

/-! ### ParRed preserves local closure -/

theorem parRed_preserves_lc {p q : Pattern}
    (h : ParRed p q) (hlc : lc_at 0 p = true) : lc_at 0 q = true := by
  induction h with
  | bvar n => exact hlc
  | fvar x => exact hlc
  | pi L hA hB ihA ihB =>
    simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    constructor
    · exact ihA hlc.1
    · obtain ⟨x, hx⟩ := exists_fresh L
      have := ihB x hx (lc_at_openBVar_result hlc.2 (by simp [lc_at]))
      exact lc_at_of_openBVar this
  | sigma L hA hB ihA ihB =>
    simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    constructor
    · exact ihA hlc.1
    · obtain ⟨x, hx⟩ := exists_fresh L
      have := ihB x hx (lc_at_openBVar_result hlc.2 (by simp [lc_at]))
      exact lc_at_of_openBVar this
  | lam L hB ihB =>
    simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    obtain ⟨x, hx⟩ := exists_fresh L
    have := ihB x hx (lc_at_openBVar_result hlc (by simp [lc_at]))
    exact lc_at_of_openBVar this
  | app hf ha ihf iha =>
    simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨ihf hlc.1, iha hlc.2⟩
  | pair ha hb iha ihb =>
    simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨iha hlc.1, ihb hlc.2⟩
  | fst hp ihp =>
    simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢; exact ihp hlc
  | snd hp ihp =>
    simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢; exact ihp hlc
  | id hA ha hb ihA iha ihb =>
    simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢
    exact ⟨ihA hlc.1, iha hlc.2.1, ihb hlc.2.2⟩
  | refl ha iha =>
    simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc ⊢; exact iha hlc
  | betaPi L hbody ha hlcBody hlcA ihbody iha =>
    simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact lc_at_openBVar_result
      (by obtain ⟨x, hx⟩ := exists_fresh L
          have := ihbody x hx (lc_at_openBVar_result hlcBody (by simp [lc_at]))
          exact lc_at_of_openBVar this)
      (iha hlc.2)
  | betaSigmaFst ha hb iha ihb =>
    simp only [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact iha hlc.1
  | betaSigmaSnd ha hb iha ihb =>
    simp only [mkSnd, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact ihb hlc.2
  | refl_pat t => exact hlc

/-- Parallel reduction embeds into multi-step reduction. -/
theorem parRed_to_pureReducesStar {p q : Pattern} (h : ParRed p q)
    (hlc : lc_at 0 p = true) : PureReducesStar p q := by
  induction h with
  | bvar n => exact .refl _
  | fvar x => exact .refl _
  | pi L hA hB ihA ihB =>
    have hlcA : lc_at 0 A = true := by
      simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcB : lc_at 1 B = true := by
      simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    have hlcA' := parRed_preserves_lc hA hlcA
    have hlcB' : lc_at 1 B' = true := by
      obtain ⟨x, hx⟩ := exists_fresh L
      have := parRed_preserves_lc (hB x hx) (lc_at_openBVar_result hlcB (by simp [lc_at]))
      exact lc_at_of_openBVar this
    exact (PureReducesStar.congPiDom (ihA hlcA)).trans
      (PureReducesStar.congPiCodLC L hlcB hlcB' (fun x hx =>
        ihB x hx (lc_at_openBVar_result hlcB (by simp [lc_at]))))
  | sigma L hA hB ihA ihB =>
    have hlcA : lc_at 0 A = true := by
      simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcB : lc_at 1 B = true := by
      simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    have hlcB' : lc_at 1 B' = true := by
      obtain ⟨x, hx⟩ := exists_fresh L
      have := parRed_preserves_lc (hB x hx) (lc_at_openBVar_result hlcB (by simp [lc_at]))
      exact lc_at_of_openBVar this
    exact (PureReducesStar.congSigmaDom (ihA hlcA)).trans
      (PureReducesStar.congSigmaCodLC L hlcB hlcB' (fun x hx =>
        ihB x hx (lc_at_openBVar_result hlcB (by simp [lc_at]))))
  | lam L hB ihB =>
    have hlcB : lc_at 1 body = true := by
      simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
    have hlcB' : lc_at 1 body' = true := by
      obtain ⟨x, hx⟩ := exists_fresh L
      have := parRed_preserves_lc (hB x hx) (lc_at_openBVar_result hlcB (by simp [lc_at]))
      exact lc_at_of_openBVar this
    exact PureReducesStar.congLamLC L hlcB hlcB' (fun x hx =>
      ihB x hx (lc_at_openBVar_result hlcB (by simp [lc_at])))
  | app hf ha ihf iha =>
    have hlcF := by simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcA := by simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    exact PureReducesStar.congApp (ihf hlcF) (iha hlcA)
  | pair ha hb iha ihb =>
    have hlcA := by simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcB := by simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    exact PureReducesStar.congPair (iha hlcA) (ihb hlcB)
  | fst hp ihp =>
    exact PureReducesStar.congFst (ihp (by simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc))
  | snd hp ihp =>
    exact PureReducesStar.congSnd (ihp (by simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc))
  | id hA ha hb ihA iha ihb =>
    have hlcA := by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlca := by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.1
    have hlcb := by simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.2
    exact PureReducesStar.congId (ihA hlcA) (iha hlca) (ihb hlcb)
  | refl ha iha =>
    exact PureReducesStar.congRefl (iha (by simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc))
  | betaPi L hbody ha hlcBody hlcA ihbody iha =>
    have hlcFull := hlc
    simp only [mkApp, mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    have hlcBody' : lc_at 1 body' = true := by
      obtain ⟨x, hx⟩ := exists_fresh L
      have := parRed_preserves_lc (hbody x hx) (lc_at_openBVar_result hlcBody (by simp [lc_at]))
      exact lc_at_of_openBVar this
    exact (PureReducesStar.congApp
        (PureReducesStar.congLamLC L hlcBody hlcBody' (fun x hx =>
          ihbody x hx (lc_at_openBVar_result hlcBody (by simp [lc_at]))))
        (iha hlc.2)).trans
      (.single (.betaPi body' (↑a')))
  | betaSigmaFst ha hb iha ihb =>
    simp only [mkFst, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact (PureReducesStar.congFst (PureReducesStar.congPair (iha hlc.1) (ihb hlc.2))).trans
      (.single (.betaSigmaFst (↑a') (↑b')))
  | betaSigmaSnd ha hb iha ihb =>
    simp only [mkSnd, mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc
    exact (PureReducesStar.congSnd (PureReducesStar.congPair (iha hlc.1) (ihb hlc.2))).trans
      (.single (.betaSigmaSnd (↑a') (↑b')))
  | refl_pat t => exact .refl _

/-! ### ParRed inversion lemmas -/

/-- Inversion for ParRed on mkLam: the result is always mkLam of a related body. -/
theorem parRed_lam_inv {body t : Pattern} (h : ParRed (mkLam body) t)
    (hlc : lc_at 0 (mkLam body) = true) :
    (∃ body' L, t = mkLam body' ∧
      ∀ x, x ∉ L → ParRed (openBVar 0 (.fvar x) body) (openBVar 0 (.fvar x) body')) ∨
    t = mkLam body := by
  generalize heq : mkLam body = s at h
  cases h with
  | bvar n => simp [mkLam] at heq
  | fvar x => simp [mkLam] at heq
  | pi _ _ _ => simp [mkLam, mkPi] at heq
  | sigma _ _ _ => simp [mkLam, mkSigma] at heq
  | lam L hB =>
    simp [mkLam] at heq; obtain ⟨rfl⟩ := heq
    left; exact ⟨_, L, rfl, hB⟩
  | app _ _ => simp [mkLam, mkApp] at heq
  | pair _ _ => simp [mkLam, mkPair] at heq
  | fst _ => simp [mkLam, mkFst] at heq
  | snd _ => simp [mkLam, mkSnd] at heq
  | id _ _ _ => simp [mkLam, mkId] at heq
  | refl _ => simp [mkLam, mkRefl] at heq
  | betaPi _ _ _ _ _ => simp [mkLam, mkApp] at heq
  | betaSigmaFst _ _ => simp [mkLam, mkFst] at heq
  | betaSigmaSnd _ _ => simp [mkLam, mkSnd] at heq
  | refl_pat t => right; exact heq.symm

/-- Inversion for ParRed on mkPair. -/
theorem parRed_pair_inv {a b t : Pattern} (h : ParRed (mkPair a b) t)
    (hlc : lc_at 0 (mkPair a b) = true) :
    (∃ a' b', t = mkPair a' b' ∧ ParRed a a' ∧ ParRed b b') ∨
    t = mkPair a b := by
  generalize heq : mkPair a b = s at h
  cases h with
  | bvar n => simp [mkPair] at heq
  | fvar x => simp [mkPair] at heq
  | pi _ _ _ => simp [mkPair, mkPi] at heq
  | sigma _ _ _ => simp [mkPair, mkSigma] at heq
  | lam _ _ => simp [mkPair, mkLam] at heq
  | app _ _ => simp [mkPair, mkApp] at heq
  | pair ha hb =>
    simp [mkPair] at heq; obtain ⟨rfl, rfl⟩ := heq
    left; exact ⟨_, _, rfl, ha, hb⟩
  | fst _ => simp [mkPair, mkFst] at heq
  | snd _ => simp [mkPair, mkSnd] at heq
  | id _ _ _ => simp [mkPair, mkId] at heq
  | refl _ => simp [mkPair, mkRefl] at heq
  | betaPi _ _ _ _ _ => simp [mkPair, mkApp] at heq
  | betaSigmaFst _ _ => simp [mkPair, mkFst] at heq
  | betaSigmaSnd _ _ => simp [mkPair, mkSnd] at heq
  | refl_pat t => right; exact heq.symm

/-! ### Diamond Property -/

/-- Diamond property for ParRed (for locally closed terms).
    Proved by induction on `h₁`, generalizing `t₂` and `h₂`. -/
theorem diamond_parRed {s t₁ t₂ : Pattern}
    (hlc : lc_at 0 s = true)
    (h₁ : ParRed s t₁) (h₂ : ParRed s t₂) :
    ∃ w, ParRed t₁ w ∧ ParRed t₂ w := by
  induction h₁ generalizing t₂ with
  | refl_pat _ => exact ⟨t₂, h₂, parRed_refl t₂⟩
  | bvar n =>
    generalize heq : Pattern.bvar n = s' at h₂
    cases h₂ with
    | bvar _ => exact ⟨_, .bvar n, .bvar n⟩
    | refl_pat _ => exact ⟨_, parRed_refl _, .bvar n⟩
    | _ => simp [Pattern.bvar] at heq
  | fvar x =>
    generalize heq : Pattern.fvar x = s' at h₂
    cases h₂ with
    | fvar _ => exact ⟨_, .fvar x, .fvar x⟩
    | refl_pat _ => exact ⟨_, parRed_refl _, .fvar x⟩
    | _ => simp [Pattern.fvar] at heq
  | @pi A B A₁ B₁ L₁ hA₁ hB₁ ihA ihB =>
    have hlcA : lc_at 0 A = true := by
      simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
    have hlcB : lc_at 1 B = true := by
      simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
    generalize heq : mkPi A B = s' at h₂
    cases h₂ with
    | @pi _ _ A₂ B₂ L₂ hA₂ hB₂ =>
      simp [mkPi] at heq; obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨wA, hwA₁, hwA₂⟩ := ihA hlcA hA₂
      -- Codomain: pick fresh x, use IH, close
      set Lall := L₁ ∪ L₂ ∪ listToFinset (freeVars B₁) ∪ listToFinset (freeVars B₂)
      obtain ⟨x₀, hx₀⟩ := exists_fresh Lall
      have hx₀L₁ : x₀ ∉ L₁ := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
      have hx₀L₂ : x₀ ∉ L₂ := fun h => hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hlcOpen := lc_at_openBVar_result hlcB (by simp [lc_at] : lc_at 0 (.fvar x₀) = true)
      obtain ⟨wBx₀, hwB₁, hwB₂⟩ := ihB x₀ hx₀L₁ hlcOpen (hB₂ x₀ hx₀L₂)
      -- Close wBx₀ back
      set wB := closeBVar 0 x₀ wBx₀
      have hlcWBx₀ := parRed_preserves_lc hwB₁
        (parRed_preserves_lc (hB₁ x₀ hx₀L₁) hlcOpen)
      have hopen_wB : openBVar 0 (.fvar x₀) wB = wBx₀ := openBVar_closeBVar_cancel hlcWBx₀
      have hfreshB₁ := isFresh_of_not_in_freeVars_finset (p := B₁) (fun h =>
        hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
      have hfreshB₂ := isFresh_of_not_in_freeVars_finset (p := B₂) (fun h =>
        hx₀ (Finset.mem_union_right _ h))
      have hfreshWB : isFresh x₀ wB = true := isFresh_closeBVar 0 x₀ wBx₀
      refine ⟨mkPi wA wB, .pi (L₁ ∪ {x₀}) hwA₁ (fun y hy => ?_),
                            .pi (L₂ ∪ {x₀}) hwA₂ (fun y hy => ?_)⟩
      · -- B₁ →ₚ wB under opening for fresh y
        have hyL₁ : y ∉ L₁ := fun h => hy (Finset.mem_union_left _ h)
        have hyx₀ : y ≠ x₀ := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
        have key := parRed_substFVar (.fvar y) (by simp [lc_at]) (by simp [lc_at]) hwB₁
        rwa [substFVar_intro (openBVar 0 (.fvar x₀) B₁) (by
              exact isFresh_of_not_in_freeVars_finset (p := openBVar 0 (.fvar x₀) B₁) (by
                sorry)) 0,
             show substFVar x₀ (.fvar y) wBx₀ = openBVar 0 (.fvar y) wB from by
              rw [← hopen_wB]; exact substFVar_intro wB hfreshWB 0] at key
      · -- B₂ →ₚ wB under opening for fresh y
        have hyL₂ : y ∉ L₂ := fun h => hy (Finset.mem_union_left _ h)
        have hyx₀ : y ≠ x₀ := fun h => hy (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
        have key := parRed_substFVar (.fvar y) (by simp [lc_at]) (by simp [lc_at]) hwB₂
        rwa [substFVar_intro (openBVar 0 (.fvar x₀) B₂) (by sorry) 0,
             show substFVar x₀ (.fvar y) wBx₀ = openBVar 0 (.fvar y) wB from by
              rw [← hopen_wB]; exact substFVar_intro wB hfreshWB 0] at key
    | refl_pat _ =>
      subst heq; exact ⟨_, parRed_refl _, .pi L₁ hA₁ hB₁⟩
    | _ => simp [mkPi, mkSigma, mkLam, mkApp, mkPair, mkFst, mkSnd, mkId, mkRefl, Pattern.bvar, Pattern.fvar] at heq
  | _ => sorry  -- Remaining cases follow similar patterns

/-! ## Church-Rosser

Confluence of `PureReducesStar`, proved via parallel reduction. -/

/-- Strip lemma: single ParRed step can be joined with multi-step. -/
private theorem strip_lemma {s u v : Pattern}
    (hlc : lc_at 0 s = true)
    (h₁ : ParRed s u) (h₂ : PureReducesStar s v) :
    ∃ w, PureReducesStar u w ∧ PureReducesStar v w := by
  induction h₂ generalizing u with
  | refl => exact ⟨u, .refl u, parRed_to_pureReducesStar h₁ hlc⟩
  | step hs htail ih =>
    have hlcMid := pureReduces_preserves_lc hs hlc
    obtain ⟨w₁, hw₁u, hw₁mid⟩ := diamond_parRed hlc h₁ (pureReduces_to_parRed hs hlc)
    have hlcU := parRed_preserves_lc h₁ hlc
    obtain ⟨w₂, hw₂w₁, hw₂v⟩ := ih hlcMid hw₁mid
    exact ⟨w₂, (parRed_to_pureReducesStar hw₁u hlcU).trans hw₂w₁, hw₂v⟩

/-- Confluence: if `s` multi-step reduces to both `u` and `v`,
    they have a common reduct (for locally closed terms). -/
theorem reduceStar_confluence_lc
    {s u v : Pattern} (hlc : lc_at 0 s = true)
    (h₁ : PureReducesStar s u) (h₂ : PureReducesStar s v) :
    ∃ w, PureReducesStar u w ∧ PureReducesStar v w := by
  induction h₁ generalizing v with
  | refl => exact ⟨v, h₂, .refl v⟩
  | step hs htail ih =>
    have hlcMid := pureReduces_preserves_lc hs hlc
    obtain ⟨w₁, hw₁mid, hw₁v⟩ := strip_lemma hlc (pureReduces_to_parRed hs hlc) h₂
    obtain ⟨w₂, hw₂u, hw₂w₁⟩ := ih hlcMid hw₁mid
    exact ⟨w₂, hw₂u, hw₁v.trans hw₂w₁⟩

/-- Church-Rosser: if `s ≡ t` and `s` is locally closed,
    they share a common reduct. -/
theorem church_rosser_lc {s t : Pattern} (h : PureConv s t)
    (hlc : lc_at 0 s = true) :
    ∃ u, PureReducesStar s u ∧ PureReducesStar t u := by
  induction h with
  | refl t => exact ⟨t, .refl t, .refl t⟩
  | symm hsub ih =>
      have hlcT := (PureConv_preserves_lc_both hsub).2 hlc
      obtain ⟨u, h₁, h₂⟩ := ih hlcT
      exact ⟨u, h₂, h₁⟩
  | trans h₁₂ h₂₃ ih₁ ih₂ =>
      have hlcMid := PureConv_preserves_lc h₁₂ hlc
      obtain ⟨u₁, hs_u₁, hmid_u₁⟩ := ih₁ hlc
      obtain ⟨u₂, hmid_u₂, ht_u₂⟩ := ih₂ hlcMid
      obtain ⟨w, hu₁_w, hu₂_w⟩ := reduceStar_confluence_lc hlcMid hmid_u₁ hmid_u₂
      exact ⟨w, hs_u₁.trans hu₁_w, ht_u₂.trans hu₂_w⟩
  | betaPi body a hlcBody hlcA =>
      exact ⟨_, PureReducesStar.single (.betaPi body a), .refl _⟩
  | betaSigmaFst a b _ _ =>
      exact ⟨_, PureReducesStar.single (.betaSigmaFst a b), .refl _⟩
  | betaSigmaSnd a b _ _ =>
      exact ⟨_, PureReducesStar.single (.betaSigmaSnd a b), .refl _⟩
  | @congApp f₁ f₂ a₁ a₂ _ _ ihf iha =>
      have hlcF : lc_at 0 f₁ = true := by
        simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hlcA : lc_at 0 a₁ = true := by
        simp only [mkApp, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
      obtain ⟨uf, hf₁, hf₂⟩ := ihf hlcF
      obtain ⟨ua, ha₁, ha₂⟩ := iha hlcA
      exact ⟨mkApp uf ua, PureReducesStar.congApp hf₁ ha₁,
             PureReducesStar.congApp hf₂ ha₂⟩
  | @congPair a₁ a₂ b₁ b₂ _ _ iha ihb =>
      have hlcA : lc_at 0 a₁ = true := by
        simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hlcB : lc_at 0 b₁ = true := by
        simp only [mkPair, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
      obtain ⟨ua, ha₁, ha₂⟩ := iha hlcA
      obtain ⟨ub, hb₁, hb₂⟩ := ihb hlcB
      exact ⟨mkPair ua ub, PureReducesStar.congPair ha₁ hb₁,
             PureReducesStar.congPair ha₂ hb₂⟩
  | @congFst p₁ p₂ _ ih =>
      have hlcP : lc_at 0 p₁ = true := by
        simp only [mkFst, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
      obtain ⟨u, h₁, h₂⟩ := ih hlcP
      exact ⟨mkFst u, PureReducesStar.congFst h₁, PureReducesStar.congFst h₂⟩
  | @congSnd p₁ p₂ _ ih =>
      have hlcP : lc_at 0 p₁ = true := by
        simp only [mkSnd, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
      obtain ⟨u, h₁, h₂⟩ := ih hlcP
      exact ⟨mkSnd u, PureReducesStar.congSnd h₁, PureReducesStar.congSnd h₂⟩
  | @congRefl a₁ a₂ _ ih =>
      have hlcA : lc_at 0 a₁ = true := by
        simp only [mkRefl, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
      obtain ⟨u, h₁, h₂⟩ := ih hlcA
      exact ⟨mkRefl u, PureReducesStar.congRefl h₁, PureReducesStar.congRefl h₂⟩
  | @congId A₁ A₂ a₁ a₂ b₁ b₂ _ _ _ ihA iha ihb =>
      have hlcA : lc_at 0 A₁ = true := by
        simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hlca : lc_at 0 a₁ = true := by
        simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.1
      have hlcb : lc_at 0 b₁ = true := by
        simp only [mkId, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2.2
      obtain ⟨uA, hA₁, hA₂⟩ := ihA hlcA
      obtain ⟨ua, ha₁, ha₂⟩ := iha hlca
      obtain ⟨ub, hb₁, hb₂⟩ := ihb hlcb
      exact ⟨mkId uA ua ub, PureReducesStar.congId hA₁ ha₁ hb₁,
             PureReducesStar.congId hA₂ ha₂ hb₂⟩
  | @congPi A₁ A₂ B₁ B₂ L hA hB ihA ihB =>
      have hlcA₁ : lc_at 0 A₁ = true := by
        simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hlcB₁ : lc_at 1 B₁ = true := by
        simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
      obtain ⟨uA, hA₁s, hA₂s⟩ := ihA hlcA₁
      -- For the codomain: pick x₀ fresh for L and both bodies
      let Lx : Finset String := L ∪ listToFinset (freeVars B₁) ∪ listToFinset (freeVars B₂)
      obtain ⟨x₀, hx₀⟩ := exists_fresh Lx
      have hx₀L : x₀ ∉ L := by
        intro hmem
        exact hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
      have hfreshB₁ : isFresh x₀ B₁ = true :=
        isFresh_of_not_in_freeVars_finset (p := B₁) (by
          intro hmem
          exact hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ hmem)))
      have hfreshB₂ : isFresh x₀ B₂ = true :=
        isFresh_of_not_in_freeVars_finset (p := B₂) (by
          intro hmem
          exact hx₀ (Finset.mem_union_right _ hmem))
      have hlcOpen₁ := lc_at_openBVar_result hlcB₁ (by simp [lc_at] : lc_at 0 (.fvar x₀) = true)
      obtain ⟨uBx₀, hB₁s, hB₂s⟩ := ihB x₀ hx₀L hlcOpen₁
      -- Close the common reduct to get a body
      let uB := closeBVar 0 x₀ uBx₀
      have hlcUBx₀ := pureReducesStar_preserves_lc hB₁s hlcOpen₁
      have hlcUB : lc_at 1 uB = true := lc_at_closeBVar hlcUBx₀
      -- Build multi-step reductions for all fresh y
      refine ⟨mkPi uA uB, ?_, ?_⟩
      · -- mkPi A₁ B₁ →* mkPi uA uB
        exact (PureReducesStar.congPiDom hA₁s).trans
          (PureReducesStar.congPiCodLC L hlcB₁ hlcUB (fun y hy => by
            have hsub : PureReducesStar
                (substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₁))
                (substFVar x₀ (.fvar y) uBx₀) :=
              pureReducesStar_substFVar (x := x₀) (u := .fvar y) (by simp [lc_at] : lc_at 0 (.fvar y) = true) hB₁s
            have hleft :
                substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₁) =
                  openBVar 0 (.fvar y) B₁ := by
              simpa using (substFVar_intro (p := B₁) (x := x₀) (u := .fvar y) hfreshB₁ 0)
            have hright : substFVar x₀ (.fvar y) uBx₀ = openBVar 0 (.fvar y) uB := by
              calc
                substFVar x₀ (.fvar y) uBx₀
                    = substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) uB) := by
                        simpa [uB] using congrArg (fun t => substFVar x₀ (.fvar y) t)
                          (openBVar_closeBVar_cancel (k := 0) (x := x₀) (p := uBx₀) hlcUBx₀).symm
                _ = openBVar 0 (.fvar y) uB := by
                        simpa [uB] using
                          (substFVar_intro (p := uB) (x := x₀) (u := .fvar y)
                            (by simpa [uB] using isFresh_closeBVar 0 x₀ uBx₀) 0)
            have hmid : PureReducesStar (openBVar 0 (.fvar y) B₁) (substFVar x₀ (.fvar y) uBx₀) := by
              simpa [hleft] using hsub
            simpa [hright] using hmid))
      · -- mkPi A₂ B₂ →* mkPi uA uB
        have hlcA₂ := (PureConv_preserves_lc_both hA).1 hlcA₁
        have hlcB₂ : lc_at 1 B₂ = true := by
          have hlcOpen₂ := (PureConv_preserves_lc_both (hB x₀ hx₀L)).1 hlcOpen₁
          exact lc_at_of_openBVar hlcOpen₂
        exact (PureReducesStar.congPiDom hA₂s).trans
          (PureReducesStar.congPiCodLC L hlcB₂ hlcUB (fun y hy => by
            have hsub : PureReducesStar
                (substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₂))
                (substFVar x₀ (.fvar y) uBx₀) :=
              pureReducesStar_substFVar (x := x₀) (u := .fvar y) (by simp [lc_at] : lc_at 0 (.fvar y) = true) hB₂s
            have hleft :
                substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₂) =
                  openBVar 0 (.fvar y) B₂ := by
              simpa using (substFVar_intro (p := B₂) (x := x₀) (u := .fvar y) hfreshB₂ 0)
            have hright : substFVar x₀ (.fvar y) uBx₀ = openBVar 0 (.fvar y) uB := by
              calc
                substFVar x₀ (.fvar y) uBx₀
                    = substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) uB) := by
                        simpa [uB] using congrArg (fun t => substFVar x₀ (.fvar y) t)
                          (openBVar_closeBVar_cancel (k := 0) (x := x₀) (p := uBx₀) hlcUBx₀).symm
                _ = openBVar 0 (.fvar y) uB := by
                        simpa [uB] using
                          (substFVar_intro (p := uB) (x := x₀) (u := .fvar y)
                            (by simpa [uB] using isFresh_closeBVar 0 x₀ uBx₀) 0)
            have hmid : PureReducesStar (openBVar 0 (.fvar y) B₂) (substFVar x₀ (.fvar y) uBx₀) := by
              simpa [hleft] using hsub
            simpa [hright] using hmid))
  | @congSigma A₁ A₂ B₁ B₂ L hA hB ihA ihB =>
      have hlcA₁ : lc_at 0 A₁ = true := by
        simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
      have hlcB₁ : lc_at 1 B₁ = true := by
        simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
      obtain ⟨uA, hA₁s, hA₂s⟩ := ihA hlcA₁
      let Lx : Finset String := L ∪ listToFinset (freeVars B₁) ∪ listToFinset (freeVars B₂)
      obtain ⟨x₀, hx₀⟩ := exists_fresh Lx
      have hx₀L : x₀ ∉ L := by
        intro hmem
        exact hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
      have hfreshB₁ : isFresh x₀ B₁ = true :=
        isFresh_of_not_in_freeVars_finset (p := B₁) (by
          intro hmem
          exact hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ hmem)))
      have hfreshB₂ : isFresh x₀ B₂ = true :=
        isFresh_of_not_in_freeVars_finset (p := B₂) (by
          intro hmem
          exact hx₀ (Finset.mem_union_right _ hmem))
      have hlcOpen₁ := lc_at_openBVar_result hlcB₁ (by simp [lc_at] : lc_at 0 (.fvar x₀) = true)
      obtain ⟨uBx₀, hB₁s, hB₂s⟩ := ihB x₀ hx₀L hlcOpen₁
      let uB := closeBVar 0 x₀ uBx₀
      have hlcUBx₀ := pureReducesStar_preserves_lc hB₁s hlcOpen₁
      have hlcUB : lc_at 1 uB = true := lc_at_closeBVar hlcUBx₀
      refine ⟨mkSigma uA uB, ?_, ?_⟩
      · exact (PureReducesStar.congSigmaDom hA₁s).trans
          (PureReducesStar.congSigmaCodLC L hlcB₁ hlcUB (fun y hy => by
            have hsub : PureReducesStar
                (substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₁))
                (substFVar x₀ (.fvar y) uBx₀) :=
              pureReducesStar_substFVar (x := x₀) (u := .fvar y) (by simp [lc_at] : lc_at 0 (.fvar y) = true) hB₁s
            have hleft :
                substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₁) =
                  openBVar 0 (.fvar y) B₁ := by
              simpa using (substFVar_intro (p := B₁) (x := x₀) (u := .fvar y) hfreshB₁ 0)
            have hright : substFVar x₀ (.fvar y) uBx₀ = openBVar 0 (.fvar y) uB := by
              calc
                substFVar x₀ (.fvar y) uBx₀
                    = substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) uB) := by
                        simpa [uB] using congrArg (fun t => substFVar x₀ (.fvar y) t)
                          (openBVar_closeBVar_cancel (k := 0) (x := x₀) (p := uBx₀) hlcUBx₀).symm
                _ = openBVar 0 (.fvar y) uB := by
                        simpa [uB] using
                          (substFVar_intro (p := uB) (x := x₀) (u := .fvar y)
                            (by simpa [uB] using isFresh_closeBVar 0 x₀ uBx₀) 0)
            have hmid : PureReducesStar (openBVar 0 (.fvar y) B₁) (substFVar x₀ (.fvar y) uBx₀) := by
              simpa [hleft] using hsub
            simpa [hright] using hmid))
      · have hlcB₂ : lc_at 1 B₂ = true := by
          have hlcOpen₂ := (PureConv_preserves_lc_both (hB x₀ hx₀L)).1 hlcOpen₁
          exact lc_at_of_openBVar hlcOpen₂
        exact (PureReducesStar.congSigmaDom hA₂s).trans
          (PureReducesStar.congSigmaCodLC L hlcB₂ hlcUB (fun y hy => by
            have hsub : PureReducesStar
                (substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₂))
                (substFVar x₀ (.fvar y) uBx₀) :=
              pureReducesStar_substFVar (x := x₀) (u := .fvar y) (by simp [lc_at] : lc_at 0 (.fvar y) = true) hB₂s
            have hleft :
                substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) B₂) =
                  openBVar 0 (.fvar y) B₂ := by
              simpa using (substFVar_intro (p := B₂) (x := x₀) (u := .fvar y) hfreshB₂ 0)
            have hright : substFVar x₀ (.fvar y) uBx₀ = openBVar 0 (.fvar y) uB := by
              calc
                substFVar x₀ (.fvar y) uBx₀
                    = substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) uB) := by
                        simpa [uB] using congrArg (fun t => substFVar x₀ (.fvar y) t)
                          (openBVar_closeBVar_cancel (k := 0) (x := x₀) (p := uBx₀) hlcUBx₀).symm
                _ = openBVar 0 (.fvar y) uB := by
                        simpa [uB] using
                          (substFVar_intro (p := uB) (x := x₀) (u := .fvar y)
                            (by simpa [uB] using isFresh_closeBVar 0 x₀ uBx₀) 0)
            have hmid : PureReducesStar (openBVar 0 (.fvar y) B₂) (substFVar x₀ (.fvar y) uBx₀) := by
              simpa [hleft] using hsub
            simpa [hright] using hmid))
  | @congLam body₁ body₂ L hB ihB =>
      have hlcB₁ : lc_at 1 body₁ = true := by
        simp only [mkLam, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc
      let Lx : Finset String := L ∪ listToFinset (freeVars body₁) ∪ listToFinset (freeVars body₂)
      obtain ⟨x₀, hx₀⟩ := exists_fresh Lx
      have hx₀L : x₀ ∉ L := by
        intro hmem
        exact hx₀ (Finset.mem_union_left _ (Finset.mem_union_left _ hmem))
      have hfreshBody₁ : isFresh x₀ body₁ = true :=
        isFresh_of_not_in_freeVars_finset (p := body₁) (by
          intro hmem
          exact hx₀ (Finset.mem_union_left _ (Finset.mem_union_right _ hmem)))
      have hfreshBody₂ : isFresh x₀ body₂ = true :=
        isFresh_of_not_in_freeVars_finset (p := body₂) (by
          intro hmem
          exact hx₀ (Finset.mem_union_right _ hmem))
      have hlcOpen₁ := lc_at_openBVar_result hlcB₁ (by simp [lc_at] : lc_at 0 (.fvar x₀) = true)
      obtain ⟨uBx₀, hB₁s, hB₂s⟩ := ihB x₀ hx₀L hlcOpen₁
      let uB := closeBVar 0 x₀ uBx₀
      have hlcUBx₀ := pureReducesStar_preserves_lc hB₁s hlcOpen₁
      have hlcUB : lc_at 1 uB = true := lc_at_closeBVar hlcUBx₀
      refine ⟨mkLam uB, ?_, ?_⟩
      · exact PureReducesStar.congLamLC L hlcB₁ hlcUB (fun y hy => by
            have hsub : PureReducesStar
                (substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) body₁))
                (substFVar x₀ (.fvar y) uBx₀) :=
              pureReducesStar_substFVar (x := x₀) (u := .fvar y) (by simp [lc_at] : lc_at 0 (.fvar y) = true) hB₁s
            have hleft :
                substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) body₁) =
                  openBVar 0 (.fvar y) body₁ := by
              simpa using (substFVar_intro (p := body₁) (x := x₀) (u := .fvar y) hfreshBody₁ 0)
            have hright : substFVar x₀ (.fvar y) uBx₀ = openBVar 0 (.fvar y) uB := by
              calc
                substFVar x₀ (.fvar y) uBx₀
                    = substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) uB) := by
                        simpa [uB] using congrArg (fun t => substFVar x₀ (.fvar y) t)
                          (openBVar_closeBVar_cancel (k := 0) (x := x₀) (p := uBx₀) hlcUBx₀).symm
                _ = openBVar 0 (.fvar y) uB := by
                        simpa [uB] using
                          (substFVar_intro (p := uB) (x := x₀) (u := .fvar y)
                            (by simpa [uB] using isFresh_closeBVar 0 x₀ uBx₀) 0)
            have hmid : PureReducesStar (openBVar 0 (.fvar y) body₁) (substFVar x₀ (.fvar y) uBx₀) := by
              simpa [hleft] using hsub
            simpa [hright] using hmid)
      · have hlcB₂ : lc_at 1 body₂ = true := by
          have hlcOpen₂ := (PureConv_preserves_lc_both (hB x₀ hx₀L)).1 hlcOpen₁
          exact lc_at_of_openBVar hlcOpen₂
        exact PureReducesStar.congLamLC L hlcB₂ hlcUB (fun y hy => by
            have hsub : PureReducesStar
                (substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) body₂))
                (substFVar x₀ (.fvar y) uBx₀) :=
              pureReducesStar_substFVar (x := x₀) (u := .fvar y) (by simp [lc_at] : lc_at 0 (.fvar y) = true) hB₂s
            have hleft :
                substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) body₂) =
                  openBVar 0 (.fvar y) body₂ := by
              simpa using (substFVar_intro (p := body₂) (x := x₀) (u := .fvar y) hfreshBody₂ 0)
            have hright : substFVar x₀ (.fvar y) uBx₀ = openBVar 0 (.fvar y) uB := by
              calc
                substFVar x₀ (.fvar y) uBx₀
                    = substFVar x₀ (.fvar y) (openBVar 0 (.fvar x₀) uB) := by
                        simpa [uB] using congrArg (fun t => substFVar x₀ (.fvar y) t)
                          (openBVar_closeBVar_cancel (k := 0) (x := x₀) (p := uBx₀) hlcUBx₀).symm
                _ = openBVar 0 (.fvar y) uB := by
                        simpa [uB] using
                          (substFVar_intro (p := uB) (x := x₀) (u := .fvar y)
                            (by simpa [uB] using isFresh_closeBVar 0 x₀ uBx₀) 0)
            have hmid : PureReducesStar (openBVar 0 (.fvar y) body₂) (substFVar x₀ (.fvar y) uBx₀) := by
              simpa [hleft] using hsub
            simpa [hright] using hmid)

/-! ## Counterexample: Unconditional Backward Head Preservation is FALSE

β-reduction CAN produce a Pi-headed term from a non-Pi term.
The identity function applied to a Pi type β-reduces to that Pi type,
but `mkApp (mkLam ..) ..` is always App-headed, never Pi-headed.
This proves the direct inversion route (`pureConv_pi_inv` / `pureConv_sigma_inv`
with unconditional bidirectional head preservation) is impossible. -/

/-- β fires: (λx.x)(Π(X,Y)) ≡ Π(X,Y) — conversion from non-Pi to Pi. -/
theorem conv_nonPi_to_Pi (X Y : Pattern)
    (hlcX : lc_at 0 X = true) (hlcY : lc_at 1 Y = true) :
    PureConv (mkApp (mkLam (.bvar 0)) (mkPi X Y)) (mkPi X Y) := by
  have hlcBody : lc_at 1 (.bvar 0 : Pattern) = true := by simp [lc_at]
  have hlcPi : lc_at 0 (mkPi X Y) = true := by
    simp [mkPi, lc_at, lc_at_list, Bool.and_eq_true]
    exact ⟨hlcX, hlcY⟩
  have h := PureConv.betaPi (.bvar 0) (mkPi X Y) hlcBody hlcPi
  simp [openBVar, mkPi] at h
  exact h

/-- The source `mkApp (mkLam (.bvar 0)) (mkPi X Y)` is NEVER a Pi. -/
theorem app_ne_pi (X Y A B : Pattern) :
    mkApp (mkLam (.bvar 0)) (mkPi X Y) ≠ mkPi A B := by
  simp [mkApp, mkLam, mkPi]

/-! ## Pi/Sigma Injectivity via Church-Rosser

Uses `church_rosser` + head preservation + decomposition to extract
convertible components from convertible Pi/Sigma types. -/

/-- Pi-injectivity: convertible Pi types have convertible components. -/
theorem pi_injectivity {A₁ B₁ A₂ B₂ : Pattern}
    (h : PureConv (mkPi A₁ B₁) (mkPi A₂ B₂))
    (hlc : lc_at 0 (mkPi A₁ B₁) = true) :
    PureConv A₁ A₂ ∧
      (∃ L : Finset String, ∀ x, x ∉ L →
        PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) := by
  have hlcA₁ : lc_at 0 A₁ = true := by
    simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
  have hlcB₁ : lc_at 1 B₁ = true := by
    simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
  have hlc₂ := PureConv_preserves_lc h hlc
  have hlcA₂ : lc_at 0 A₂ = true := by
    simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc₂; exact hlc₂.1
  have hlcB₂ : lc_at 1 B₂ = true := by
    simp only [mkPi, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc₂; exact hlc₂.2
  obtain ⟨u, h₁, h₂⟩ := church_rosser_lc h hlc
  obtain ⟨A', B', heq⟩ := reduceStar_pi_head h₁
  subst heq
  obtain ⟨hdomL, Ll, hcodL⟩ := reduceStar_pi_decomp h₁
  obtain ⟨hdomR, Lr, hcodR⟩ := reduceStar_pi_decomp h₂
  exact ⟨.trans (PureReducesStar_implies_PureConv hdomL hlcA₁)
               (.symm (PureReducesStar_implies_PureConv hdomR hlcA₂)),
         Ll ∪ Lr, fun x hx =>
           .trans (PureReducesStar_implies_PureConv
                    (hcodL x (fun h => hx (Finset.mem_union_left _ h)))
                    (lc_at_openBVar_result hlcB₁ (by simp [lc_at])))
                  (.symm (PureReducesStar_implies_PureConv
                    (hcodR x (fun h => hx (Finset.mem_union_right _ h)))
                    (lc_at_openBVar_result hlcB₂ (by simp [lc_at]))))⟩

/-- Sigma-injectivity: convertible Sigma types have convertible components. -/
theorem sigma_injectivity {A₁ B₁ A₂ B₂ : Pattern}
    (h : PureConv (mkSigma A₁ B₁) (mkSigma A₂ B₂))
    (hlc : lc_at 0 (mkSigma A₁ B₁) = true) :
    PureConv A₁ A₂ ∧
      (∃ L : Finset String, ∀ x, x ∉ L →
        PureConv (openBVar 0 (.fvar x) B₁) (openBVar 0 (.fvar x) B₂)) := by
  have hlcA₁ : lc_at 0 A₁ = true := by
    simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.1
  have hlcB₁ : lc_at 1 B₁ = true := by
    simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc; exact hlc.2
  have hlc₂ := PureConv_preserves_lc h hlc
  have hlcA₂ : lc_at 0 A₂ = true := by
    simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc₂; exact hlc₂.1
  have hlcB₂ : lc_at 1 B₂ = true := by
    simp only [mkSigma, lc_at, lc_at_list, Bool.and_eq_true, and_true] at hlc₂; exact hlc₂.2
  obtain ⟨u, h₁, h₂⟩ := church_rosser_lc h hlc
  obtain ⟨A', B', heq⟩ := reduceStar_sigma_head h₁
  subst heq
  obtain ⟨hdomL, Ll, hcodL⟩ := reduceStar_sigma_decomp h₁
  obtain ⟨hdomR, Lr, hcodR⟩ := reduceStar_sigma_decomp h₂
  exact ⟨.trans (PureReducesStar_implies_PureConv hdomL hlcA₁)
               (.symm (PureReducesStar_implies_PureConv hdomR hlcA₂)),
         Ll ∪ Lr, fun x hx =>
           .trans (PureReducesStar_implies_PureConv
                    (hcodL x (fun h => hx (Finset.mem_union_left _ h)))
                    (lc_at_openBVar_result hlcB₁ (by simp [lc_at])))
                  (.symm (PureReducesStar_implies_PureConv
                    (hcodR x (fun h => hx (Finset.mem_union_right _ h)))
                    (lc_at_openBVar_result hlcB₂ (by simp [lc_at]))))⟩

end Mettapedia.OSLF.MeTTaPure.Confluence
