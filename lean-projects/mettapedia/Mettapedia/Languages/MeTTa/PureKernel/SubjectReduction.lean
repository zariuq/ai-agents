import Mettapedia.Languages.MeTTa.PureKernel.Confluence

namespace Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Parallel
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.Confluence

private theorem subst0_wk_cancel (a t : PureTm n) :
    subst (subst0 a) (rename wk t) = t := by
  calc
    subst (subst0 a) (rename wk t)
        = subst (fun i => subst0 a (wk i)) t := by
            simpa using (subst_rename (σ := subst0 a) (ρ := wk) (t := t))
    _ = subst ids t := by
          apply subst_ext
          intro i
          rfl
    _ = t := by
          exact subst_ids (t := t)

private theorem inst0_rename_wk_app_zero (motive a : PureTm n) :
    subst (subst0 a) (.app (rename wk motive) (.var 0)) = .app motive a := by
  calc
    subst (subst0 a) (.app (rename wk motive) (.var 0))
        = .app (subst (subst0 a) (rename wk motive)) (subst (subst0 a) (.var 0)) := by
            rfl
    _ = .app motive a := by
          simp [subst0_wk_cancel]

private theorem natRecSuccCodomain_inst0
    (motive k rec : PureTm n) :
    inst0 rec
      (subst (liftSub (subst0 k))
        (.app (rename wk (rename wk motive)) (.natSucc (.var 1)))) =
      .app motive (.natSucc k) := by
  calc
    inst0 rec
        (subst (liftSub (subst0 k))
          (.app (rename wk (rename wk motive)) (.natSucc (.var 1))))
        =
          subst (subst0 rec)
            (.app (subst (liftSub (subst0 k)) (rename wk (rename wk motive)))
              (.natSucc (subst (liftSub (subst0 k)) (.var 1)))) := by
                rfl
    _ = subst (subst0 rec) (.app (rename wk motive) (.natSucc (rename wk k))) := by
          have hFun :
              subst (liftSub (subst0 k)) (rename wk (rename wk motive)) = rename wk motive := by
            calc
              subst (liftSub (subst0 k)) (rename wk (rename wk motive))
                  = rename wk (subst (subst0 k) (rename wk motive)) := by
                      simpa using (subst_liftSub_wk (σ := subst0 k) (t := rename wk motive))
              _ = rename wk motive := by
                    simp [subst0_wk_cancel]
          have hArg : subst (liftSub (subst0 k)) (.var 1) = rename wk k := by
            show liftSub (subst0 k) (Fin.succ 0) = rename wk k
            rfl
          have hInner :
              PureTm.app (subst (liftSub (subst0 k)) (rename wk (rename wk motive)))
                (.natSucc (subst (liftSub (subst0 k)) (.var 1))) =
              PureTm.app (rename wk motive) (.natSucc (rename wk k)) := by
            rw [hFun, hArg]
          exact congrArg (subst (subst0 rec)) hInner
    _ = .app motive (.natSucc k) := by
          calc
            subst (subst0 rec) ((rename wk motive).app (rename wk k).natSucc)
                = .app (subst (subst0 rec) (rename wk motive))
                    (.natSucc (subst (subst0 rec) (rename wk k))) := by
                      rfl
            _ = .app motive (.natSucc k) := by
                  simp [subst0_wk_cancel]

private theorem ctxMor_subst0 {Γ : Ctx n} {A a : PureTm n}
    (ha : HasType Γ a A) :
    CtxMor (.snoc Γ A) Γ (subst0 a) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa [CtxMor, lookup_snoc_zero, subst0_wk_cancel] using ha
  · intro j
    simpa [CtxMor, lookup_snoc_succ, subst0_wk_cancel] using
      (HasType.var (Γ := Γ) (i := j))

private theorem typing_inst0 {Γ : Ctx n} {A a : PureTm n} {body B : PureTm (n + 1)}
    (hbody : HasType (.snoc Γ A) body B) (ha : HasType Γ a A) :
    HasType Γ (inst0 a body) (inst0 a B) := by
  simpa [inst0] using
    (typing_subst (Γ := .snoc Γ A) (Δ := Γ) (σ := subst0 a) hbody (ctxMor_subst0 ha))

private def tmOf {Γ : Ctx n} {t A : PureTm n} (_ : HasType Γ t A) : PureTm n := t

private theorem parStar_inst0_arg {a a' : PureTm n} {B : PureTm (n + 1)}
    (h : ParStar a a') : ParStar (inst0 a B) (inst0 a' B) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih (par_inst0 hyz (par_refl B))

private theorem redStar_inst0_arg {a a' : PureTm n} {B : PureTm (n + 1)}
    (h : RedStar a a') : RedStar (inst0 a B) (inst0 a' B) := by
  exact parStar_to_redStar (parStar_inst0_arg (redStar_to_parStar h))

private theorem conv_inst0_arg {a a' : PureTm n} {B : PureTm (n + 1)}
    (h : Conv a a') : Conv (inst0 a B) (inst0 a' B) := by
  rcases church_rosser_conv h with ⟨u, ha, ha'⟩
  have h1 : RedStar (inst0 a B) (inst0 u B) := redStar_inst0_arg ha
  have h2 : RedStar (inst0 a' B) (inst0 u B) := redStar_inst0_arg ha'
  have hc1 : Conv (inst0 a B) (inst0 u B) := redStar_implies_conv h1
  have hc2 : Conv (inst0 a' B) (inst0 u B) := redStar_implies_conv h2
  exact Relation.EqvGen.trans _ _ _ hc1 (Relation.EqvGen.symm _ _ hc2)

private theorem conv_app_fun {f f' a : PureTm n}
    (h : Conv f f') : Conv (.app f a) (.app f' a) := by
  rcases church_rosser_conv h with ⟨u, hf, hf'⟩
  have h1 : RedStar (.app f a) (.app u a) := RedStar.congAppFun hf
  have h2 : RedStar (.app f' a) (.app u a) := RedStar.congAppFun hf'
  exact Relation.EqvGen.trans _ _ _ (redStar_implies_conv h1)
    (Relation.EqvGen.symm _ _ (redStar_implies_conv h2))

private theorem conv_app_arg {f a a' : PureTm n}
    (h : Conv a a') : Conv (.app f a) (.app f a') := by
  rcases church_rosser_conv h with ⟨u, ha, ha'⟩
  have h1 : RedStar (.app f a) (.app f u) := RedStar.congAppArg ha
  have h2 : RedStar (.app f a') (.app f u) := RedStar.congAppArg ha'
  exact Relation.EqvGen.trans _ _ _ (redStar_implies_conv h1)
    (Relation.EqvGen.symm _ _ (redStar_implies_conv h2))

private theorem conv_pi {A A' : PureTm n} {B B' : PureTm (n + 1)}
    (hA : Conv A A') (hB : Conv B B') : Conv (.pi A B) (.pi A' B') := by
  rcases church_rosser_conv hA with ⟨U, hAU, hA'U⟩
  rcases church_rosser_conv hB with ⟨V, hBV, hB'V⟩
  have h1 : RedStar (.pi A B) (.pi U V) :=
    RedStar.trans (RedStar.congPiDom hAU) (RedStar.congPiCod hBV)
  have h2 : RedStar (.pi A' B') (.pi U V) :=
    RedStar.trans (RedStar.congPiDom hA'U) (RedStar.congPiCod hB'V)
  exact Relation.EqvGen.trans _ _ _ (redStar_implies_conv h1)
    (Relation.EqvGen.symm _ _ (redStar_implies_conv h2))

private theorem conv_natRecStepTy {motive motive' : PureTm n}
    (h : Conv motive motive') : Conv (natRecStepTy motive) (natRecStepTy motive') := by
  have hDom : Conv (.app (rename wk motive) (.var 0)) (.app (rename wk motive') (.var 0)) :=
    conv_app_fun (conv_rename (ρ := wk) h)
  have hCod :
      Conv (.app (rename wk (rename wk motive)) (.natSucc (.var 1)))
        (.app (rename wk (rename wk motive')) (.natSucc (.var 1))) := by
    have hShift : Conv (rename wk (rename wk motive)) (rename wk (rename wk motive')) := by
      exact conv_rename (ρ := wk) (conv_rename (ρ := wk) h)
    exact conv_app_fun hShift
  exact conv_pi (conv_refl .natTy) (conv_pi hDom hCod)

private theorem app_generation_aux {Γ : Ctx n} {t C : PureTm n}
    (ht : HasType Γ t C) :
    ∀ {f a : PureTm n}, t = .app f a →
      ∃ A B, HasType Γ f (.pi A B) ∧ HasType Γ a A ∧ Conv (inst0 a B) C := by
  induction ht with
  | app_elim hf ha =>
      intro f a hEq
      cases hEq
      exact ⟨_, _, hf, ha, conv_refl _⟩
  | conv ht hconv ih =>
      intro f a hEq
      rcases ih hEq with ⟨A, B, hf, ha, hC⟩
      exact ⟨A, B, hf, ha, Relation.EqvGen.trans _ _ _ hC hconv⟩
  | u0_type =>
      intro f a hEq
      cases hEq
  | unitTy_type =>
      intro f a hEq
      cases hEq
  | unitMk_intro =>
      intro f a hEq
      cases hEq
  | boolTy_type =>
      intro f a hEq
      cases hEq
  | boolFalse_intro =>
      intro f a hEq
      cases hEq
  | boolTrue_intro =>
      intro f a hEq
      cases hEq
  | natTy_type =>
      intro f a hEq
      cases hEq
  | natZero_intro =>
      intro f a hEq
      cases hEq
  | var =>
      intro f a hEq
      cases hEq
  | natSucc_intro hk ihk =>
      intro f a hEq
      cases hEq
  | pi_form hA hB ihA ihB =>
      intro f a hEq
      cases hEq
  | sigma_form hA hB ihA ihB =>
      intro f a hEq
      cases hEq
  | lam_intro hBody ihBody =>
      intro f a hEq
      cases hEq
  | pair_intro ha hb iha ihb =>
      intro f a hEq
      cases hEq
  | fst_elim hp ihp =>
      intro f a hEq
      cases hEq
  | snd_elim hp ihp =>
      intro f a hEq
      cases hEq
  | id_form hA ha hb ihA iha ihb =>
      intro f a hEq
      cases hEq
  | refl_intro ha iha =>
      intro f a hEq
      cases hEq
  | unitRec_elim hmotive hcase hscrutinee ihmotive ihcase ihscrutinee =>
      intro f a hEq
      cases hEq
  | boolRec_elim hmotive hFalse hTrue hscrutinee ihmotive ihFalse ihTrue ihscrutinee =>
      intro f a hEq
      cases hEq
  | natRec_elim hmotive hZero hSucc hscrutinee ihmotive ihZero ihSucc ihscrutinee =>
      intro f a hEq
      cases hEq

theorem app_generation {Γ : Ctx n} {f a C : PureTm n}
    (ht : HasType Γ (.app f a) C) :
    ∃ A B, HasType Γ f (.pi A B) ∧ HasType Γ a A ∧ Conv (inst0 a B) C :=
  app_generation_aux ht rfl

private theorem lam_generation_aux {Γ : Ctx n} {t C : PureTm n}
    (ht : HasType Γ t C) :
    ∀ {body : PureTm (n + 1)}, t = .lam body →
      ∃ A B, HasType (.snoc Γ A) body B ∧ Conv (.pi A B) C := by
  induction ht with
  | lam_intro hBody =>
      intro body hEq
      cases hEq
      exact ⟨_, _, hBody, conv_refl _⟩
  | conv ht hconv ih =>
      intro body hEq
      rcases ih hEq with ⟨A, B, hBody, hPi⟩
      exact ⟨A, B, hBody, Relation.EqvGen.trans _ _ _ hPi hconv⟩
  | u0_type =>
      intro body hEq
      cases hEq
  | unitTy_type =>
      intro body hEq
      cases hEq
  | unitMk_intro =>
      intro body hEq
      cases hEq
  | boolTy_type =>
      intro body hEq
      cases hEq
  | boolFalse_intro =>
      intro body hEq
      cases hEq
  | boolTrue_intro =>
      intro body hEq
      cases hEq
  | natTy_type =>
      intro body hEq
      cases hEq
  | natZero_intro =>
      intro body hEq
      cases hEq
  | var =>
      intro body hEq
      cases hEq
  | natSucc_intro hk ihk =>
      intro body hEq
      cases hEq
  | pi_form hA hB ihA ihB =>
      intro body hEq
      cases hEq
  | sigma_form hA hB ihA ihB =>
      intro body hEq
      cases hEq
  | app_elim hf ha ihf iha =>
      intro body hEq
      cases hEq
  | pair_intro ha hb iha ihb =>
      intro body hEq
      cases hEq
  | fst_elim hp ihp =>
      intro body hEq
      cases hEq
  | snd_elim hp ihp =>
      intro body hEq
      cases hEq
  | id_form hA ha hb ihA iha ihb =>
      intro body hEq
      cases hEq
  | refl_intro ha iha =>
      intro body hEq
      cases hEq
  | unitRec_elim hmotive hcase hscrutinee ihmotive ihcase ihscrutinee =>
      intro body hEq
      cases hEq
  | boolRec_elim hmotive hFalse hTrue hscrutinee ihmotive ihFalse ihTrue ihscrutinee =>
      intro body hEq
      cases hEq
  | natRec_elim hmotive hZero hSucc hscrutinee ihmotive ihZero ihSucc ihscrutinee =>
      intro body hEq
      cases hEq

theorem lam_generation {Γ : Ctx n} {body : PureTm (n + 1)} {C : PureTm n}
    (ht : HasType Γ (.lam body) C) :
    ∃ A B, HasType (.snoc Γ A) body B ∧ Conv (.pi A B) C :=
  lam_generation_aux ht rfl

private theorem pair_generation_aux {Γ : Ctx n} {t C : PureTm n}
    (ht : HasType Γ t C) :
    ∀ {a b : PureTm n}, t = .pair a b →
      ∃ A B, HasType Γ a A ∧ HasType Γ b (inst0 a B) ∧ Conv (.sigma A B) C := by
  induction ht with
  | pair_intro ha hb =>
      intro a b hEq
      cases hEq
      exact ⟨_, _, ha, hb, conv_refl _⟩
  | conv ht hconv ih =>
      intro a b hEq
      rcases ih hEq with ⟨A, B, ha, hb, hSigma⟩
      exact ⟨A, B, ha, hb, Relation.EqvGen.trans _ _ _ hSigma hconv⟩
  | u0_type =>
      intro a b hEq
      cases hEq
  | var =>
      intro a b hEq
      cases hEq
  | pi_form hA hB ihA ihB =>
      intro a b hEq
      cases hEq
  | sigma_form hA hB ihA ihB =>
      intro a b hEq
      cases hEq
  | lam_intro hBody ihBody =>
      intro a b hEq
      cases hEq
  | app_elim hf ha ihf iha =>
      intro a b hEq
      cases hEq
  | fst_elim hp ihp =>
      intro a b hEq
      cases hEq
  | snd_elim hp ihp =>
      intro a b hEq
      cases hEq
  | id_form hA ha hb ihA iha ihb =>
      intro a b hEq
      cases hEq
  | refl_intro ha iha =>
      intro a b hEq
      cases hEq
  | unitTy_type =>
      intro a b hEq
      cases hEq
  | unitMk_intro =>
      intro a b hEq
      cases hEq
  | boolTy_type =>
      intro a b hEq
      cases hEq
  | boolFalse_intro =>
      intro a b hEq
      cases hEq
  | boolTrue_intro =>
      intro a b hEq
      cases hEq
  | natTy_type =>
      intro a b hEq
      cases hEq
  | natZero_intro =>
      intro a b hEq
      cases hEq
  | natSucc_intro hk ihk =>
      intro a b hEq
      cases hEq
  | unitRec_elim hmotive hcase hscrutinee ihmotive ihcase ihscrutinee =>
      intro a b hEq
      cases hEq
  | boolRec_elim hmotive hFalse hTrue hscrutinee ihmotive ihFalse ihTrue ihscrutinee =>
      intro a b hEq
      cases hEq
  | natRec_elim hmotive hZero hSucc hscrutinee ihmotive ihZero ihSucc ihscrutinee =>
      intro a b hEq
      cases hEq

theorem pair_generation {Γ : Ctx n} {a b C : PureTm n}
    (ht : HasType Γ (.pair a b) C) :
    ∃ A B, HasType Γ a A ∧ HasType Γ b (inst0 a B) ∧ Conv (.sigma A B) C :=
  pair_generation_aux ht rfl

private theorem natSucc_generation_aux {Γ : Ctx n} {t C : PureTm n}
    (ht : HasType Γ t C) :
    ∀ {k : PureTm n}, t = .natSucc k →
      HasType Γ k .natTy ∧ Conv .natTy C := by
  induction ht with
  | natSucc_intro hk =>
      intro k hEq
      cases hEq
      exact ⟨hk, conv_refl _⟩
  | conv ht hconv ih =>
      intro k hEq
      rcases ih hEq with ⟨hk, hC⟩
      exact ⟨hk, Relation.EqvGen.trans _ _ _ hC hconv⟩
  | u0_type =>
      intro k hEq
      cases hEq
  | unitTy_type =>
      intro k hEq
      cases hEq
  | unitMk_intro =>
      intro k hEq
      cases hEq
  | boolTy_type =>
      intro k hEq
      cases hEq
  | boolFalse_intro =>
      intro k hEq
      cases hEq
  | boolTrue_intro =>
      intro k hEq
      cases hEq
  | natTy_type =>
      intro k hEq
      cases hEq
  | natZero_intro =>
      intro k hEq
      cases hEq
  | var =>
      intro k hEq
      cases hEq
  | pi_form hA hB ihA ihB =>
      intro k hEq
      cases hEq
  | sigma_form hA hB ihA ihB =>
      intro k hEq
      cases hEq
  | lam_intro hBody ihBody =>
      intro k hEq
      cases hEq
  | app_elim hf ha ihf iha =>
      intro k hEq
      cases hEq
  | pair_intro ha hb iha ihb =>
      intro k hEq
      cases hEq
  | fst_elim hp ihp =>
      intro k hEq
      cases hEq
  | snd_elim hp ihp =>
      intro k hEq
      cases hEq
  | id_form hA ha hb ihA iha ihb =>
      intro k hEq
      cases hEq
  | refl_intro ha iha =>
      intro k hEq
      cases hEq
  | unitRec_elim hmotive hcase hscrutinee ihmotive ihcase ihscrutinee =>
      intro k hEq
      cases hEq
  | boolRec_elim hmotive hFalse hTrue hscrutinee ihmotive ihFalse ihTrue ihscrutinee =>
      intro k hEq
      cases hEq
  | natRec_elim hmotive hZero hSucc hscrutinee ihmotive ihZero ihSucc ihscrutinee =>
      intro k hEq
      cases hEq

theorem natSucc_generation {Γ : Ctx n} {k C : PureTm n}
    (ht : HasType Γ (.natSucc k) C) :
    HasType Γ k .natTy ∧ Conv .natTy C :=
  natSucc_generation_aux ht rfl

/-- One-step subject reduction for the Pure kernel. -/
theorem subject_reduction {Γ : Ctx n} {t t' A : PureTm n}
    (ht : HasType Γ t A) (hr : Red t t') :
    HasType Γ t' A := by
  induction ht with
  | u0_type =>
      cases hr
  | unitTy_type =>
      cases hr
  | unitMk_intro =>
      cases hr
  | boolTy_type =>
      cases hr
  | boolFalse_intro =>
      cases hr
  | boolTrue_intro =>
      cases hr
  | natTy_type =>
      cases hr
  | natZero_intro =>
      cases hr
  | var =>
      cases hr
  | @natSucc_intro n Γ k hk ihk =>
      cases hr with
      | congNatSucc hred =>
          exact .natSucc_intro (ihk hred)
  | @pi_form n Γ A B hA hB ihA ihB =>
      cases hr with
      | congPiDom hred =>
          have hA' : HasType Γ _ .u1 := ihA hred
          have hB' : HasType (.snoc Γ _) B .u1 := context_conv_head (red_implies_conv hred) hB
          exact .pi_form hA' hB'
      | congPiCod hred =>
          exact .pi_form hA (ihB hred)
  | @sigma_form n Γ A B hA hB ihA ihB =>
      cases hr with
      | congSigmaDom hred =>
          have hA' : HasType Γ _ .u1 := ihA hred
          have hB' : HasType (.snoc Γ _) B .u1 := context_conv_head (red_implies_conv hred) hB
          exact .sigma_form hA' hB'
      | congSigmaCod hred =>
          exact .sigma_form hA (ihB hred)
  | @lam_intro n Γ A body B hBody ihBody =>
      cases hr with
      | congLam hred =>
          exact .lam_intro (ihBody hred)
  | @app_elim n Γ f a A B hf ha ihf iha =>
      cases hr with
      | betaPi body _ =>
          have hfLam : HasType Γ (.lam body) (.pi A B) := by
            simpa using hf
          have haArg : HasType Γ a A := by
            simpa using ha
          rcases lam_generation hfLam with ⟨A1, B1, hBody, hPiConv⟩
          have hAB : Conv A1 A ∧ Conv B1 B := pi_injectivity hPiConv
          have ha1 : HasType Γ a A1 :=
            .conv haArg (Relation.EqvGen.symm _ _ hAB.1)
          have hSub : HasType Γ (inst0 a body) (inst0 a B1) :=
            typing_inst0 hBody ha1
          have hTy : Conv (inst0 a B1) (inst0 a B) :=
            conv_subst (σ := subst0 a) hAB.2
          have hRes : HasType Γ (inst0 a body) (inst0 a B) :=
            .conv hSub hTy
          simpa using hRes
      | congAppFun hred =>
          exact .app_elim (ihf hred) ha
      | congAppArg hred =>
          have ha' : HasType Γ _ A := iha hred
          have hApp' : HasType Γ (.app f _) (inst0 _ B) := .app_elim hf ha'
          have hArgConv : Conv a _ := red_implies_conv hred
          have hTy : Conv (inst0 _ B) (inst0 a B) :=
            conv_inst0_arg (Relation.EqvGen.symm _ _ hArgConv)
          exact .conv hApp' hTy
  | @pair_intro n Γ a b A B ha hb iha ihb =>
      cases hr with
      | congPairFst hred =>
          have ha' : HasType Γ _ A := iha hred
          have hArgConv : Conv a _ := red_implies_conv hred
          have hTy : Conv (inst0 a B) (inst0 _ B) := conv_inst0_arg hArgConv
          have hb' : HasType Γ b (inst0 _ B) := .conv hb hTy
          exact .pair_intro ha' hb'
      | congPairSnd hred =>
          exact .pair_intro ha (ihb hred)
  | @fst_elim n Γ p A B hp ihp =>
      cases hr with
      | betaSigmaFst _ _ =>
          rcases pair_generation hp with ⟨A1, B1, ha1, hb1, hSigma⟩
          have hAB : Conv A1 A ∧ Conv B1 B := sigma_injectivity hSigma
          exact .conv ha1 hAB.1
      | congFst hred =>
          exact .fst_elim (ihp hred)
  | @snd_elim n Γ p A B hp ihp =>
      cases hr with
      | betaSigmaSnd _ _ =>
          rcases pair_generation hp with ⟨A1, B1, ha1, hb1, hSigma⟩
          have hAB : Conv A1 A ∧ Conv B1 B := sigma_injectivity hSigma
          let a0 : PureTm n := tmOf ha1
          let b0 : PureTm n := tmOf hb1
          have hb1' : HasType Γ b0 (inst0 a0 B1) := by
            simpa [a0, b0, tmOf] using hb1
          have hCod : Conv (inst0 a0 B1) (inst0 a0 B) :=
            conv_subst (σ := subst0 a0) hAB.2
          have hFst : Conv a0 (.fst (.pair a0 b0)) :=
            Relation.EqvGen.symm _ _ (red_implies_conv (Red.betaSigmaFst a0 b0))
          have hArg : Conv (inst0 a0 B) (inst0 (.fst (.pair a0 b0)) B) :=
            conv_inst0_arg hFst
          exact .conv hb1' (Relation.EqvGen.trans _ _ _ hCod hArg)
      | congSnd hred =>
          have hp' : HasType Γ _ (.sigma A B) := ihp hred
          have hsnd' : HasType Γ (.snd _) (inst0 (.fst _) B) := .snd_elim hp'
          have hFst : Conv (.fst _) (.fst p) :=
            Relation.EqvGen.symm _ _ (red_implies_conv (Red.congFst hred))
          have hTy : Conv (inst0 (.fst _) B) (inst0 (.fst p) B) :=
            conv_inst0_arg hFst
          exact .conv hsnd' hTy
  | @id_form n Γ A a b hA ha hb ihA iha ihb =>
      cases hr with
      | congIdTy hred =>
          have hA' : HasType Γ _ .u1 := ihA hred
          have hAA' : Conv A _ := red_implies_conv hred
          have ha' : HasType Γ a _ := .conv ha hAA'
          have hb' : HasType Γ b _ := .conv hb hAA'
          exact .id_form hA' ha' hb'
      | congIdLeft hred =>
          exact .id_form hA (iha hred) hb
      | congIdRight hred =>
          exact .id_form hA ha (ihb hred)
  | @refl_intro n Γ a A ha iha =>
      cases hr with
      | congRefl hred =>
          have ha' : HasType Γ _ A := iha hred
          let a' : PureTm n := tmOf ha'
          have hidL : Conv (.id A a a) (.id A a' a) :=
            red_implies_conv (Red.congIdLeft hred)
          have hidR : Conv (.id A a' a) (.id A a' a') :=
            red_implies_conv (Red.congIdRight (A := A) (a := a') hred)
          have hid : Conv (.id A a a) (.id A a' a') :=
            Relation.EqvGen.trans _ _ _ hidL hidR
          exact .conv (.refl_intro ha') (Relation.EqvGen.symm _ _ hid)
  | @unitRec_elim n Γ motive unitCase scrutinee hmotive hcase hscrutinee ihmotive ihcase ihscrutinee =>
      cases hr with
      | betaUnitRec =>
          simpa using hcase
      | congUnitRecMotive hred =>
          let motive' : PureTm n := tmOf (ihmotive hred)
          have hmotive' : HasType Γ motive' unitMotiveTy := ihmotive hred
          have hcase' : HasType Γ unitCase (.app motive' .unitMk) := by
            exact .conv hcase (conv_app_fun (red_implies_conv hred))
          have hTarget : HasType Γ (.unitRec motive' unitCase scrutinee) (.app motive' scrutinee) :=
            .unitRec_elim hmotive' hcase' hscrutinee
          have hTy : Conv (.app motive' scrutinee) (.app motive scrutinee) :=
            Relation.EqvGen.symm _ _ (conv_app_fun (red_implies_conv hred))
          exact .conv hTarget hTy
      | congUnitRecCase hred =>
          exact .unitRec_elim hmotive (ihcase hred) hscrutinee
      | congUnitRecScrutinee hred =>
          let scrutinee' : PureTm n := tmOf (ihscrutinee hred)
          have hscrutinee' : HasType Γ scrutinee' PureTm.unitTy := ihscrutinee hred
          have hTarget : HasType Γ (.unitRec motive unitCase scrutinee') (.app motive scrutinee') :=
            .unitRec_elim hmotive hcase hscrutinee'
          exact .conv hTarget (Relation.EqvGen.symm _ _ (conv_app_arg (red_implies_conv hred)))
  | @boolRec_elim n Γ motive falseCase trueCase scrutinee hmotive hFalse hTrue hscrutinee
      ihmotive ihFalse ihTrue ihscrutinee =>
      cases hr with
      | betaBoolRecFalse =>
          simpa using hFalse
      | betaBoolRecTrue =>
          simpa using hTrue
      | congBoolRecMotive hred =>
          let motive' : PureTm n := tmOf (ihmotive hred)
          have hmotive' : HasType Γ motive' boolMotiveTy := ihmotive hred
          have hFalse' : HasType Γ falseCase (.app motive' .boolFalse) := by
            exact .conv hFalse (conv_app_fun (red_implies_conv hred))
          have hTrue' : HasType Γ trueCase (.app motive' .boolTrue) := by
            exact .conv hTrue (conv_app_fun (red_implies_conv hred))
          have hTarget : HasType Γ (.boolRec motive' falseCase trueCase scrutinee) (.app motive' scrutinee) :=
            .boolRec_elim hmotive' hFalse' hTrue' hscrutinee
          have hTy : Conv (.app motive' scrutinee) (.app motive scrutinee) :=
            Relation.EqvGen.symm _ _ (conv_app_fun (red_implies_conv hred))
          exact .conv hTarget hTy
      | congBoolRecFalseCase hred =>
          exact .boolRec_elim hmotive (ihFalse hred) hTrue hscrutinee
      | congBoolRecTrueCase hred =>
          exact .boolRec_elim hmotive hFalse (ihTrue hred) hscrutinee
      | congBoolRecScrutinee hred =>
          let scrutinee' : PureTm n := tmOf (ihscrutinee hred)
          have hscrutinee' : HasType Γ scrutinee' PureTm.boolTy := ihscrutinee hred
          have hTarget : HasType Γ (.boolRec motive falseCase trueCase scrutinee') (.app motive scrutinee') :=
            .boolRec_elim hmotive hFalse hTrue hscrutinee'
          exact .conv hTarget (Relation.EqvGen.symm _ _ (conv_app_arg (red_implies_conv hred)))
  | @natRec_elim n Γ motive zeroCase succCase scrutinee hmotive hZero hSucc hscrutinee
      ihmotive ihZero ihSucc ihscrutinee =>
      cases hr with
      | betaNatRecZero =>
          simpa using hZero
      | betaNatRecSucc =>
          rcases natSucc_generation hscrutinee with ⟨hk, _⟩
          let k : PureTm n := tmOf hk
          have hk' : HasType Γ k PureTm.natTy := hk
          have hStep1 := HasType.app_elim hSucc hk'
          have hRec : HasType Γ (.natRec motive zeroCase succCase k) (.app motive k) :=
            .natRec_elim hmotive hZero hSucc hk'
          have hRec' :
              HasType Γ (.natRec motive zeroCase succCase k)
                (subst (subst0 k) (.app (rename wk motive) (.var 0))) := by
            simpa [inst0_rename_wk_app_zero] using hRec
          have hStep2 := HasType.app_elim hStep1 hRec'
          have hTyEq :
              inst0 (.natRec motive zeroCase succCase k)
                (subst (liftSub (subst0 k))
                  (.app (rename wk (rename wk motive)) (.natSucc (.var 1)))) =
                .app motive (.natSucc k) :=
            natRecSuccCodomain_inst0 motive k (.natRec motive zeroCase succCase k)
          exact .conv hStep2 (by rw [hTyEq]; exact conv_refl _)
      | congNatRecMotive hred =>
          let motive' : PureTm n := tmOf (ihmotive hred)
          have hmotive' : HasType Γ motive' natMotiveTy := ihmotive hred
          have hZero' : HasType Γ zeroCase (.app motive' .natZero) := by
            exact .conv hZero (conv_app_fun (red_implies_conv hred))
          have hSucc' : HasType Γ succCase (natRecStepTy motive') := by
            exact .conv hSucc (conv_natRecStepTy (red_implies_conv hred))
          have hTarget : HasType Γ (.natRec motive' zeroCase succCase scrutinee) (.app motive' scrutinee) :=
            .natRec_elim hmotive' hZero' hSucc' hscrutinee
          have hTy : Conv (.app motive' scrutinee) (.app motive scrutinee) :=
            Relation.EqvGen.symm _ _ (conv_app_fun (red_implies_conv hred))
          exact .conv hTarget hTy
      | congNatRecZeroCase hred =>
          exact .natRec_elim hmotive (ihZero hred) hSucc hscrutinee
      | congNatRecSuccCase hred =>
          exact .natRec_elim hmotive hZero (ihSucc hred) hscrutinee
      | congNatRecScrutinee hred =>
          let scrutinee' : PureTm n := tmOf (ihscrutinee hred)
          have hscrutinee' : HasType Γ scrutinee' PureTm.natTy := ihscrutinee hred
          have hTarget : HasType Γ (.natRec motive zeroCase succCase scrutinee') (.app motive scrutinee') :=
            .natRec_elim hmotive hZero hSucc hscrutinee'
          exact .conv hTarget (Relation.EqvGen.symm _ _ (conv_app_arg (red_implies_conv hred)))
  | @conv n Γ t A B ht hAB ih =>
      exact .conv (ih hr) hAB

end Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction
