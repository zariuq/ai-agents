import Mettapedia.Languages.MeTTa.PureKernel.Reduction

namespace Mettapedia.Languages.MeTTa.PureKernel.Parallel

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction

/-- Parallel one-step reduction for the Pure kernel. -/
inductive ParRed : PureTm n → PureTm n → Prop where
  | var (i : Fin n) : ParRed (.var i) (.var i)
  | u0 : ParRed (.u0 : PureTm n) .u0
  | u1 : ParRed (.u1 : PureTm n) .u1
  | unitTy : ParRed (.unitTy : PureTm n) .unitTy
  | unitMk : ParRed (.unitMk : PureTm n) .unitMk
  | boolTy : ParRed (.boolTy : PureTm n) .boolTy
  | boolFalse : ParRed (.boolFalse : PureTm n) .boolFalse
  | boolTrue : ParRed (.boolTrue : PureTm n) .boolTrue
  | natTy : ParRed (.natTy : PureTm n) .natTy
  | natZero : ParRed (.natZero : PureTm n) .natZero
  | natSucc {k k' : PureTm n} :
      ParRed k k' → ParRed (.natSucc k) (.natSucc k')
  | pi {A A' : PureTm n} {B B' : PureTm (n + 1)} :
      ParRed A A' → ParRed B B' → ParRed (.pi A B) (.pi A' B')
  | sigma {A A' : PureTm n} {B B' : PureTm (n + 1)} :
      ParRed A A' → ParRed B B' → ParRed (.sigma A B) (.sigma A' B')
  | id {A A' a a' b b' : PureTm n} :
      ParRed A A' → ParRed a a' → ParRed b b' → ParRed (.id A a b) (.id A' a' b')
  | lam {b b' : PureTm (n + 1)} :
      ParRed b b' → ParRed (.lam b) (.lam b')
  | app {f f' a a' : PureTm n} :
      ParRed f f' → ParRed a a' → ParRed (.app f a) (.app f' a')
  | pair {a a' b b' : PureTm n} :
      ParRed a a' → ParRed b b' → ParRed (.pair a b) (.pair a' b')
  | fst {p p' : PureTm n} :
      ParRed p p' → ParRed (.fst p) (.fst p')
  | snd {p p' : PureTm n} :
      ParRed p p' → ParRed (.snd p) (.snd p')
  | refl {a a' : PureTm n} :
      ParRed a a' → ParRed (.refl a) (.refl a')
  | unitRec {motive motive' unitCase unitCase' scrutinee scrutinee' : PureTm n} :
      ParRed motive motive' →
      ParRed unitCase unitCase' →
      ParRed scrutinee scrutinee' →
      ParRed (.unitRec motive unitCase scrutinee) (.unitRec motive' unitCase' scrutinee')
  | boolRec {motive motive' falseCase falseCase' trueCase trueCase' scrutinee scrutinee' : PureTm n} :
      ParRed motive motive' →
      ParRed falseCase falseCase' →
      ParRed trueCase trueCase' →
      ParRed scrutinee scrutinee' →
      ParRed (.boolRec motive falseCase trueCase scrutinee)
        (.boolRec motive' falseCase' trueCase' scrutinee')
  | natRec {motive motive' zeroCase zeroCase' succCase succCase' scrutinee scrutinee' : PureTm n} :
      ParRed motive motive' →
      ParRed zeroCase zeroCase' →
      ParRed succCase succCase' →
      ParRed scrutinee scrutinee' →
      ParRed (.natRec motive zeroCase succCase scrutinee)
        (.natRec motive' zeroCase' succCase' scrutinee')
  | betaPi {body body' : PureTm (n + 1)} {a a' : PureTm n} :
      ParRed body body' → ParRed a a' →
      ParRed (.app (.lam body) a) (inst0 a' body')
  | betaSigmaFst {a a' b b' : PureTm n} :
      ParRed a a' → ParRed b b' →
      ParRed (.fst (.pair a b)) a'
  | betaSigmaSnd {a a' b b' : PureTm n} :
      ParRed a a' → ParRed b b' →
      ParRed (.snd (.pair a b)) b'
  | betaUnitRec {motive motive' unitCase unitCase' : PureTm n} :
      ParRed motive motive' →
      ParRed unitCase unitCase' →
      ParRed (.unitRec motive unitCase .unitMk) unitCase'
  | betaBoolRecFalse {motive motive' falseCase falseCase' trueCase trueCase' : PureTm n} :
      ParRed motive motive' →
      ParRed falseCase falseCase' →
      ParRed trueCase trueCase' →
      ParRed (.boolRec motive falseCase trueCase .boolFalse) falseCase'
  | betaBoolRecTrue {motive motive' falseCase falseCase' trueCase trueCase' : PureTm n} :
      ParRed motive motive' →
      ParRed falseCase falseCase' →
      ParRed trueCase trueCase' →
      ParRed (.boolRec motive falseCase trueCase .boolTrue) trueCase'
  | betaNatRecZero {motive motive' zeroCase zeroCase' succCase succCase' : PureTm n} :
      ParRed motive motive' →
      ParRed zeroCase zeroCase' →
      ParRed succCase succCase' →
      ParRed (.natRec motive zeroCase succCase .natZero) zeroCase'
  | betaNatRecSucc {motive motive' zeroCase zeroCase' succCase succCase' k k' : PureTm n} :
      ParRed motive motive' →
      ParRed zeroCase zeroCase' →
      ParRed succCase succCase' →
      ParRed k k' →
      ParRed (.natRec motive zeroCase succCase (.natSucc k))
        (.app (.app succCase' k') (.natRec motive' zeroCase' succCase' k'))

@[simp] theorem par_refl : ∀ t : PureTm n, ParRed t t := by
  intro t
  induction t with
  | var i => exact .var i
  | u0 => exact .u0
  | u1 => exact .u1
  | unitTy => exact .unitTy
  | unitMk => exact .unitMk
  | boolTy => exact .boolTy
  | boolFalse => exact .boolFalse
  | boolTrue => exact .boolTrue
  | natTy => exact .natTy
  | natZero => exact .natZero
  | natSucc k ih => exact .natSucc ih
  | pi A B ihA ihB => exact .pi ihA ihB
  | sigma A B ihA ihB => exact .sigma ihA ihB
  | id A a b ihA iha ihb => exact .id ihA iha ihb
  | lam b ih => exact .lam ih
  | app f a ihf iha => exact .app ihf iha
  | pair a b iha ihb => exact .pair iha ihb
  | fst p ih => exact .fst ih
  | snd p ih => exact .snd ih
  | refl a iha => exact .refl iha
  | unitRec motive unitCase scrutinee ihmotive ihcase ihscrutinee =>
      exact .unitRec ihmotive ihcase ihscrutinee
  | boolRec motive falseCase trueCase scrutinee ihmotive ihFalse ihTrue ihscrutinee =>
      exact .boolRec ihmotive ihFalse ihTrue ihscrutinee
  | natRec motive zeroCase succCase scrutinee ihmotive ihZero ihSucc ihscrutinee =>
      exact .natRec ihmotive ihZero ihSucc ihscrutinee

theorem red_to_par {t u : PureTm n} (h : Red t u) : ParRed t u := by
  induction h with
  | betaPi body a =>
      exact .betaPi (par_refl body) (par_refl a)
  | betaSigmaFst a b =>
      exact .betaSigmaFst (par_refl a) (par_refl b)
  | betaSigmaSnd a b =>
      exact .betaSigmaSnd (par_refl a) (par_refl b)
  | betaUnitRec motive unitCase =>
      exact .betaUnitRec (par_refl motive) (par_refl unitCase)
  | betaBoolRecFalse motive falseCase trueCase =>
      exact .betaBoolRecFalse (par_refl motive) (par_refl falseCase) (par_refl trueCase)
  | betaBoolRecTrue motive falseCase trueCase =>
      exact .betaBoolRecTrue (par_refl motive) (par_refl falseCase) (par_refl trueCase)
  | betaNatRecZero motive zeroCase succCase =>
      exact .betaNatRecZero (par_refl motive) (par_refl zeroCase) (par_refl succCase)
  | betaNatRecSucc motive zeroCase succCase k =>
      exact .betaNatRecSucc (par_refl motive) (par_refl zeroCase) (par_refl succCase) (par_refl k)
  | congPiDom h ih =>
      exact .pi ih (par_refl _)
  | congPiCod h ih =>
      exact .pi (par_refl _) ih
  | congSigmaDom h ih =>
      exact .sigma ih (par_refl _)
  | congSigmaCod h ih =>
      exact .sigma (par_refl _) ih
  | congIdTy h ih =>
      exact .id ih (par_refl _) (par_refl _)
  | congIdLeft h ih =>
      exact .id (par_refl _) ih (par_refl _)
  | congIdRight h ih =>
      exact .id (par_refl _) (par_refl _) ih
  | congLam h ih =>
      exact .lam ih
  | congAppFun h ih =>
      exact .app ih (par_refl _)
  | congAppArg h ih =>
      exact .app (par_refl _) ih
  | congPairFst h ih =>
      exact .pair ih (par_refl _)
  | congPairSnd h ih =>
      exact .pair (par_refl _) ih
  | congFst h ih =>
      exact .fst ih
  | congSnd h ih =>
      exact .snd ih
  | congRefl h ih =>
      exact .refl ih
  | congNatSucc h ih =>
      exact .natSucc ih
  | congUnitRecMotive h ih =>
      exact .unitRec ih (par_refl _) (par_refl _)
  | congUnitRecCase h ih =>
      exact .unitRec (par_refl _) ih (par_refl _)
  | congUnitRecScrutinee h ih =>
      exact .unitRec (par_refl _) (par_refl _) ih
  | congBoolRecMotive h ih =>
      exact .boolRec ih (par_refl _) (par_refl _) (par_refl _)
  | congBoolRecFalseCase h ih =>
      exact .boolRec (par_refl _) ih (par_refl _) (par_refl _)
  | congBoolRecTrueCase h ih =>
      exact .boolRec (par_refl _) (par_refl _) ih (par_refl _)
  | congBoolRecScrutinee h ih =>
      exact .boolRec (par_refl _) (par_refl _) (par_refl _) ih
  | congNatRecMotive h ih =>
      exact .natRec ih (par_refl _) (par_refl _) (par_refl _)
  | congNatRecZeroCase h ih =>
      exact .natRec (par_refl _) ih (par_refl _) (par_refl _)
  | congNatRecSuccCase h ih =>
      exact .natRec (par_refl _) (par_refl _) ih (par_refl _)
  | congNatRecScrutinee h ih =>
      exact .natRec (par_refl _) (par_refl _) (par_refl _) ih

theorem par_rename {n m : Nat} (ρ : Ren n m) {t u : PureTm n}
    (h : ParRed t u) : ParRed (rename ρ t) (rename ρ u) := by
  induction h generalizing m with
  | var i =>
      exact .var (ρ i)
  | u0 =>
      exact .u0
  | u1 =>
      exact .u1
  | unitTy =>
      exact .unitTy
  | unitMk =>
      exact .unitMk
  | boolTy =>
      exact .boolTy
  | boolFalse =>
      exact .boolFalse
  | boolTrue =>
      exact .boolTrue
  | natTy =>
      exact .natTy
  | natZero =>
      exact .natZero
  | natSucc hk ih =>
      simpa [rename] using .natSucc (ih (ρ := ρ))
  | pi hA hB ihA ihB =>
      simpa [rename] using .pi (ihA (ρ := ρ)) (ihB (ρ := liftRen ρ))
  | sigma hA hB ihA ihB =>
      simpa [rename] using .sigma (ihA (ρ := ρ)) (ihB (ρ := liftRen ρ))
  | id hA ha hb ihA iha ihb =>
      simpa [rename] using .id (ihA (ρ := ρ)) (iha (ρ := ρ)) (ihb (ρ := ρ))
  | lam hb ih =>
      simpa [rename] using .lam (ih (ρ := liftRen ρ))
  | app hf ha ihf iha =>
      simpa [rename] using .app (ihf (ρ := ρ)) (iha (ρ := ρ))
  | pair ha hb iha ihb =>
      simpa [rename] using .pair (iha (ρ := ρ)) (ihb (ρ := ρ))
  | fst hp ih =>
      simpa [rename] using .fst (ih (ρ := ρ))
  | snd hp ih =>
      simpa [rename] using .snd (ih (ρ := ρ))
  | refl ha ih =>
      simpa [rename] using .refl (ih (ρ := ρ))
  | unitRec hm hc hs ihm ihc ihs =>
      simpa [rename] using .unitRec (ihm (ρ := ρ)) (ihc (ρ := ρ)) (ihs (ρ := ρ))
  | boolRec hm hf ht hs ihm ihf iht ihs =>
      simpa [rename] using .boolRec (ihm (ρ := ρ)) (ihf (ρ := ρ)) (iht (ρ := ρ)) (ihs (ρ := ρ))
  | natRec hm hz hs hk ihm ihz ihs ihk =>
      simpa [rename] using .natRec (ihm (ρ := ρ)) (ihz (ρ := ρ)) (ihs (ρ := ρ)) (ihk (ρ := ρ))
  | betaPi hbody ha ihbody iha =>
      simpa [rename, rename_inst0] using
        (ParRed.betaPi (ihbody (ρ := liftRen ρ)) (iha (ρ := ρ)))
  | betaSigmaFst ha hb iha ihb =>
      simpa [rename] using
        (ParRed.betaSigmaFst (iha (ρ := ρ)) (ihb (ρ := ρ)))
  | betaSigmaSnd ha hb iha ihb =>
      simpa [rename] using
        (ParRed.betaSigmaSnd (iha (ρ := ρ)) (ihb (ρ := ρ)))
  | betaUnitRec hm hc ihm ihc =>
      simpa [rename] using
        (ParRed.betaUnitRec (ihm (ρ := ρ)) (ihc (ρ := ρ)))
  | betaBoolRecFalse hm hf ht ihm ihf iht =>
      simpa [rename] using
        (ParRed.betaBoolRecFalse (ihm (ρ := ρ)) (ihf (ρ := ρ)) (iht (ρ := ρ)))
  | betaBoolRecTrue hm hf ht ihm ihf iht =>
      simpa [rename] using
        (ParRed.betaBoolRecTrue (ihm (ρ := ρ)) (ihf (ρ := ρ)) (iht (ρ := ρ)))
  | betaNatRecZero hm hz hs ihm ihz ihs =>
      simpa [rename] using
        (ParRed.betaNatRecZero (ihm (ρ := ρ)) (ihz (ρ := ρ)) (ihs (ρ := ρ)))
  | betaNatRecSucc hm hz hs hk ihm ihz ihs ihk =>
      simpa [rename] using
        (ParRed.betaNatRecSucc (ihm (ρ := ρ)) (ihz (ρ := ρ)) (ihs (ρ := ρ)) (ihk (ρ := ρ)))

theorem par_subst {n m : Nat} {σ σ' : Sub n m}
    (hσ : ∀ i, ParRed (σ i) (σ' i))
    {t u : PureTm n} (h : ParRed t u) :
    ParRed (subst σ t) (subst σ' u) := by
  induction h generalizing m with
  | var i =>
      exact hσ i
  | u0 =>
      exact .u0
  | u1 =>
      exact .u1
  | unitTy =>
      exact .unitTy
  | unitMk =>
      exact .unitMk
  | boolTy =>
      exact .boolTy
  | boolFalse =>
      exact .boolFalse
  | boolTrue =>
      exact .boolTrue
  | natTy =>
      exact .natTy
  | natZero =>
      exact .natZero
  | natSucc hk ih =>
      simpa [subst] using .natSucc (ih hσ)
  | pi hA hB ihA ihB =>
      have hσlift : ∀ i, ParRed (liftSub σ i) (liftSub σ' i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact .var 0
        · intro j
          simpa [liftSub] using par_rename (ρ := wk) (hσ j)
      simpa [subst] using .pi (ihA hσ) (ihB hσlift)
  | sigma hA hB ihA ihB =>
      have hσlift : ∀ i, ParRed (liftSub σ i) (liftSub σ' i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact .var 0
        · intro j
          simpa [liftSub] using par_rename (ρ := wk) (hσ j)
      simpa [subst] using .sigma (ihA hσ) (ihB hσlift)
  | id hA ha hb ihA iha ihb =>
      simpa [subst] using .id (ihA hσ) (iha hσ) (ihb hσ)
  | lam hb ih =>
      have hσlift : ∀ i, ParRed (liftSub σ i) (liftSub σ' i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact .var 0
        · intro j
          simpa [liftSub] using par_rename (ρ := wk) (hσ j)
      simpa [subst] using .lam (ih hσlift)
  | app hf ha ihf iha =>
      simpa [subst] using .app (ihf hσ) (iha hσ)
  | pair ha hb iha ihb =>
      simpa [subst] using .pair (iha hσ) (ihb hσ)
  | fst hp ih =>
      simpa [subst] using .fst (ih hσ)
  | snd hp ih =>
      simpa [subst] using .snd (ih hσ)
  | refl ha ih =>
      simpa [subst] using .refl (ih hσ)
  | unitRec hm hc hs ihm ihc ihs =>
      simpa [subst] using .unitRec (ihm hσ) (ihc hσ) (ihs hσ)
  | boolRec hm hf ht hs ihm ihf iht ihs =>
      simpa [subst] using .boolRec (ihm hσ) (ihf hσ) (iht hσ) (ihs hσ)
  | natRec hm hz hs hk ihm ihz ihs ihk =>
      simpa [subst] using .natRec (ihm hσ) (ihz hσ) (ihs hσ) (ihk hσ)
  | betaPi hbody ha ihbody iha =>
      have hσlift : ∀ i, ParRed (liftSub σ i) (liftSub σ' i) := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact .var 0
        · intro j
          simpa [liftSub] using par_rename (ρ := wk) (hσ j)
      simpa [subst, subst_inst0] using (ParRed.betaPi (ihbody hσlift) (iha hσ))
  | betaSigmaFst ha hb iha ihb =>
      simpa [subst] using (ParRed.betaSigmaFst (iha hσ) (ihb hσ))
  | betaSigmaSnd ha hb iha ihb =>
      simpa [subst] using (ParRed.betaSigmaSnd (iha hσ) (ihb hσ))
  | betaUnitRec hm hc ihm ihc =>
      simpa [subst] using (ParRed.betaUnitRec (ihm hσ) (ihc hσ))
  | betaBoolRecFalse hm hf ht ihm ihf iht =>
      simpa [subst] using (ParRed.betaBoolRecFalse (ihm hσ) (ihf hσ) (iht hσ))
  | betaBoolRecTrue hm hf ht ihm ihf iht =>
      simpa [subst] using (ParRed.betaBoolRecTrue (ihm hσ) (ihf hσ) (iht hσ))
  | betaNatRecZero hm hz hs ihm ihz ihs =>
      simpa [subst] using (ParRed.betaNatRecZero (ihm hσ) (ihz hσ) (ihs hσ))
  | betaNatRecSucc hm hz hs hk ihm ihz ihs ihk =>
      simpa [subst] using (ParRed.betaNatRecSucc (ihm hσ) (ihz hσ) (ihs hσ) (ihk hσ))

theorem par_inst0 {a a' : PureTm n} {b b' : PureTm (n + 1)}
    (ha : ParRed a a') (hb : ParRed b b') :
    ParRed (inst0 a b) (inst0 a' b') := by
  have hσ : ∀ i, ParRed (subst0 a i) (subst0 a' i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using ha
    · intro j
      exact .var j
  simpa [inst0] using (par_subst (σ := subst0 a) (σ' := subst0 a') hσ hb)

theorem par_to_redStar {t u : PureTm n} (h : ParRed t u) : RedStar t u := by
  induction h with
  | var i =>
      exact .refl _
  | u0 =>
      exact .refl _
  | u1 =>
      exact .refl _
  | unitTy =>
      exact .refl _
  | unitMk =>
      exact .refl _
  | boolTy =>
      exact .refl _
  | boolFalse =>
      exact .refl _
  | boolTrue =>
      exact .refl _
  | natTy =>
      exact .refl _
  | natZero =>
      exact .refl _
  | natSucc hk ihk =>
      exact .congNatSucc ihk
  | pi hA hB ihA ihB =>
      exact .trans (.congPiDom ihA) (.congPiCod ihB)
  | sigma hA hB ihA ihB =>
      exact .trans (.congSigmaDom ihA) (.congSigmaCod ihB)
  | id hA ha hb ihA iha ihb =>
      exact .trans
        (.trans
          (RedStar.map (F := fun t => .id t _ _) (fun hstep => .congIdTy hstep) ihA)
          (RedStar.map (F := fun t => .id _ t _) (fun hstep => .congIdLeft hstep) iha))
        (RedStar.map (F := fun t => .id _ _ t) (fun hstep => .congIdRight hstep) ihb)
  | lam hb ih =>
      exact .congLam ih
  | app hf ha ihf iha =>
      exact .trans (.congAppFun ihf) (.congAppArg iha)
  | pair ha hb iha ihb =>
      exact .trans (.congPairFst iha) (.congPairSnd ihb)
  | fst hp ih =>
      exact .congFst ih
  | snd hp ih =>
      exact .congSnd ih
  | refl ha iha =>
      exact .congRefl iha
  | unitRec hm hc hs ihm ihc ihs =>
      exact .trans (.trans (.congUnitRecMotive ihm) (.congUnitRecCase ihc))
        (.congUnitRecScrutinee ihs)
  | boolRec hm hf ht hs ihm ihf iht ihs =>
      exact .trans
        (.trans
          (.trans (.congBoolRecMotive ihm) (.congBoolRecFalseCase ihf))
          (.congBoolRecTrueCase iht))
        (.congBoolRecScrutinee ihs)
  | natRec hm hz hs hk ihm ihz ihs ihk =>
      exact .trans
        (.trans
          (.trans (.congNatRecMotive ihm) (.congNatRecZeroCase ihz))
          (.congNatRecSuccCase ihs))
        (.congNatRecScrutinee ihk)
  | betaPi hb ha ihb iha =>
      exact .trans
        (.trans
          (.congAppFun (.congLam ihb))
          (.congAppArg iha))
        (red_to_redStar (.betaPi _ _))
  | betaSigmaFst ha hb iha ihb =>
      exact .trans
        (.trans
          (.congFst (.congPairFst iha))
          (.congFst (.congPairSnd ihb)))
        (red_to_redStar (.betaSigmaFst _ _))
  | betaSigmaSnd ha hb iha ihb =>
      exact .trans
        (.trans
          (.congSnd (.congPairFst iha))
          (.congSnd (.congPairSnd ihb)))
        (red_to_redStar (.betaSigmaSnd _ _))
  | betaUnitRec hm hc ihm ihc =>
      exact .trans
        (.trans (.congUnitRecMotive ihm) (.congUnitRecCase ihc))
        (red_to_redStar (.betaUnitRec _ _))
  | betaBoolRecFalse hm hf ht ihm ihf iht =>
      exact .trans
        (.trans
          (.trans (.congBoolRecMotive ihm) (.congBoolRecFalseCase ihf))
          (.congBoolRecTrueCase iht))
        (red_to_redStar (.betaBoolRecFalse _ _ _))
  | betaBoolRecTrue hm hf ht ihm ihf iht =>
      exact .trans
        (.trans
          (.trans (.congBoolRecMotive ihm) (.congBoolRecFalseCase ihf))
          (.congBoolRecTrueCase iht))
        (red_to_redStar (.betaBoolRecTrue _ _ _))
  | betaNatRecZero hm hz hs ihm ihz ihs =>
      exact .trans
        (.trans
          (.trans (.congNatRecMotive ihm) (.congNatRecZeroCase ihz))
          (.congNatRecSuccCase ihs))
        (red_to_redStar (.betaNatRecZero _ _ _))
  | betaNatRecSucc hm hz hs hk ihm ihz ihs ihk =>
      exact .trans
        (.trans
          (.trans
            (.trans (.congNatRecMotive ihm) (.congNatRecZeroCase ihz))
            (.congNatRecSuccCase ihs))
          (.congNatRecScrutinee (.congNatSucc ihk)))
        (red_to_redStar (.betaNatRecSucc _ _ _ _))

end Mettapedia.Languages.MeTTa.PureKernel.Parallel
