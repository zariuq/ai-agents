import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzApplicativeFragment

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

namespace ApplicativeTerm

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Δ : Ctx Base} {τ υ : Ty Base}

/-- Rename the free variables of an applicative-fragment term. -/
def rename :
    {Γ Δ : Ctx Base} → {τ : Ty Base} →
      Rename Base Γ Δ →
      ApplicativeTerm Base Const Γ τ → ApplicativeTerm Base Const Δ τ
  | _, _, _, ρ, .var v => .var (ρ v)
  | _, _, _, _, .const c => .const c
  | _, _, _, ρ, .app f t => .app (rename ρ f) (rename ρ t)
  | _, _, _, ρ, .lam t => .lam (rename (Rename.lift (Base := Base) (σ := _) ρ) t)

@[simp] theorem rename_var (ρ : Rename Base Γ Δ) (v : Var Γ τ) :
    rename ρ (.var v : ApplicativeTerm Base Const Γ τ) = .var (ρ v) :=
  rfl

@[simp] theorem rename_const (ρ : Rename Base Γ Δ) (c : Const τ) :
    rename ρ (.const c : ApplicativeTerm Base Const Γ τ) = .const c :=
  rfl

@[simp] theorem rename_app (ρ : Rename Base Γ Δ)
    (f : ApplicativeTerm Base Const Γ (υ ⇒ τ))
    (t : ApplicativeTerm Base Const Γ υ) :
    rename ρ (.app f t : ApplicativeTerm Base Const Γ τ) =
      .app (rename ρ f) (rename ρ t) :=
  rfl

@[simp] theorem rename_lam (ρ : Rename Base Γ Δ)
    (t : ApplicativeTerm Base Const (υ :: Γ) τ) :
    rename ρ (.lam t : ApplicativeTerm Base Const Γ (υ ⇒ τ)) =
      .lam (rename (Rename.lift (Base := Base) (σ := υ) ρ) t) :=
  rfl

@[simp] theorem toTerm_rename (ρ : Rename Base Γ Δ)
    (t : ApplicativeTerm Base Const Γ τ) :
    toTerm (rename ρ t) =
      Mettapedia.AutoBooks.Codex.IntuitionisticHOL.rename ρ (toTerm t) := by
  induction t generalizing Δ with
  | var v =>
      rfl
  | const c =>
      rfl
  | app f t ihf iht =>
      simpa [rename, toTerm, Mettapedia.AutoBooks.Codex.IntuitionisticHOL.rename] using
        congrArg₂ Term.app (ihf ρ) (iht ρ)
  | lam t ih =>
      simpa [rename, toTerm, Mettapedia.AutoBooks.Codex.IntuitionisticHOL.rename] using
        congrArg Term.lam
          (ih (ρ := Rename.lift (Base := Base) (σ := _) ρ))

/-- Weaken an applicative-fragment term by one new head variable. -/
def weaken (t : ApplicativeTerm Base Const Γ τ) : ApplicativeTerm Base Const (υ :: Γ) τ :=
  rename (Rename.weaken (Base := Base) (Γ := Γ) (σ := υ)) t

@[simp] theorem toTerm_weaken (t : ApplicativeTerm Base Const Γ τ) :
    toTerm (weaken (υ := υ) t) =
      Mettapedia.AutoBooks.Codex.IntuitionisticHOL.weaken
        (Base := Base) (Const := Const) (σ := υ) (toTerm t) := by
  rw [ApplicativeTerm.weaken, Mettapedia.AutoBooks.Codex.IntuitionisticHOL.weaken]
  exact toTerm_rename
    (Base := Base) (Const := Const)
    (Γ := Γ) (Δ := υ :: Γ) (τ := τ)
    (ρ := Rename.weaken (Base := Base) (Γ := Γ) (σ := υ)) t

end ApplicativeTerm

/--
An archive-free higher-order substitution into the applicative fragment.
-/
abbrev ApplicativeSubst (Base : Type u) (Const : Ty Base → Type v)
    (Γ Δ : Ctx Base) : Type (max u v) :=
  {τ : Ty Base} → Var Γ τ → ApplicativeTerm Base Const Δ τ

namespace ApplicativeSubst

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Δ : Ctx Base} {τ υ : Ty Base}

/-- Identity applicative substitution. -/
def id : ApplicativeSubst Base Const Γ Γ := fun x => .var x

/-- Drop the head component of an applicative substitution. -/
def tail (σs : ApplicativeSubst Base Const (τ :: Γ) Δ) :
    ApplicativeSubst Base Const Γ Δ :=
  fun x => σs (.vs x)

/-- Extend an applicative substitution by a term for the new head variable. -/
def cons (t : ApplicativeTerm Base Const Δ τ)
    (σs : ApplicativeSubst Base Const Γ Δ) :
    ApplicativeSubst Base Const (τ :: Γ) Δ
  | _, .vz => t
  | _, .vs x => σs x

/-- Lift an applicative substitution under one additional binder. -/
def lift (σs : ApplicativeSubst Base Const Γ Δ) :
    ApplicativeSubst Base Const (υ :: Γ) (υ :: Δ) :=
  cons (.var (.vz : Var (υ :: Δ) υ))
    (fun x => ApplicativeTerm.weaken (υ := υ) (σs x))

@[simp] theorem id_apply (x : Var Γ τ) :
    id (Base := Base) (Const := Const) x = .var x :=
  rfl

@[simp] theorem tail_cons (t : ApplicativeTerm Base Const Δ τ)
    (σs : ApplicativeSubst Base Const Γ Δ) (x : Var Γ υ) :
    tail (cons t σs) x = σs x :=
  rfl

@[simp] theorem cons_vz (t : ApplicativeTerm Base Const Δ τ)
    (σs : ApplicativeSubst Base Const Γ Δ) :
    cons t σs (Var.vz : Var (τ :: Γ) τ) = t :=
  rfl

@[simp] theorem cons_vs (t : ApplicativeTerm Base Const Δ τ)
    (σs : ApplicativeSubst Base Const Γ Δ) (x : Var Γ υ) :
    cons t σs (.vs x) = σs x :=
  rfl

@[simp] theorem lift_vz (σs : ApplicativeSubst Base Const Γ Δ) :
    lift (υ := υ) σs (Var.vz : Var (υ :: Γ) υ) =
      (.var (Var.vz : Var (υ :: Δ) υ) : ApplicativeTerm Base Const (υ :: Δ) υ) :=
  rfl

@[simp] theorem lift_vs (σs : ApplicativeSubst Base Const Γ Δ) (x : Var Γ τ) :
    lift (υ := υ) σs (.vs x) =
      ApplicativeTerm.weaken (υ := υ) (σs x) :=
  rfl

@[simp] theorem lift_id_apply
    (v : Var (υ :: Γ) τ) :
    lift (Base := Base) (Const := Const) (Γ := Γ) (Δ := Γ) (υ := υ)
      (id (Base := Base) (Const := Const) (Γ := Γ)) v =
      (.var v : ApplicativeTerm Base Const (υ :: Γ) τ) := by
  cases v with
  | vz =>
      rfl
  | vs x =>
      simp [lift, id, ApplicativeTerm.weaken, Rename.weaken]

/-- Translate an applicative substitution into the native HOL substitution type. -/
def toSubst (σs : ApplicativeSubst Base Const Γ Δ) :
    Mettapedia.Logic.HOL.Subst Const Γ Δ :=
  fun x => ApplicativeTerm.toTerm (σs x)

@[simp] theorem toSubst_apply (σs : ApplicativeSubst Base Const Γ Δ) (x : Var Γ τ) :
    toSubst σs x = ApplicativeTerm.toTerm (σs x) :=
  rfl

@[simp] theorem toSubst_lift_apply (σs : ApplicativeSubst Base Const Γ Δ)
    {ρ : Ty Base} (x : Var (υ :: Γ) ρ) :
    toSubst (lift (υ := υ) σs) x =
      Mettapedia.Logic.HOL.Subst.lift
        (Base := Base) (Const := Const) (σ := υ) (toSubst σs) x := by
  cases x with
  | vz =>
      rfl
  | vs x =>
      change ApplicativeTerm.toTerm (ApplicativeTerm.weaken (υ := υ) (σs x)) =
        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.rename
          (Rename.weaken (Base := Base) (Γ := Δ) (σ := υ))
          (ApplicativeTerm.toTerm (σs x))
      exact ApplicativeTerm.toTerm_weaken
        (Base := Base) (Const := Const) (Γ := Δ) (τ := ρ) (υ := υ) (t := σs x)

end ApplicativeSubst

namespace ApplicativeTerm

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Δ : Ctx Base} {τ : Ty Base}

/-- Substitute applicative-fragment terms for the free variables of a term. -/
def subst :
    {Γ Δ : Ctx Base} → {τ : Ty Base} →
      ApplicativeSubst Base Const Γ Δ →
      ApplicativeTerm Base Const Γ τ → ApplicativeTerm Base Const Δ τ
  | _, _, _, σs, .var v => σs v
  | _, _, _, _, .const c => .const c
  | _, _, _, σs, .app f t => .app (subst σs f) (subst σs t)
  | _, _, _, σs, .lam t => .lam (subst (ApplicativeSubst.lift σs) t)

theorem subst_ext
    (σs τs : ApplicativeSubst Base Const Γ Δ)
    (h : ∀ {ρ : Ty Base} (v : Var Γ ρ), σs v = τs v)
    (t : ApplicativeTerm Base Const Γ τ) :
    subst σs t = subst τs t := by
  induction t generalizing Δ with
  | var v =>
      simpa [subst] using h v
  | const c =>
      rfl
  | app f t ihf iht =>
      exact congrArg₂ ApplicativeTerm.app (ihf (@σs) (@τs) h) (iht (@σs) (@τs) h)
  | lam t ih =>
      apply congrArg ApplicativeTerm.lam
      exact ih
        (Δ := _ :: Δ)
        (ApplicativeSubst.lift (υ := _) (@σs))
        (ApplicativeSubst.lift (υ := _) (@τs))
        (fun v => by
          cases v with
          | vz =>
              rfl
          | vs w =>
              simpa using congrArg (ApplicativeTerm.weaken (υ := _)) (h w))

@[simp] theorem subst_var (σs : ApplicativeSubst Base Const Γ Δ) (v : Var Γ τ) :
    subst σs (.var v : ApplicativeTerm Base Const Γ τ) = σs v :=
  rfl

@[simp] theorem subst_const (σs : ApplicativeSubst Base Const Γ Δ) (c : Const τ) :
    subst σs (.const c : ApplicativeTerm Base Const Γ τ) = .const c :=
  rfl

@[simp] theorem subst_app
    (σs : ApplicativeSubst Base Const Γ Δ)
    (f : ApplicativeTerm Base Const Γ (σ ⇒ τ))
    (t : ApplicativeTerm Base Const Γ σ) :
    subst σs (.app f t : ApplicativeTerm Base Const Γ τ) =
      .app (subst σs f) (subst σs t) :=
  rfl

@[simp] theorem subst_lam
    (σs : ApplicativeSubst Base Const Γ Δ)
    (t : ApplicativeTerm Base Const (σ :: Γ) τ) :
    subst σs (.lam t : ApplicativeTerm Base Const Γ (σ ⇒ τ)) =
      .lam (subst (ApplicativeSubst.lift (υ := σ) σs) t) :=
  rfl

@[simp] theorem subst_id (t : ApplicativeTerm Base Const Γ τ) :
    subst (ApplicativeSubst.id (Base := Base) (Const := Const) (Γ := Γ)) t = t := by
  induction t with
  | var v =>
      rfl
  | const c =>
      rfl
  | app f t ihf iht =>
      simp [subst, ihf, iht]
  | lam t iht =>
      apply congrArg ApplicativeTerm.lam
      calc
        subst
            (ApplicativeSubst.lift (υ := _)
              (ApplicativeSubst.id (Base := Base) (Const := Const) (Γ := _))) t
            =
          subst (ApplicativeSubst.id (Base := Base) (Const := Const) (Γ := _)) t := by
            apply subst_ext
            intro ρ v
            cases v <;> rfl
        _ = t := by
          simpa using iht

@[simp] theorem toTerm_subst (σs : ApplicativeSubst Base Const Γ Δ)
    (t : ApplicativeTerm Base Const Γ τ) :
    toTerm (subst σs t) =
      Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
        (ApplicativeSubst.toSubst σs) (toTerm t) := by
  induction t generalizing Δ with
  | var v =>
      rfl
  | const c =>
      rfl
  | app f t ihf iht =>
      simpa [subst, toTerm, Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst] using
        congrArg₂ Term.app (ihf σs) (iht σs)
  | lam t ih =>
      apply congrArg Term.lam
      rw [ih (σs := ApplicativeSubst.lift σs)]
      apply Mettapedia.Logic.HOL.subst_ext
      intro ρ v
      exact ApplicativeSubst.toSubst_lift_apply (σs := σs) v

end ApplicativeTerm

namespace HigherOrderPointTopologicalGlobalModelBridge

namespace basicInterp

variable {Base : Type u} {Const : Ty Base → Type v}
variable (M : GlobalModel Base Const)

namespace ApplicativeTopologicalInterpretation

end ApplicativeTopologicalInterpretation

end basicInterp

end HigherOrderPointTopologicalGlobalModelBridge

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
