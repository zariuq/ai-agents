import Mettapedia.Logic.HOL.Syntax.Term

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Typed variable renamings. -/
abbrev Rename (Base : Type u) (Γ Δ : Ctx Base) := ∀ {τ}, Var Γ τ → Var Δ τ

/-- Typed substitutions. -/
abbrev Subst (Const : Ty Base → Type v) (Γ Δ : Ctx Base) := ∀ {τ}, Var Γ τ → Term Const Δ τ

namespace Rename

def id : Rename Base Γ Γ := fun v => v

def weaken : Rename Base Γ (σ :: Γ) := fun v => .vs v

def lift (ρ : Rename Base Γ Δ) : Rename Base (σ :: Γ) (σ :: Δ)
  | _, .vz => .vz
  | _, .vs v => .vs (ρ v)

@[simp] theorem lift_id_apply (v : Var (σ :: Γ) τ) :
    Rename.lift (Base := Base) (Γ := Γ) (Δ := Γ) (σ := σ)
      (Rename.id (Base := Base) (Γ := Γ)) v = v := by
  cases v <;> rfl

end Rename

/-- Rename variables in a term. -/
def rename (ρ : Rename Base Γ Δ) : Term Const Γ τ → Term Const Δ τ
  | .var v => .var (ρ v)
  | .const c => .const c
  | .app f t => .app (rename ρ f) (rename ρ t)
  | .lam t => .lam (rename (Rename.lift ρ) t)
  | .top => .top
  | .bot => .bot
  | .and φ ψ => .and (rename ρ φ) (rename ρ ψ)
  | .or φ ψ => .or (rename ρ φ) (rename ρ ψ)
  | .imp φ ψ => .imp (rename ρ φ) (rename ρ ψ)
  | .not φ => .not (rename ρ φ)
  | .eq t u => .eq (rename ρ t) (rename ρ u)
  | .all φ => .all (rename (Rename.lift ρ) φ)
  | .ex φ => .ex (rename (Rename.lift ρ) φ)

theorem rename_ext {ρ ρ' : Rename Base Γ Δ} (h : ∀ {τ}, (v : Var Γ τ) → ρ v = ρ' v)
    : (t : Term Const Γ τ) → rename ρ t = rename ρ' t
  | .var v => by
      simp [rename, h v]
  | .const _ => rfl
  | .app f t => by
      simp [rename, rename_ext h f, rename_ext h t]
  | .lam t => by
      apply congrArg Term.lam
      exact rename_ext
        (ρ := Rename.lift ρ)
        (ρ' := Rename.lift ρ')
        (fun v => by
          cases v with
          | vz => rfl
          | vs v => simp [Rename.lift, h v]) t
  | .top => rfl
  | .bot => rfl
  | .and φ ψ => by
      simp [rename, rename_ext h φ, rename_ext h ψ]
  | .or φ ψ => by
      simp [rename, rename_ext h φ, rename_ext h ψ]
  | .imp φ ψ => by
      simp [rename, rename_ext h φ, rename_ext h ψ]
  | .not φ => by
      simp [rename, rename_ext h φ]
  | .eq t u => by
      simp [rename, rename_ext h t, rename_ext h u]
  | .all φ => by
      apply congrArg Term.all
      exact rename_ext
        (ρ := Rename.lift ρ)
        (ρ' := Rename.lift ρ')
        (fun v => by
          cases v with
          | vz => rfl
          | vs v => simp [Rename.lift, h v]) φ
  | .ex φ => by
      apply congrArg Term.ex
      exact rename_ext
        (ρ := Rename.lift ρ)
        (ρ' := Rename.lift ρ')
        (fun v => by
          cases v with
          | vz => rfl
          | vs v => simp [Rename.lift, h v]) φ

namespace Subst

def id : Subst Const Γ Γ := fun v => .var v

def ofRename (ρ : Rename Base Γ Δ) : Subst Const Γ Δ :=
  fun v => .var (ρ v)

def lift (σs : Subst Const Γ Δ) : Subst Const (σ :: Γ) (σ :: Δ)
  | _, .vz => .var .vz
  | _, .vs v => rename (Rename.weaken (Base := Base) (Γ := Δ) (σ := σ)) (σs v)

def single (t : Term Const Γ σ) : Subst Const (σ :: Γ) Γ
  | _, .vz => t
  | _, .vs v => .var v

end Subst

/-- Substitute terms for variables. -/
def subst (σs : Subst Const Γ Δ) : Term Const Γ τ → Term Const Δ τ
  | .var v => σs v
  | .const c => .const c
  | .app f t => .app (subst σs f) (subst σs t)
  | .lam t => .lam (subst (Subst.lift (Base := Base) σs) t)
  | .top => .top
  | .bot => .bot
  | .and φ ψ => .and (subst σs φ) (subst σs ψ)
  | .or φ ψ => .or (subst σs φ) (subst σs ψ)
  | .imp φ ψ => .imp (subst σs φ) (subst σs ψ)
  | .not φ => .not (subst σs φ)
  | .eq t u => .eq (subst σs t) (subst σs u)
  | .all φ => .all (subst (Subst.lift (Base := Base) σs) φ)
  | .ex φ => .ex (subst (Subst.lift (Base := Base) σs) φ)

/-- Weaken a term by one variable. -/
def weaken (t : Term Const Γ τ) : Term Const (σ :: Γ) τ :=
  rename (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) t

/-- Instantiate the top bound variable with a term. -/
def instantiate (t : Term Const Γ σ) (u : Term Const (σ :: Γ) τ) : Term Const Γ τ :=
  subst (Subst.single t) u

namespace Subst

/-- Compose substitutions right-to-left: first `σs`, then `τs`. -/
def comp (τs : Subst Const Δ Ξ) (σs : Subst Const Γ Δ) : Subst Const Γ Ξ :=
  fun v => subst τs (σs v)

end Subst

theorem subst_ext {σs τs : Subst Const Γ Δ}
    (h : ∀ {τ}, (v : Var Γ τ) → σs v = τs v) :
    (t : Term Const Γ ρ) → subst σs t = subst τs t
  | .var v => by
      simp [subst, h v]
  | .const _ => rfl
  | .app f t => by
      simp [subst, subst_ext h f, subst_ext h t]
  | .lam t => by
      apply congrArg Term.lam
      exact subst_ext
        (σs := Subst.lift (Base := Base) σs)
        (τs := Subst.lift (Base := Base) τs)
        (fun v => by
          cases v with
          | vz => rfl
          | vs v => simp [Subst.lift, h v]) t
  | .top => rfl
  | .bot => rfl
  | .and φ ψ => by
      simp [subst, subst_ext h φ, subst_ext h ψ]
  | .or φ ψ => by
      simp [subst, subst_ext h φ, subst_ext h ψ]
  | .imp φ ψ => by
      simp [subst, subst_ext h φ, subst_ext h ψ]
  | .not φ => by
      simp [subst, subst_ext h φ]
  | .eq t u => by
      simp [subst, subst_ext h t, subst_ext h u]
  | .all φ => by
      apply congrArg Term.all
      exact subst_ext
        (σs := Subst.lift (Base := Base) σs)
        (τs := Subst.lift (Base := Base) τs)
        (fun v => by
          cases v with
          | vz => rfl
          | vs v => simp [Subst.lift, h v]) φ
  | .ex φ => by
      apply congrArg Term.ex
      exact subst_ext
        (σs := Subst.lift (Base := Base) σs)
        (τs := Subst.lift (Base := Base) τs)
        (fun v => by
          cases v with
          | vz => rfl
          | vs v => simp [Subst.lift, h v]) φ

@[simp] theorem rename_var (ρ : Rename Base Γ Δ) (v : Var Γ τ) :
    rename ρ (.var v : Term Const Γ τ) = .var (ρ v) := rfl

@[simp] theorem subst_var (σs : Subst Const Γ Δ) (v : Var Γ τ) :
    subst σs (.var v : Term Const Γ τ) = σs v := rfl

@[simp] theorem instantiate_var_vz (t : Term Const Γ σ) :
    instantiate t (.var (.vz : Var (σ :: Γ) σ)) = t := rfl

@[simp] theorem instantiate_var_vs (t : Term Const Γ σ) (v : Var Γ τ) :
    instantiate t (.var (.vs v) : Term Const (σ :: Γ) τ) = .var v := rfl

@[simp] theorem rename_comp (ρ₂ : Rename Base Δ Ξ) (ρ₁ : Rename Base Γ Δ)
    (t : Term Const Γ τ) :
    rename ρ₂ (rename ρ₁ t) = rename (fun {_τ} v => ρ₂ (ρ₁ v)) t := by
  induction t generalizing Δ Ξ with
  | var v =>
      rfl
  | const c =>
      rfl
  | app f t hf ht =>
      simp [rename, hf (ρ₂ := ρ₂) (ρ₁ := ρ₁), ht (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | lam t ih =>
      apply congrArg Term.lam
      calc
        rename
            (Rename.lift (Base := Base) (σ := _) ρ₂)
            (rename (Rename.lift (Base := Base) (σ := _) ρ₁) t)
            =
            rename
              (fun {τ} v =>
                Rename.lift (Base := Base) (σ := _) ρ₂
                  (Rename.lift (Base := Base) (σ := _) ρ₁ v)) t := by
                    exact ih
                      (ρ₂ := Rename.lift (Base := Base) (σ := _) ρ₂)
                      (ρ₁ := Rename.lift (Base := Base) (σ := _) ρ₁)
        _ =
            rename
              (Rename.lift (Base := Base) (σ := _)
                (fun {τ} v => ρ₂ (ρ₁ v))) t := by
                  apply rename_ext
                  intro τ v
                  cases v <;> rfl
  | top =>
      rfl
  | bot =>
      rfl
  | and φ ψ hφ hψ =>
      simp [rename, hφ (ρ₂ := ρ₂) (ρ₁ := ρ₁), hψ (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | or φ ψ hφ hψ =>
      simp [rename, hφ (ρ₂ := ρ₂) (ρ₁ := ρ₁), hψ (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | imp φ ψ hφ hψ =>
      simp [rename, hφ (ρ₂ := ρ₂) (ρ₁ := ρ₁), hψ (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | not φ hφ =>
      simp [rename, hφ (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | eq t u ht hu =>
      simp [rename, ht (ρ₂ := ρ₂) (ρ₁ := ρ₁), hu (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | all φ hφ =>
      apply congrArg Term.all
      calc
        rename
            (Rename.lift (Base := Base) (σ := _) ρ₂)
            (rename (Rename.lift (Base := Base) (σ := _) ρ₁) φ)
            =
            rename
              (fun {τ} v =>
                Rename.lift (Base := Base) (σ := _) ρ₂
                  (Rename.lift (Base := Base) (σ := _) ρ₁ v)) φ := by
                    exact hφ
                      (ρ₂ := Rename.lift (Base := Base) (σ := _) ρ₂)
                      (ρ₁ := Rename.lift (Base := Base) (σ := _) ρ₁)
        _ =
            rename
              (Rename.lift (Base := Base) (σ := _)
                (fun {τ} v => ρ₂ (ρ₁ v))) φ := by
                  apply rename_ext
                  intro τ v
                  cases v <;> rfl
  | ex φ hφ =>
      apply congrArg Term.ex
      calc
        rename
            (Rename.lift (Base := Base) (σ := _) ρ₂)
            (rename (Rename.lift (Base := Base) (σ := _) ρ₁) φ)
            =
            rename
              (fun {τ} v =>
                Rename.lift (Base := Base) (σ := _) ρ₂
                  (Rename.lift (Base := Base) (σ := _) ρ₁ v)) φ := by
                    exact hφ
                      (ρ₂ := Rename.lift (Base := Base) (σ := _) ρ₂)
                      (ρ₁ := Rename.lift (Base := Base) (σ := _) ρ₁)
        _ =
            rename
              (Rename.lift (Base := Base) (σ := _)
                (fun {τ} v => ρ₂ (ρ₁ v))) φ := by
                  apply rename_ext
                  intro τ v
                  cases v <;> rfl

@[simp] theorem rename_lift_apply (ρ : Rename Base Δ Ξ) (σs : Subst Const Γ Δ)
    (v : Var (σ :: Γ) τ) :
    rename (Rename.lift (Base := Base) (σ := σ) ρ)
        ((Subst.lift (Base := Base) (σ := σ) σs) v) =
      (Subst.lift (Base := Base) (Const := Const) (σ := σ)
        (fun {_τ} v => rename ρ (σs v))) v := by
  cases v with
  | vz =>
      rfl
  | vs v =>
      calc
        rename (Rename.lift (Base := Base) (σ := σ) ρ)
            ((Subst.lift (Base := Base) (σ := σ) σs) (.vs v))
            =
            rename
              (Rename.lift (Base := Base) (σ := σ) ρ)
              (rename (Rename.weaken (Base := Base) (Γ := Δ) (σ := σ)) (σs v)) := by
                rfl
        _ =
            rename
              (fun {τ} x =>
                Rename.lift (Base := Base) (σ := σ) ρ
                  (Rename.weaken (Base := Base) (Γ := Δ) (σ := σ) x))
              (σs v) := by
                simp [rename_comp]
        _ =
            rename
              (fun {τ} x =>
                Rename.weaken (Base := Base) (Γ := Ξ) (σ := σ) (ρ x))
              (σs v) := by
                apply rename_ext
                intro τ x
                simp [Rename.lift, Rename.weaken]
        _ =
            rename (Rename.weaken (Base := Base) (Γ := Ξ) (σ := σ))
              (rename ρ (σs v)) := by
                simp [rename_comp]
        _ = (Subst.lift (Base := Base) (Const := Const) (σ := σ)
              (fun {τ} v => rename ρ (σs v))) (.vs v) := by
                rfl

theorem rename_subst (ρ : Rename Base Δ Ξ) (σs : Subst Const Γ Δ)
    (t : Term Const Γ τ) :
    rename ρ (subst σs t) = subst (fun {_τ} v => rename ρ (σs v)) t := by
  induction t generalizing Δ Ξ with
  | var v =>
      rfl
  | const c =>
      rfl
  | app f t hf ht =>
      simp [rename, subst, hf (ρ := ρ) (σs := σs), ht (ρ := ρ) (σs := σs)]
  | lam t ih =>
      apply congrArg Term.lam
      calc
        rename
            (Rename.lift (Base := Base) (σ := _) ρ)
            (subst (Subst.lift (Base := Base) (σ := _) σs) t)
            =
            subst
              (fun {τ} v =>
                rename (Rename.lift (Base := Base) (σ := _) ρ)
                  ((Subst.lift (Base := Base) (σ := _) σs) v))
              t := by
                exact ih
                  (ρ := Rename.lift (Base := Base) (σ := _) ρ)
                  (σs := Subst.lift (Base := Base) (σ := _) σs)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const) (σ := _)
                (fun {τ} v => rename ρ (σs v))) t := by
                  apply subst_ext
                  intro τ v
                  exact rename_lift_apply (Base := Base) (Const := Const) (σ := _) ρ σs v
  | top =>
      rfl
  | bot =>
      rfl
  | and φ ψ hφ hψ =>
      simp [rename, subst, hφ (ρ := ρ) (σs := σs), hψ (ρ := ρ) (σs := σs)]
  | or φ ψ hφ hψ =>
      simp [rename, subst, hφ (ρ := ρ) (σs := σs), hψ (ρ := ρ) (σs := σs)]
  | imp φ ψ hφ hψ =>
      simp [rename, subst, hφ (ρ := ρ) (σs := σs), hψ (ρ := ρ) (σs := σs)]
  | not φ hφ =>
      simp [rename, subst, hφ (ρ := ρ) (σs := σs)]
  | eq t u ht hu =>
      simp [rename, subst, ht (ρ := ρ) (σs := σs), hu (ρ := ρ) (σs := σs)]
  | all φ hφ =>
      apply congrArg Term.all
      calc
        rename
            (Rename.lift (Base := Base) (σ := _) ρ)
            (subst (Subst.lift (Base := Base) (σ := _) σs) φ)
            =
            subst
              (fun {τ} v =>
                rename (Rename.lift (Base := Base) (σ := _) ρ)
                  ((Subst.lift (Base := Base) (σ := _) σs) v))
              φ := by
                exact hφ
                  (ρ := Rename.lift (Base := Base) (σ := _) ρ)
                  (σs := Subst.lift (Base := Base) (σ := _) σs)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const) (σ := _)
                (fun {τ} v => rename ρ (σs v))) φ := by
                  apply subst_ext
                  intro τ v
                  exact rename_lift_apply (Base := Base) (Const := Const) (σ := _) ρ σs v
  | ex φ hφ =>
      apply congrArg Term.ex
      calc
        rename
            (Rename.lift (Base := Base) (σ := _) ρ)
            (subst (Subst.lift (Base := Base) (σ := _) σs) φ)
            =
            subst
              (fun {τ} v =>
                rename (Rename.lift (Base := Base) (σ := _) ρ)
                  ((Subst.lift (Base := Base) (σ := _) σs) v))
              φ := by
                exact hφ
                  (ρ := Rename.lift (Base := Base) (σ := _) ρ)
                  (σs := Subst.lift (Base := Base) (σ := _) σs)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const) (σ := _)
                (fun {τ} v => rename ρ (σs v))) φ := by
                  apply subst_ext
                  intro τ v
                  exact rename_lift_apply (Base := Base) (Const := Const) (σ := _) ρ σs v

@[simp] theorem Subst.lift_rename_apply (σs : Subst Const Δ Ξ) (ρ : Rename Base Γ Δ)
    (v : Var (σ :: Γ) τ) :
    (Subst.lift (Base := Base) (σ := σ) σs)
        (Rename.lift (Base := Base) (σ := σ) ρ v) =
      (Subst.lift (Base := Base) (Const := Const) (σ := σ)
        (fun {_τ} v => σs (ρ v))) v := by
  cases v with
  | vz =>
      rfl
  | vs v =>
      rfl

theorem subst_rename (σs : Subst Const Δ Ξ) (ρ : Rename Base Γ Δ)
    (t : Term Const Γ τ) :
    subst σs (rename ρ t) = subst (fun {_τ} v => σs (ρ v)) t := by
  induction t generalizing Δ Ξ with
  | var v =>
      rfl
  | const c =>
      rfl
  | app f t hf ht =>
      simp [subst, rename, hf (σs := σs) (ρ := ρ), ht (σs := σs) (ρ := ρ)]
  | lam t ih =>
      apply congrArg Term.lam
      calc
        subst (Subst.lift (Base := Base) (σ := _) σs)
            (rename (Rename.lift (Base := Base) (σ := _) ρ) t)
            =
            subst
              (fun {τ} v =>
                (Subst.lift (Base := Base) (σ := _) σs)
                  (Rename.lift (Base := Base) (σ := _) ρ v))
              t := by
                exact ih
                  (σs := Subst.lift (Base := Base) (σ := _) σs)
                  (ρ := Rename.lift (Base := Base) (σ := _) ρ)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const) (σ := _)
                (fun {τ} v => σs (ρ v))) t := by
                  apply subst_ext
                  intro τ v
                  exact Subst.lift_rename_apply (Base := Base) (Const := Const) (σ := _) σs ρ v
  | top =>
      rfl
  | bot =>
      rfl
  | and φ ψ hφ hψ =>
      simp [subst, rename, hφ (σs := σs) (ρ := ρ), hψ (σs := σs) (ρ := ρ)]
  | or φ ψ hφ hψ =>
      simp [subst, rename, hφ (σs := σs) (ρ := ρ), hψ (σs := σs) (ρ := ρ)]
  | imp φ ψ hφ hψ =>
      simp [subst, rename, hφ (σs := σs) (ρ := ρ), hψ (σs := σs) (ρ := ρ)]
  | not φ hφ =>
      simp [subst, rename, hφ (σs := σs) (ρ := ρ)]
  | eq t u ht hu =>
      simp [subst, rename, ht (σs := σs) (ρ := ρ), hu (σs := σs) (ρ := ρ)]
  | all φ hφ =>
      apply congrArg Term.all
      calc
        subst (Subst.lift (Base := Base) (σ := _) σs)
            (rename (Rename.lift (Base := Base) (σ := _) ρ) φ)
            =
            subst
              (fun {τ} v =>
                (Subst.lift (Base := Base) (σ := _) σs)
                  (Rename.lift (Base := Base) (σ := _) ρ v))
              φ := by
                exact hφ
                  (σs := Subst.lift (Base := Base) (σ := _) σs)
                  (ρ := Rename.lift (Base := Base) (σ := _) ρ)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const) (σ := _)
                (fun {τ} v => σs (ρ v))) φ := by
                  apply subst_ext
                  intro τ v
                  exact Subst.lift_rename_apply (Base := Base) (Const := Const) (σ := _) σs ρ v
  | ex φ hφ =>
      apply congrArg Term.ex
      calc
        subst (Subst.lift (Base := Base) (σ := _) σs)
            (rename (Rename.lift (Base := Base) (σ := _) ρ) φ)
            =
            subst
              (fun {τ} v =>
                (Subst.lift (Base := Base) (σ := _) σs)
                  (Rename.lift (Base := Base) (σ := _) ρ v))
              φ := by
                exact hφ
                  (σs := Subst.lift (Base := Base) (σ := _) σs)
                  (ρ := Rename.lift (Base := Base) (σ := _) ρ)
        _ =
            subst
              (Subst.lift (Base := Base) (Const := Const) (σ := _)
                (fun {τ} v => σs (ρ v))) φ := by
                  apply subst_ext
                  intro τ v
                  exact Subst.lift_rename_apply (Base := Base) (Const := Const) (σ := _) σs ρ v

@[simp] theorem subst_weaken (σs : Subst Const Γ Δ) (t : Term Const Γ τ) :
    subst (Subst.lift (Base := Base) (σ := σ) σs)
        (weaken (Base := Base) (σ := σ) t) =
      weaken (Base := Base) (σ := σ) (subst σs t) := by
  calc
    subst (Subst.lift (Base := Base) (σ := σ) σs)
        (weaken (Base := Base) (σ := σ) t)
        =
        subst
          (fun {τ} v =>
            (Subst.lift (Base := Base) (σ := σ) σs)
              (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ) v))
          t := by
            simpa [weaken] using
              (subst_rename (Base := Base) (Const := Const)
                (σs := Subst.lift (Base := Base) (σ := σ) σs)
                (ρ := Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))
                (t := t))
    _ =
        subst
          (fun {τ} v =>
            weaken (Base := Base) (Const := Const) (σ := σ) (σs v))
          t := by
            rfl
    _ =
        rename (Rename.weaken (Base := Base) (Γ := Δ) (σ := σ)) (subst σs t) := by
          symm
          simpa [weaken] using
            (rename_subst (Base := Base) (Const := Const)
              (ρ := Rename.weaken (Base := Base) (Γ := Δ) (σ := σ))
              (σs := σs) (t := t))
    _ = weaken (Base := Base) (σ := σ) (subst σs t) := by
          rfl

@[simp] theorem Subst.comp_apply (τs : Subst Const Δ Ξ) (σs : Subst Const Γ Δ)
    (v : Var Γ τ) :
    Subst.comp τs σs v = subst τs (σs v) := rfl

@[simp] theorem Subst.lift_comp_apply (τs : Subst Const Δ Ξ) (σs : Subst Const Γ Δ)
    (v : Var (σ :: Γ) τ) :
    Subst.lift (Base := Base) (σ := σ) (Subst.comp τs σs) v =
      Subst.comp
        (Subst.lift (Base := Base) (σ := σ) τs)
        (Subst.lift (Base := Base) (σ := σ) σs) v := by
  cases v with
  | vz =>
      rfl
  | vs v =>
      simpa [Subst.comp, weaken] using
        (subst_weaken (Base := Base) (Const := Const) (σ := σ) (σs := τs) (t := σs v)).symm

theorem subst_comp (τs : Subst Const Δ Ξ) (σs : Subst Const Γ Δ)
    (t : Term Const Γ ρ) :
    subst τs (subst σs t) = subst (Subst.comp τs σs) t := by
  induction t generalizing Δ Ξ with
  | var v =>
      simp [Subst.comp]
  | const c =>
      rfl
  | app f t hf ht =>
      simp [subst, hf, ht]
  | lam t ih =>
      apply congrArg Term.lam
      calc
        subst (Subst.lift (Base := Base) (σ := _) τs)
            (subst (Subst.lift (Base := Base) (σ := _) σs) t)
            =
            subst
              (Subst.comp
                (Subst.lift (Base := Base) (σ := _) τs)
                (Subst.lift (Base := Base) (σ := _) σs)) t := by
                  exact ih (Subst.lift (Base := Base) τs) (Subst.lift (Base := Base) σs)
        _ =
            subst (Subst.lift (Base := Base) (σ := _) (Subst.comp τs σs)) t := by
              apply subst_ext
              intro τ v
              symm
              exact Subst.lift_comp_apply (Base := Base) (Const := Const) (σ := _) τs σs v
  | top =>
      rfl
  | bot =>
      rfl
  | and φ ψ hφ hψ =>
      simp [subst, hφ, hψ]
  | or φ ψ hφ hψ =>
      simp [subst, hφ, hψ]
  | imp φ ψ hφ hψ =>
      simp [subst, hφ, hψ]
  | not φ hφ =>
      simp [subst, hφ]
  | eq t u ht hu =>
      simp [subst, ht, hu]
  | all φ hφ =>
      apply congrArg Term.all
      calc
        subst (Subst.lift (Base := Base) (σ := _) τs)
            (subst (Subst.lift (Base := Base) (σ := _) σs) φ)
            =
            subst
              (Subst.comp
                (Subst.lift (Base := Base) (σ := _) τs)
                (Subst.lift (Base := Base) (σ := _) σs)) φ := by
                  exact hφ (Subst.lift (Base := Base) τs) (Subst.lift (Base := Base) σs)
        _ =
            subst (Subst.lift (Base := Base) (σ := _) (Subst.comp τs σs)) φ := by
              apply subst_ext
              intro τ v
              symm
              exact Subst.lift_comp_apply (Base := Base) (Const := Const) (σ := _) τs σs v
  | ex φ hφ =>
      apply congrArg Term.ex
      calc
        subst (Subst.lift (Base := Base) (σ := _) τs)
            (subst (Subst.lift (Base := Base) (σ := _) σs) φ)
            =
            subst
              (Subst.comp
                (Subst.lift (Base := Base) (σ := _) τs)
                (Subst.lift (Base := Base) (σ := _) σs)) φ := by
                  exact hφ (Subst.lift (Base := Base) τs) (Subst.lift (Base := Base) σs)
        _ =
            subst (Subst.lift (Base := Base) (σ := _) (Subst.comp τs σs)) φ := by
              apply subst_ext
              intro τ v
              symm
              exact Subst.lift_comp_apply (Base := Base) (Const := Const) (σ := _) τs σs v

theorem subst_id (t : Term Const Γ τ) :
    subst (Subst.id (Base := Base) (Const := Const) (Γ := Γ)) t = t := by
  induction t with
  | var v =>
      rfl
  | const c =>
      rfl
  | app f t hf ht =>
      simp [subst, hf, ht]
  | lam t ih =>
      apply congrArg Term.lam
      calc
        subst
            (Subst.lift (Base := Base) (σ := _)
              (Subst.id (Base := Base) (Const := Const) (Γ := _))) t
            =
            subst (Subst.id (Base := Base) (Const := Const) (Γ := _)) t := by
              apply subst_ext
              intro τ v
              cases v <;> rfl
        _ = t := ih
  | top =>
      rfl
  | bot =>
      rfl
  | and φ ψ hφ hψ =>
      simp [subst, hφ, hψ]
  | or φ ψ hφ hψ =>
      simp [subst, hφ, hψ]
  | imp φ ψ hφ hψ =>
      simp [subst, hφ, hψ]
  | not φ hφ =>
      simp [subst, hφ]
  | eq t u ht hu =>
      simp [subst, ht, hu]
  | all φ hφ =>
      apply congrArg Term.all
      calc
        subst
            (Subst.lift (Base := Base) (σ := _)
              (Subst.id (Base := Base) (Const := Const) (Γ := _))) φ
            =
            subst (Subst.id (Base := Base) (Const := Const) (Γ := _)) φ := by
              apply subst_ext
              intro τ v
              cases v <;> rfl
        _ = φ := hφ
  | ex φ hφ =>
      apply congrArg Term.ex
      calc
        subst
            (Subst.lift (Base := Base) (σ := _)
              (Subst.id (Base := Base) (Const := Const) (Γ := _))) φ
            =
            subst (Subst.id (Base := Base) (Const := Const) (Γ := _)) φ := by
              apply subst_ext
              intro τ v
              cases v <;> rfl
        _ = φ := hφ

@[simp] theorem instantiate_weaken
    (t : Term Const Γ σ) (u : Term Const Γ τ) :
    instantiate (Base := Base) t (weaken (Base := Base) (Γ := Γ) (σ := σ) u) = u := by
  unfold instantiate weaken
  calc
    subst
        (Subst.single (Base := Base) (Const := Const) t)
        (rename (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ)) u)
        =
        subst
          (fun {τ} v =>
            (Subst.single (Base := Base) (Const := Const) t)
              (Rename.weaken (Base := Base) (Γ := Γ) (σ := σ) v))
          u := by
            simpa using
              (subst_rename (Base := Base) (Const := Const)
                (σs := Subst.single (Base := Base) (Const := Const) t)
                (ρ := Rename.weaken (Base := Base) (Γ := Γ) (σ := σ))
                (t := u))
    _ =
        subst (Subst.id (Base := Base) (Const := Const) (Γ := Γ)) u := by
          apply subst_ext
          intro τ v
          rfl
    _ = u := subst_id (Base := Base) (Const := Const) u

theorem rename_id (t : Term Const Γ τ) :
    rename (Rename.id (Base := Base) (Γ := Γ)) t = t := by
  induction t with
  | var v =>
      rfl
  | const c =>
      rfl
  | app f t hf ht =>
      simp [rename, hf, ht]
  | lam t ih =>
      apply congrArg Term.lam
      calc
        rename
            (Rename.lift (Base := Base) (Γ := _) (Δ := _) (σ := _)
              (Rename.id (Base := Base) (Γ := _))) t
            =
            rename (Rename.id (Base := Base) (Γ := _)) t := by
              apply rename_ext
              intro τ v
              exact Rename.lift_id_apply (Base := Base) (Γ := _) (σ := _) v
        _ = t := ih
  | top =>
      rfl
  | bot =>
      rfl
  | and φ ψ hφ hψ =>
      simp [rename, hφ, hψ]
  | or φ ψ hφ hψ =>
      simp [rename, hφ, hψ]
  | imp φ ψ hφ hψ =>
      simp [rename, hφ, hψ]
  | not φ hφ =>
      simp [rename, hφ]
  | eq t u ht hu =>
      simp [rename, ht, hu]
  | all φ ih =>
      apply congrArg Term.all
      calc
        rename
            (Rename.lift (Base := Base) (Γ := _) (Δ := _) (σ := _)
              (Rename.id (Base := Base) (Γ := _))) φ
            =
            rename (Rename.id (Base := Base) (Γ := _)) φ := by
              apply rename_ext
              intro τ v
              exact Rename.lift_id_apply (Base := Base) (Γ := _) (σ := _) v
        _ = φ := ih
  | ex φ ih =>
      apply congrArg Term.ex
      calc
        rename
            (Rename.lift (Base := Base) (Γ := _) (Δ := _) (σ := _)
              (Rename.id (Base := Base) (Γ := _))) φ
            =
            rename (Rename.id (Base := Base) (Γ := _)) φ := by
              apply rename_ext
              intro τ v
              exact Rename.lift_id_apply (Base := Base) (Γ := _) (σ := _) v
        _ = φ := ih

end Mettapedia.Logic.HOL
