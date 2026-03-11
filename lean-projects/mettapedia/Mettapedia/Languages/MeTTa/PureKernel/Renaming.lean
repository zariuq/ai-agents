import Mettapedia.Languages.MeTTa.PureKernel.Syntax

namespace Mettapedia.Languages.MeTTa.PureKernel.Renaming

open Mettapedia.Languages.MeTTa.PureKernel.Syntax

abbrev Ren (n m : Nat) := Fin n → Fin m

def idRen : Ren n n := fun i => i

def wk : Ren n (n + 1) := Fin.succ

def liftRen (ρ : Ren n m) : Ren (n + 1) (m + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

def rename (ρ : Ren n m) : PureTm n → PureTm m
  | .var i => .var (ρ i)
  | .u0 => .u0
  | .u1 => .u1
  | .unitTy => .unitTy
  | .unitMk => .unitMk
  | .boolTy => .boolTy
  | .boolFalse => .boolFalse
  | .boolTrue => .boolTrue
  | .natTy => .natTy
  | .natZero => .natZero
  | .natSucc k => .natSucc (rename ρ k)
  | .pi A B => .pi (rename ρ A) (rename (liftRen ρ) B)
  | .sigma A B => .sigma (rename ρ A) (rename (liftRen ρ) B)
  | .id A a b => .id (rename ρ A) (rename ρ a) (rename ρ b)
  | .lam b => .lam (rename (liftRen ρ) b)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .pair a b => .pair (rename ρ a) (rename ρ b)
  | .fst p => .fst (rename ρ p)
  | .snd p => .snd (rename ρ p)
  | .refl a => .refl (rename ρ a)
  | .unitRec motive unitCase scrutinee =>
      .unitRec (rename ρ motive) (rename ρ unitCase) (rename ρ scrutinee)
  | .boolRec motive falseCase trueCase scrutinee =>
      .boolRec (rename ρ motive) (rename ρ falseCase) (rename ρ trueCase) (rename ρ scrutinee)
  | .natRec motive zeroCase succCase scrutinee =>
      .natRec (rename ρ motive) (rename ρ zeroCase) (rename ρ succCase) (rename ρ scrutinee)

@[simp] theorem liftRen_id : liftRen (idRen (n := n)) = idRen := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

@[simp] theorem liftRen_comp_apply (ρ₂ : Ren m k) (ρ₁ : Ren n m) (i : Fin (n + 1)) :
    liftRen ρ₂ (liftRen ρ₁ i) = liftRen (fun j => ρ₂ (ρ₁ j)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

@[simp] theorem liftRen_ext {ρ ξ : Ren n m} (hρ : ∀ i, ρ i = ξ i) :
    ∀ i : Fin (n + 1), liftRen ρ i = liftRen ξ i := by
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp [liftRen, hρ j]

theorem rename_ext {ρ ξ : Ren n m} (hρ : ∀ i, ρ i = ξ i) :
    ∀ t : PureTm n, rename ρ t = rename ξ t := by
  intro t
  induction t generalizing m with
  | var i =>
    simp [rename, hρ i]
  | u0 =>
    rfl
  | u1 =>
    rfl
  | unitTy =>
    rfl
  | unitMk =>
    rfl
  | boolTy =>
    rfl
  | boolFalse =>
    rfl
  | boolTrue =>
    rfl
  | natTy =>
    rfl
  | natZero =>
    rfl
  | natSucc k ih =>
    simp [rename, ih (ρ := ρ) (ξ := ξ) hρ]
  | pi A B ihA ihB =>
    simp [rename, ihA (ρ := ρ) (ξ := ξ) hρ]
    exact ihB (ρ := liftRen ρ) (ξ := liftRen ξ) (liftRen_ext hρ)
  | sigma A B ihA ihB =>
    simp [rename, ihA (ρ := ρ) (ξ := ξ) hρ]
    exact ihB (ρ := liftRen ρ) (ξ := liftRen ξ) (liftRen_ext hρ)
  | id A a b ihA iha ihb =>
    simp [rename, ihA (ρ := ρ) (ξ := ξ) hρ, iha (ρ := ρ) (ξ := ξ) hρ,
      ihb (ρ := ρ) (ξ := ξ) hρ]
  | lam b ih =>
    simp [rename]
    exact ih (ρ := liftRen ρ) (ξ := liftRen ξ) (liftRen_ext hρ)
  | app f a ihf iha =>
    simp [rename, ihf (ρ := ρ) (ξ := ξ) hρ, iha (ρ := ρ) (ξ := ξ) hρ]
  | pair a b iha ihb =>
    simp [rename, iha (ρ := ρ) (ξ := ξ) hρ, ihb (ρ := ρ) (ξ := ξ) hρ]
  | fst p ih =>
    simpa [rename] using ih (ρ := ρ) (ξ := ξ) hρ
  | snd p ih =>
    simpa [rename] using ih (ρ := ρ) (ξ := ξ) hρ
  | refl a iha =>
    simpa [rename] using iha (ρ := ρ) (ξ := ξ) hρ
  | unitRec motive unitCase scrutinee ihmotive ihcase ihscrutinee =>
    simp [rename, ihmotive (ρ := ρ) (ξ := ξ) hρ, ihcase (ρ := ρ) (ξ := ξ) hρ,
      ihscrutinee (ρ := ρ) (ξ := ξ) hρ]
  | boolRec motive falseCase trueCase scrutinee ihmotive ihFalse ihTrue ihscrutinee =>
    simp [rename, ihmotive (ρ := ρ) (ξ := ξ) hρ, ihFalse (ρ := ρ) (ξ := ξ) hρ,
      ihTrue (ρ := ρ) (ξ := ξ) hρ, ihscrutinee (ρ := ρ) (ξ := ξ) hρ]
  | natRec motive zeroCase succCase scrutinee ihmotive ihZero ihSucc ihscrutinee =>
    simp [rename, ihmotive (ρ := ρ) (ξ := ξ) hρ, ihZero (ρ := ρ) (ξ := ξ) hρ,
      ihSucc (ρ := ρ) (ξ := ξ) hρ, ihscrutinee (ρ := ρ) (ξ := ξ) hρ]

@[simp] theorem rename_id : ∀ t : PureTm n, rename idRen t = t := by
  intro t
  induction t with
  | var i =>
    rfl
  | u0 =>
    rfl
  | u1 =>
    rfl
  | unitTy =>
    rfl
  | unitMk =>
    rfl
  | boolTy =>
    rfl
  | boolFalse =>
    rfl
  | boolTrue =>
    rfl
  | natTy =>
    rfl
  | natZero =>
    rfl
  | natSucc k ih =>
    simp [rename, ih]
  | pi A B ihA ihB =>
    simp [rename, ihA, ihB]
  | sigma A B ihA ihB =>
    simp [rename, ihA, ihB]
  | id A a b ihA iha ihb =>
    simp [rename, ihA, iha, ihb]
  | lam b ih =>
    simp [rename, ih]
  | app f a ihf iha =>
    simp [rename, ihf, iha]
  | pair a b iha ihb =>
    simp [rename, iha, ihb]
  | fst p ih =>
    simp [rename, ih]
  | snd p ih =>
    simp [rename, ih]
  | refl a iha =>
    simp [rename, iha]
  | unitRec motive unitCase scrutinee ihmotive ihcase ihscrutinee =>
    simp [rename, ihmotive, ihcase, ihscrutinee]
  | boolRec motive falseCase trueCase scrutinee ihmotive ihFalse ihTrue ihscrutinee =>
    simp [rename, ihmotive, ihFalse, ihTrue, ihscrutinee]
  | natRec motive zeroCase succCase scrutinee ihmotive ihZero ihSucc ihscrutinee =>
    simp [rename, ihmotive, ihZero, ihSucc, ihscrutinee]

@[simp] theorem rename_comp :
    ∀ {n m k} (ρ₂ : Ren m k) (ρ₁ : Ren n m) (t : PureTm n),
      rename ρ₂ (rename ρ₁ t) = rename (fun i => ρ₂ (ρ₁ i)) t := by
  intro n m k ρ₂ ρ₁ t
  induction t generalizing m k ρ₂ with
  | var i =>
    rfl
  | u0 =>
    rfl
  | u1 =>
    rfl
  | unitTy =>
    rfl
  | unitMk =>
    rfl
  | boolTy =>
    rfl
  | boolFalse =>
    rfl
  | boolTrue =>
    rfl
  | natTy =>
    rfl
  | natZero =>
    rfl
  | natSucc k ih =>
    simp [rename, ih (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | pi A B ihA ihB =>
    simp [rename, ihA (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
    calc
      rename (liftRen ρ₂) (rename (liftRen ρ₁) B)
          = rename (fun i => liftRen ρ₂ (liftRen ρ₁ i)) B := by
              simpa using ihB (ρ₂ := liftRen ρ₂) (ρ₁ := liftRen ρ₁)
      _ = rename (liftRen (fun i => ρ₂ (ρ₁ i))) B := by
            exact rename_ext
              (ρ := fun i => liftRen ρ₂ (liftRen ρ₁ i))
              (ξ := liftRen (fun i => ρ₂ (ρ₁ i)))
              (fun i => liftRen_comp_apply ρ₂ ρ₁ i)
              B
  | sigma A B ihA ihB =>
    simp [rename, ihA (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
    calc
      rename (liftRen ρ₂) (rename (liftRen ρ₁) B)
          = rename (fun i => liftRen ρ₂ (liftRen ρ₁ i)) B := by
              simpa using ihB (ρ₂ := liftRen ρ₂) (ρ₁ := liftRen ρ₁)
      _ = rename (liftRen (fun i => ρ₂ (ρ₁ i))) B := by
            exact rename_ext
              (ρ := fun i => liftRen ρ₂ (liftRen ρ₁ i))
              (ξ := liftRen (fun i => ρ₂ (ρ₁ i)))
              (fun i => liftRen_comp_apply ρ₂ ρ₁ i)
              B
  | id A a b ihA iha ihb =>
    simp [rename, ihA (ρ₂ := ρ₂) (ρ₁ := ρ₁), iha (ρ₂ := ρ₂) (ρ₁ := ρ₁),
      ihb (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | lam b ih =>
    simp [rename]
    calc
      rename (liftRen ρ₂) (rename (liftRen ρ₁) b)
          = rename (fun i => liftRen ρ₂ (liftRen ρ₁ i)) b := by
              simpa using ih (ρ₂ := liftRen ρ₂) (ρ₁ := liftRen ρ₁)
      _ = rename (liftRen (fun i => ρ₂ (ρ₁ i))) b := by
            exact rename_ext
              (ρ := fun i => liftRen ρ₂ (liftRen ρ₁ i))
              (ξ := liftRen (fun i => ρ₂ (ρ₁ i)))
              (fun i => liftRen_comp_apply ρ₂ ρ₁ i)
              b
  | app f a ihf iha =>
    simp [rename, ihf (ρ₂ := ρ₂) (ρ₁ := ρ₁), iha (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | pair a b iha ihb =>
    simp [rename, iha (ρ₂ := ρ₂) (ρ₁ := ρ₁), ihb (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | fst p ih =>
    simpa [rename] using ih (ρ₂ := ρ₂) (ρ₁ := ρ₁)
  | snd p ih =>
    simpa [rename] using ih (ρ₂ := ρ₂) (ρ₁ := ρ₁)
  | refl a iha =>
    simpa [rename] using iha (ρ₂ := ρ₂) (ρ₁ := ρ₁)
  | unitRec motive unitCase scrutinee ihmotive ihcase ihscrutinee =>
    simp [rename, ihmotive (ρ₂ := ρ₂) (ρ₁ := ρ₁), ihcase (ρ₂ := ρ₂) (ρ₁ := ρ₁),
      ihscrutinee (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | boolRec motive falseCase trueCase scrutinee ihmotive ihFalse ihTrue ihscrutinee =>
    simp [rename, ihmotive (ρ₂ := ρ₂) (ρ₁ := ρ₁), ihFalse (ρ₂ := ρ₂) (ρ₁ := ρ₁),
      ihTrue (ρ₂ := ρ₂) (ρ₁ := ρ₁), ihscrutinee (ρ₂ := ρ₂) (ρ₁ := ρ₁)]
  | natRec motive zeroCase succCase scrutinee ihmotive ihZero ihSucc ihscrutinee =>
    simp [rename, ihmotive (ρ₂ := ρ₂) (ρ₁ := ρ₁), ihZero (ρ₂ := ρ₂) (ρ₁ := ρ₁),
      ihSucc (ρ₂ := ρ₂) (ρ₁ := ρ₁), ihscrutinee (ρ₂ := ρ₂) (ρ₁ := ρ₁)]

end Mettapedia.Languages.MeTTa.PureKernel.Renaming
