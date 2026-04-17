import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzPropositionalProofBridge
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Models
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Soundness

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

namespace SimplePropFormula

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Δ : List (SimpleTy Base)}

/--
Direct semilocal-model evaluation for the live simple propositional fragment,
stated on the native HOL side after translation of contexts and atoms.
-/
def semilocalTruth (M : SemilocalModel Base Const)
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx Γ)) :
    SimplePropFormula Base Const Γ → M.Omega
  | .atom t => SemilocalModel.formulaTruth M ρ (SimpleTerm.toTerm t)
  | .top => ⊤
  | .bot => ⊥
  | .conj φ ψ => semilocalTruth M ρ φ ⊓ semilocalTruth M ρ ψ
  | .disj φ ψ => semilocalTruth M ρ φ ⊔ semilocalTruth M ρ ψ
  | .impl φ ψ => semilocalTruth M ρ φ ⇨ semilocalTruth M ρ ψ

@[simp] theorem semilocalTruth_atom (M : SemilocalModel Base Const)
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx Γ))
    (t : SimpleTerm Base Const Γ .prop) :
    semilocalTruth M ρ (.atom t : SimplePropFormula Base Const Γ) =
      SemilocalModel.formulaTruth M ρ (SimpleTerm.toTerm t) :=
  rfl

@[simp] theorem semilocalTruth_top (M : SemilocalModel Base Const)
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx Γ)) :
    semilocalTruth M ρ (.top : SimplePropFormula Base Const Γ) = ⊤ :=
  rfl

@[simp] theorem semilocalTruth_bot (M : SemilocalModel Base Const)
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx Γ)) :
    semilocalTruth M ρ (.bot : SimplePropFormula Base Const Γ) = ⊥ :=
  rfl

@[simp] theorem semilocalTruth_conj (M : SemilocalModel Base Const)
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx Γ))
    (φ ψ : SimplePropFormula Base Const Γ) :
    semilocalTruth M ρ (.conj φ ψ) =
      semilocalTruth M ρ φ ⊓ semilocalTruth M ρ ψ :=
  rfl

@[simp] theorem semilocalTruth_disj (M : SemilocalModel Base Const)
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx Γ))
    (φ ψ : SimplePropFormula Base Const Γ) :
    semilocalTruth M ρ (.disj φ ψ) =
      semilocalTruth M ρ φ ⊔ semilocalTruth M ρ ψ :=
  rfl

@[simp] theorem semilocalTruth_impl (M : SemilocalModel Base Const)
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx Γ))
    (φ ψ : SimplePropFormula Base Const Γ) :
    semilocalTruth M ρ (.impl φ ψ) =
      semilocalTruth M ρ φ ⇨ semilocalTruth M ρ ψ :=
  rfl

/-- The direct simple-fragment evaluator matches native formula semantics exactly. -/
@[simp] theorem semilocalTruth_toFormula (M : SemilocalModel Base Const)
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx Γ))
    (φ : SimplePropFormula Base Const Γ) :
    semilocalTruth M ρ φ =
      SemilocalModel.formulaTruth M ρ (toFormula φ) := by
  induction φ with
  | atom t =>
      simp [semilocalTruth, SemilocalModel.formulaTruth]
  | top =>
      simp [semilocalTruth]
  | bot =>
      simp [semilocalTruth]
  | conj φ ψ ihφ ihψ =>
      simp [semilocalTruth, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      simp [semilocalTruth, ihφ, ihψ]
  | impl φ ψ ihφ ihψ =>
      simp [semilocalTruth, ihφ, ihψ]

/--
Semantic substitution for the live simple propositional fragment, expressed
through the native semilocal model substitution environment.
-/
@[simp] theorem semilocalTruth_subst (M : SemilocalModel Base Const)
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx Δ))
    (σs : SimpleSubst Base Const Γ Δ)
    (φ : SimplePropFormula Base Const Γ) :
    semilocalTruth M ρ (SimplePropFormula.subst σs φ) =
      semilocalTruth M
        (SemilocalModel.substEnv M (SimpleSubst.toSubst σs) ρ) φ := by
  rw [semilocalTruth_toFormula, semilocalTruth_toFormula]
  rw [SimplePropFormula.toFormula_subst]
  unfold SemilocalModel.formulaTruth
  congr 1
  exact SemilocalModel.eval_subst M (SimpleSubst.toSubst σs) (toFormula φ) ρ

/--
Native propositional derivations on translated simple formulas are sound for the
direct simple-fragment evaluator.
-/
theorem semilocalTruth_sound_of_translated
    (M : SemilocalModel Base Const)
    {Δ : List (SimplePropFormula Base Const Γ)}
    {φ : SimplePropFormula Base Const Γ}
    (h : PropositionalDerivable Const (Δ.map toFormula) (toFormula φ))
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx Γ))
    (hρ : SemilocalModel.IsGlobalEnv M ρ) :
    SemilocalModel.antecedentTruth M ρ (Δ.map toFormula) ≤
      semilocalTruth M ρ φ := by
  simpa using (SemilocalModel.propositional_soundness M h) ρ hρ

/--
Closed translated derivations evaluate to truth in every global semilocal
environment.
-/
theorem semilocalTruth_of_closed_derivable
    (M : SemilocalModel Base Const)
    {φ : SimplePropFormula Base Const []}
    (h : PropositionalDerivable Const [] (toFormula φ))
    (ρ : SemilocalModel.Env M (SimpleTy.toCtx ([] : List (SimpleTy Base))))
    (hρ : SemilocalModel.IsGlobalEnv M ρ) :
    semilocalTruth M ρ φ = ⊤ := by
  have hs :
      SemilocalModel.antecedentTruth M ρ [] ≤ semilocalTruth M ρ φ :=
    semilocalTruth_sound_of_translated (M := M) (Δ := []) (φ := φ) h ρ hρ
  have htop : (⊤ : M.Omega) ≤ semilocalTruth M ρ φ := by
    simpa [SemilocalModel.antecedentTruth] using hs
  exact le_antisymm le_top htop

end SimplePropFormula

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
