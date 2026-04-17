import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzPropositionalFragment
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzQuantifiedFragment

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w

namespace SimpleTopologicalInterpretation

variable {Base : Type u} {Const : Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

namespace CtxHom

variable {I : SimpleTopologicalInterpretation Base Const X}
variable {Γ Δ : List (SimpleTy Base)} {τ : SimpleTy Base}

/-- Lift a context morphism under one additional bound variable. -/
def lift (σ : I.CtxHom Δ Γ) : I.CtxHom (τ :: Δ) (τ :: Γ) :=
  CtxTerm.cons (CtxTerm.head I τ Δ) ((tail I τ Δ).comp σ)

@[simp] theorem lift_tail (σ : I.CtxHom Δ Γ) :
    (lift (I := I) (τ := τ) σ).comp (tail I τ Γ) =
      (tail I τ Δ).comp σ := by
  rfl

end CtxHom

namespace SimpleTerm

variable {I : SimpleTopologicalInterpretation Base Const X}
variable {Γ : List (SimpleTy Base)} {τ υ : SimpleTy Base}

@[simp] theorem eval_weaken (t : Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm Base Const Γ τ) :
    eval I (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm.weaken (υ := υ) t) =
      (eval I t).weaken υ := by
  cases t with
  | var x =>
      rfl
  | const c =>
      exact (CtxTerm.const_reindex
        (I := I)
        (Γ := Γ)
        (Δ := υ :: Γ)
        (t := CtxHom.tail I υ Γ)
        (τ := τ)
        c).symm

end SimpleTerm

namespace SimpleSubst

variable {I : SimpleTopologicalInterpretation Base Const X}
variable {Γ Δ : List (SimpleTy Base)} {τ υ : SimpleTy Base}

/--
Evaluating a pointwise-weakened substitution is exactly reindexing its semantic
context morphism along the tail projection.
-/
@[simp] theorem eval_weaken
    (σs : Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst Base Const Γ Δ) :
    eval I (fun {_τ} x => Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm.weaken
      (υ := υ) (σs x)) =
      (CtxHom.tail I υ Δ).comp (eval I σs) := by
  induction Γ generalizing Δ with
  | nil =>
      exact (CtxHom.toEmpty_eq_terminal (I := I)
        (σ := (CtxHom.tail I υ Δ).comp (eval I σs))).symm
  | cons τ Γ ih =>
      calc
        eval I (fun {_τ} x => Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm.weaken
            (υ := υ) (σs x))
            = CtxTerm.cons
                (SimpleTerm.eval I
                  (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm.weaken
                    (υ := υ) (σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ))))
                (eval I (fun {_τ} x =>
                  Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm.weaken
                    (υ := υ)
                    ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.tail σs) x))) := by
                  rfl
        _ = CtxTerm.cons
              ((CtxTerm.head I τ Γ).reindex ((CtxHom.tail I υ Δ).comp (eval I σs)))
              (((CtxHom.tail I υ Δ).comp (eval I σs)).comp (CtxHom.tail I τ Γ)) := by
                congr 1
                · calc
                    SimpleTerm.eval I
                        (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm.weaken
                          (υ := υ) (σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ)))
                        = (SimpleTerm.eval I
                            (σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ))).weaken υ := by
                              exact SimpleTopologicalInterpretation.SimpleTerm.eval_weaken
                                (I := I)
                                (υ := υ)
                                (t := σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ))
                    _ = ((CtxTerm.var I (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ)).reindex
                          (eval I σs)).weaken υ := by
                          rw [← var_reindex_eval (I := I) (σs := σs)
                            (x := (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ))]
                    _ = ((CtxTerm.head I τ Γ).reindex (eval I σs)).weaken υ := by
                          rfl
                    _ = ((CtxTerm.head I τ Γ).reindex (eval I σs)).reindex
                          (CtxHom.tail I υ Δ) := by
                          rfl
                    _ = (CtxTerm.head I τ Γ).reindex
                          ((CtxHom.tail I υ Δ).comp (eval I σs)) := by
                          exact (CtxTerm.reindex_comp
                            (t := CtxTerm.head I τ Γ)
                            (σ := CtxHom.tail I υ Δ)
                            (ρ := eval I σs)).symm
                · calc
                    eval I (fun {_τ} x =>
                        Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm.weaken
                          (υ := υ)
                          ((Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.tail σs) x))
                        = (CtxHom.tail I υ Δ).comp
                            (eval I
                              (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.tail σs)) := by
                                exact ih
                                  (σs := Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.tail σs)
                    _ = (CtxHom.tail I υ Δ).comp
                          ((eval I σs).comp (CtxHom.tail I τ Γ)) := by
                            simp [eval]
                    _ = (((CtxHom.tail I υ Δ).comp (eval I σs)).comp
                          (CtxHom.tail I τ Γ)) := by
                            exact (CtxHom.comp_assoc
                              (σ := CtxHom.tail I υ Δ)
                              (ρ := eval I σs)
                              (θ := CtxHom.tail I τ Γ)).symm
        _ = (CtxHom.tail I υ Δ).comp (eval I σs) := by
              exact (CtxHom.cons_reconstruct
                (I := I)
                (Γ := υ :: Δ)
                (Δ := Γ)
                (τ := τ)
                ((CtxHom.tail I υ Δ).comp (eval I σs))).symm

/-- Semantic evaluation of lifted substitutions matches lifted context morphisms. -/
@[simp] theorem eval_lift
    (σs : Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst Base Const Γ Δ) :
    eval I (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.lift
      (υ := υ) σs) =
      CtxHom.lift (I := I) (τ := υ) (eval I σs) := by
  apply (CtxHom.splitEquiv I (υ :: Δ) υ Γ).injective
  simp [CtxHom.lift, Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.lift]
  congr 1
  exact eval_weaken (I := I) (υ := υ) (σs := σs)

end SimpleSubst

end SimpleTopologicalInterpretation

/--
Quantifier operations on actual Awodey-Butz predicates in context, extending the
live proposition fragment with binder-aware reindexing laws.
-/
structure SimpleQuantifiedInterpretation
    (Base : Type u) (Const : Ty Base → Type v)
    (X : Type w) [TopologicalSpace X] where
  toPropositional : SimplePropositionalInterpretation Base Const X
  allPred : {τ : SimpleTy Base} → {Γ : List (SimpleTy Base)} →
    SimpleTopologicalInterpretation.Pred toPropositional.toSimple (τ :: Γ) →
      SimpleTopologicalInterpretation.Pred toPropositional.toSimple Γ
  exPred : {τ : SimpleTy Base} → {Γ : List (SimpleTy Base)} →
    SimpleTopologicalInterpretation.Pred toPropositional.toSimple (τ :: Γ) →
      SimpleTopologicalInterpretation.Pred toPropositional.toSimple Γ
  all_reindex :
    ∀ {τ : SimpleTy Base} {Γ Δ : List (SimpleTy Base)}
      (p : SimpleTopologicalInterpretation.Pred toPropositional.toSimple (τ :: Γ))
      (σ : toPropositional.toSimple.CtxHom Δ Γ),
      (allPred p).reindex σ =
        allPred (p.reindex
          (SimpleTopologicalInterpretation.CtxHom.lift
            (I := toPropositional.toSimple) (τ := τ) σ))
  ex_reindex :
    ∀ {τ : SimpleTy Base} {Γ Δ : List (SimpleTy Base)}
      (p : SimpleTopologicalInterpretation.Pred toPropositional.toSimple (τ :: Γ))
      (σ : toPropositional.toSimple.CtxHom Δ Γ),
      (exPred p).reindex σ =
        exPred (p.reindex
          (SimpleTopologicalInterpretation.CtxHom.lift
            (I := toPropositional.toSimple) (τ := τ) σ))

namespace SimpleQuantifiedInterpretation

variable {Base : Type u} {Const : Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

instance : Coe (SimpleQuantifiedInterpretation Base Const X)
    (SimplePropositionalInterpretation Base Const X) where
  coe := SimpleQuantifiedInterpretation.toPropositional

instance : Coe (SimpleQuantifiedInterpretation Base Const X)
    (SimpleTopologicalInterpretation Base Const X) where
  coe := fun I => I.toPropositional.toSimple

@[simp] theorem allPred_reindex
    (I : SimpleQuantifiedInterpretation Base Const X)
    {τ : SimpleTy Base} {Γ Δ : List (SimpleTy Base)}
    (p : SimpleTopologicalInterpretation.Pred I.toPropositional.toSimple (τ :: Γ))
    (σ : I.toPropositional.toSimple.CtxHom Δ Γ) :
    (I.allPred p).reindex σ =
      I.allPred (p.reindex
        (SimpleTopologicalInterpretation.CtxHom.lift
          (I := I.toPropositional.toSimple) (τ := τ) σ)) :=
  I.all_reindex p σ

@[simp] theorem exPred_reindex
    (I : SimpleQuantifiedInterpretation Base Const X)
    {τ : SimpleTy Base} {Γ Δ : List (SimpleTy Base)}
    (p : SimpleTopologicalInterpretation.Pred I.toPropositional.toSimple (τ :: Γ))
    (σ : I.toPropositional.toSimple.CtxHom Δ Γ) :
    (I.exPred p).reindex σ =
      I.exPred (p.reindex
        (SimpleTopologicalInterpretation.CtxHom.lift
          (I := I.toPropositional.toSimple) (τ := τ) σ)) :=
  I.ex_reindex p σ

end SimpleQuantifiedInterpretation

namespace SimpleQuantifiedFormula

variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Δ : List (SimpleTy Base)}

namespace SimpleQuantifiedInterpretation

variable {X : Type w} [TopologicalSpace X]

/-- Evaluate quantified simple formulas as actual Awodey-Butz predicates in context. -/
def eval (I : Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedInterpretation Base Const X) :
    {Γ : List (SimpleTy Base)} →
      SimpleQuantifiedFormula Base Const Γ →
        SimpleTopologicalInterpretation.Pred I.toPropositional.toSimple Γ
  | _, .atom t => SimpleTopologicalInterpretation.SimpleTerm.eval I.toPropositional.toSimple t
  | _, .top => I.toPropositional.top _
  | _, .bot => I.toPropositional.bot _
  | _, .conj φ ψ => I.toPropositional.conj (eval I φ) (eval I ψ)
  | _, .disj φ ψ => I.toPropositional.disj (eval I φ) (eval I ψ)
  | _, .impl φ ψ => I.toPropositional.impl (eval I φ) (eval I ψ)
  | _, .all _ φ => I.allPred (eval I φ)
  | _, .ex _ φ => I.exPred (eval I φ)

@[simp] theorem eval_subst
    (I : Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleQuantifiedInterpretation Base Const X)
    (σs : Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst Base Const Γ Δ)
    (φ : SimpleQuantifiedFormula Base Const Γ) :
    eval I (subst σs φ) =
      (eval I φ).reindex
        (SimpleTopologicalInterpretation.SimpleSubst.eval
          (I := (I : SimpleTopologicalInterpretation Base Const X)) σs) := by
  induction φ generalizing Δ with
  | atom t =>
      change
        SimpleTopologicalInterpretation.SimpleTerm.eval I.toPropositional.toSimple
            (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleTerm.subst σs t) =
          (SimpleTopologicalInterpretation.SimpleTerm.eval I.toPropositional.toSimple t).reindex
            (SimpleTopologicalInterpretation.SimpleSubst.eval
              (I := I.toPropositional.toSimple) σs)
      exact
        (SimpleTopologicalInterpretation.SimpleSubst.term_eval_subst
          (I := (I : SimpleTopologicalInterpretation Base Const X))
          (σs := σs) (t := t))
  | top =>
      simp [eval, subst]
  | bot =>
      simp [eval, subst]
  | conj φ ψ ihφ ihψ =>
      simp [eval, subst, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      simp [eval, subst, ihφ, ihψ]
  | impl φ ψ ihφ ihψ =>
      simp [eval, subst, ihφ, ihψ]
  | @all Γ τ φ ih =>
      simp [eval, subst, ih]
      have htail :
          SimpleTopologicalInterpretation.SimpleSubst.eval
              (I := (I : SimpleTopologicalInterpretation Base Const X))
              (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.tail
                (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.lift
                  (υ := τ) σs)) =
            (SimpleTopologicalInterpretation.CtxHom.tail
                (I := (I : SimpleTopologicalInterpretation Base Const X)) τ Δ).comp
              (SimpleTopologicalInterpretation.SimpleSubst.eval
                (I := (I : SimpleTopologicalInterpretation Base Const X)) σs) := by
            exact
              (SimpleTopologicalInterpretation.SimpleSubst.eval_weaken
                (I := (I : SimpleTopologicalInterpretation Base Const X))
                (υ := τ)
                (σs := σs))
      rw [htail]
      simp [SimpleTopologicalInterpretation.genericVar, SimpleTopologicalInterpretation.CtxHom.lift]
  | @ex Γ τ φ ih =>
      simp [eval, subst, ih]
      have htail :
          SimpleTopologicalInterpretation.SimpleSubst.eval
              (I := (I : SimpleTopologicalInterpretation Base Const X))
              (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.tail
                (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.SimpleSubst.lift
                  (υ := τ) σs)) =
            (SimpleTopologicalInterpretation.CtxHom.tail
                (I := (I : SimpleTopologicalInterpretation Base Const X)) τ Δ).comp
              (SimpleTopologicalInterpretation.SimpleSubst.eval
                (I := (I : SimpleTopologicalInterpretation Base Const X)) σs) := by
            exact
              (SimpleTopologicalInterpretation.SimpleSubst.eval_weaken
                (I := (I : SimpleTopologicalInterpretation Base Const X))
                (υ := τ)
                (σs := σs))
      rw [htail]
      simp [SimpleTopologicalInterpretation.genericVar, SimpleTopologicalInterpretation.CtxHom.lift]

end SimpleQuantifiedInterpretation

end SimpleQuantifiedFormula

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
