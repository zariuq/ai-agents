import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSimpleVariables

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

universe u v w

/--
The first live term syntax for the archive-free Awodey-Butz route: variables
and constants in the simple proposition/base-sort fragment.
-/
inductive SimpleTerm (Base : Type u) (Const : Mettapedia.Logic.HOL.Ty Base → Type v) :
    List (SimpleTy Base) → SimpleTy Base → Type (max u v) where
  | var : SimpleVar Base Γ τ → SimpleTerm Base Const Γ τ
  | const : Const τ.toTy → SimpleTerm Base Const Γ τ

/--
A substitution from `Γ` into `Δ` assigns to each variable of `Γ` a term over
`Δ`.
-/
abbrev SimpleSubst (Base : Type u) (Const : Mettapedia.Logic.HOL.Ty Base → Type v)
    (Γ Δ : List (SimpleTy Base)) : Type (max u v) :=
  {τ : SimpleTy Base} → SimpleVar Base Γ τ → SimpleTerm Base Const Δ τ

namespace SimpleSubst

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {Γ Δ Ξ : List (SimpleTy Base)} {τ : SimpleTy Base}

/-- Identity substitution. -/
def id : SimpleSubst Base Const Γ Γ := fun x => .var x

/-- Drop the head component of a substitution into an extended context. -/
def tail (σs : SimpleSubst Base Const (τ :: Γ) Δ) : SimpleSubst Base Const Γ Δ :=
  fun x => σs (.vs x)

/-- Extend a substitution by a term for the new head variable. -/
def cons (t : SimpleTerm Base Const Δ τ) (σs : SimpleSubst Base Const Γ Δ) :
    SimpleSubst Base Const (τ :: Γ) Δ
  | _, .vz => t
  | _, .vs x => σs x

@[simp] theorem id_apply (x : SimpleVar Base Γ τ) :
    id (Base := Base) (Const := Const) x = .var x :=
  rfl

@[simp] theorem tail_cons (t : SimpleTerm Base Const Δ τ) (σs : SimpleSubst Base Const Γ Δ)
    (x : SimpleVar Base Γ τ) :
    tail (cons t σs) x = σs x :=
  rfl

@[simp] theorem cons_vz (t : SimpleTerm Base Const Δ τ) (σs : SimpleSubst Base Const Γ Δ) :
    cons t σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ) = t :=
  rfl

@[simp] theorem cons_vs (t : SimpleTerm Base Const Δ τ) (σs : SimpleSubst Base Const Γ Δ)
    (x : SimpleVar Base Γ τ) :
    cons t σs (SimpleVar.vs x) = σs x :=
  rfl

end SimpleSubst

namespace SimpleTerm

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {Γ Δ : List (SimpleTy Base)} {τ υ : SimpleTy Base}

/-- Weaken a term by adding a new head variable to the context. -/
def weaken : SimpleTerm Base Const Γ τ → SimpleTerm Base Const (υ :: Γ) τ
  | .var x => .var (.vs x)
  | .const c => .const c

/-- Substitute terms for the variables of a term. -/
def subst (σs : SimpleSubst Base Const Γ Δ) : SimpleTerm Base Const Γ τ → SimpleTerm Base Const Δ τ
  | .var x => σs x
  | .const c => .const c

@[simp] theorem subst_var (σs : SimpleSubst Base Const Γ Δ) (x : SimpleVar Base Γ τ) :
    subst σs (.var x : SimpleTerm Base Const Γ τ) = σs x :=
  rfl

@[simp] theorem subst_const (σs : SimpleSubst Base Const Γ Δ) (c : Const τ.toTy) :
    subst σs (.const c : SimpleTerm Base Const Γ τ) = .const c :=
  rfl

@[simp] theorem subst_id (t : SimpleTerm Base Const Γ τ) :
    subst (SimpleSubst.id (Base := Base) (Const := Const) (Γ := Γ)) t = t := by
  cases t <;> rfl

@[simp] theorem subst_cons_vz (t : SimpleTerm Base Const Δ τ) (σs : SimpleSubst Base Const Γ Δ) :
    subst (SimpleSubst.cons t σs) (.var (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ)) = t :=
  rfl

@[simp] theorem subst_cons_vs
    (t : SimpleTerm Base Const Δ υ) (σs : SimpleSubst Base Const Γ Δ)
    (x : SimpleVar Base Γ τ) :
    subst (SimpleSubst.cons t σs) (.var (SimpleVar.vs x) : SimpleTerm Base Const (υ :: Γ) τ) =
      subst σs (.var x : SimpleTerm Base Const Γ τ) :=
  rfl

end SimpleTerm

namespace SimpleSubst

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {Γ Δ Ξ Ω : List (SimpleTy Base)} {τ : SimpleTy Base}

/-- Compose substitutions by term substitution. -/
def comp (σs : SimpleSubst Base Const Γ Δ) (τs : SimpleSubst Base Const Δ Ξ) :
    SimpleSubst Base Const Γ Ξ :=
  fun x => SimpleTerm.subst τs (σs x)

@[simp] theorem comp_apply (σs : SimpleSubst Base Const Γ Δ) (τs : SimpleSubst Base Const Δ Ξ)
    (x : SimpleVar Base Γ τ) :
    comp σs τs x = SimpleTerm.subst τs (σs x) :=
  rfl

@[simp] theorem tail_comp_apply {υ : SimpleTy Base}
    (σs : SimpleSubst Base Const (τ :: Γ) Δ)
    (τs : SimpleSubst Base Const Δ Ξ) (x : SimpleVar Base Γ υ) :
    tail (comp σs τs) x = comp (tail σs) τs x :=
  rfl

@[simp] theorem comp_id_apply (σs : SimpleSubst Base Const Γ Δ) (x : SimpleVar Base Γ τ) :
    comp σs (id (Base := Base) (Const := Const) (Γ := Δ)) x = σs x := by
  simp [comp]

@[simp] theorem id_comp_apply (σs : SimpleSubst Base Const Γ Δ) (x : SimpleVar Base Γ τ) :
    comp (id (Base := Base) (Const := Const) (Γ := Γ)) σs x = σs x :=
  rfl

@[simp] theorem comp_assoc_apply (σs : SimpleSubst Base Const Γ Δ)
    (τs : SimpleSubst Base Const Δ Ξ) (υs : SimpleSubst Base Const Ξ Ω)
    (x : SimpleVar Base Γ τ) :
    comp (comp σs τs) υs x = comp σs (comp τs υs) x := by
  cases h : σs x <;> simp [comp, SimpleTerm.subst, h]

end SimpleSubst

namespace SimpleTerm

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {Γ Δ Ξ : List (SimpleTy Base)} {τ : SimpleTy Base}

@[simp] theorem subst_comp (σs : SimpleSubst Base Const Γ Δ)
    (τs : SimpleSubst Base Const Δ Ξ) (t : SimpleTerm Base Const Γ τ) :
    subst τs (subst σs t) = subst (SimpleSubst.comp σs τs) t := by
  cases t <;> rfl

end SimpleTerm

namespace SimpleTopologicalInterpretation

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

namespace SimpleTerm

variable {I : SimpleTopologicalInterpretation Base Const X}
variable {Γ Δ : List (SimpleTy Base)} {τ : SimpleTy Base}

/-- Interpret a simple term as a semantic term in context. -/
def eval (I : SimpleTopologicalInterpretation Base Const X) :
    SimpleTerm Base Const Γ τ → I.CtxTerm Γ τ
  | .var x => CtxTerm.var I x
  | .const c => CtxTerm.const I Γ τ c

@[simp] theorem eval_var (x : SimpleVar Base Γ τ) :
    eval I (.var x : SimpleTerm Base Const Γ τ) = CtxTerm.var I x :=
  rfl

@[simp] theorem eval_const (c : Const τ.toTy) :
    eval I (.const c : SimpleTerm Base Const Γ τ) = CtxTerm.const I Γ τ c :=
  rfl

end SimpleTerm

namespace SimpleSubst

variable {I : SimpleTopologicalInterpretation Base Const X}
variable {Γ Δ : List (SimpleTy Base)} {τ : SimpleTy Base}

/-- Interpret a syntactic substitution as a semantic context morphism. -/
def eval (I : SimpleTopologicalInterpretation Base Const X) :
    {Γ Δ : List (SimpleTy Base)} →
      SimpleSubst Base Const Γ Δ → I.CtxHom Δ Γ
  | [], Δ, _ => CtxHom.terminal I Δ
  | τ :: Γ, _, σs =>
      CtxTerm.cons (SimpleTerm.eval I (σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ)))
        (eval I (SimpleSubst.tail σs))

@[simp] theorem eval_nil (σs : SimpleSubst Base Const [] Δ) :
    eval I σs = CtxHom.terminal I Δ :=
  rfl

@[simp] theorem eval_cons (σs : SimpleSubst Base Const (τ :: Γ) Δ) :
    eval I σs =
      CtxTerm.cons (SimpleTerm.eval I (σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ)))
        (eval I (SimpleSubst.tail σs)) :=
  rfl

@[simp] theorem var_reindex_eval
    (σs : SimpleSubst Base Const Γ Δ) (x : SimpleVar Base Γ τ) :
    (CtxTerm.var I x).reindex (eval I σs) = SimpleTerm.eval I (σs x) := by
  induction x generalizing Δ with
  | vz =>
      simp [eval, SimpleTerm.eval]
  | @vs Γ υ τ x ih =>
      calc
        (CtxTerm.var I (.vs x)).reindex (eval I σs)
            = (CtxTerm.var I x).reindex (eval I (SimpleSubst.tail σs)) := by
                simpa [SimpleSubst.tail, SimpleTerm.eval] using
                  (CtxTerm.var_vs_reindex_cons (I := I) (x := x)
                    (t := SimpleTerm.eval I (σs SimpleVar.vz))
                    (σ := eval I (SimpleSubst.tail σs)))
        _ = SimpleTerm.eval I ((SimpleSubst.tail σs) x) := ih (σs := SimpleSubst.tail σs)
        _ = SimpleTerm.eval I (σs (.vs x)) := rfl

@[simp] theorem term_eval_subst
    (σs : SimpleSubst Base Const Γ Δ) (t : SimpleTerm Base Const Γ τ) :
    SimpleTerm.eval I (SimpleTerm.subst σs t) =
      (SimpleTerm.eval I t).reindex (eval I σs) := by
  cases t with
  | var x =>
      exact (var_reindex_eval (I := I) σs x).symm
  | const c =>
      exact (CtxTerm.const_reindex (I := I) (Γ := Γ) (Δ := Δ) (t := eval I σs) (τ := τ) c).symm

@[simp] theorem eval_comp
    {Ξ : List (SimpleTy Base)} (σs : SimpleSubst Base Const Γ Δ)
    (τs : SimpleSubst Base Const Δ Ξ) :
    eval I (SimpleSubst.comp σs τs) = (eval I τs).comp (eval I σs) := by
  induction Γ generalizing Δ Ξ with
  | nil =>
      exact (CtxHom.toEmpty_eq_terminal (I := I)
        (σ := (eval I τs).comp (eval I σs))).symm
  | cons τ Γ ih =>
      calc
        eval I (SimpleSubst.comp σs τs)
            = CtxTerm.cons
                (SimpleTerm.eval I (SimpleTerm.subst τs (σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ))))
                (eval I (SimpleSubst.tail (SimpleSubst.comp σs τs))) := by
                  simp [eval, SimpleSubst.comp]
        _ = CtxTerm.cons
                (SimpleTerm.eval I (SimpleTerm.subst τs (σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ))))
                (eval I (SimpleSubst.comp (SimpleSubst.tail σs) τs)) := by
                  rfl
        _ = CtxTerm.cons
              ((CtxTerm.head I τ Γ).reindex ((eval I τs).comp (eval I σs)))
              (((eval I τs).comp (eval I σs)).comp (CtxHom.tail I τ Γ)) := by
                congr 1
                · calc
                    SimpleTerm.eval I (SimpleTerm.subst τs (σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ)))
                        = (SimpleTerm.eval I (σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ))).reindex
                            (eval I τs) := by
                              exact term_eval_subst (I := I) (σs := τs)
                                (t := σs (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ))
                    _ = ((CtxTerm.var I (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ)).reindex
                            (eval I σs)).reindex (eval I τs) := by
                              rw [← var_reindex_eval (I := I) (σs := σs)
                                (x := (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ))]
                    _ = (CtxTerm.var I (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ)).reindex
                          ((eval I τs).comp (eval I σs)) := by
                              exact (CtxTerm.reindex_comp (t := CtxTerm.var I (SimpleVar.vz : SimpleVar Base (τ :: Γ) τ))
                                (σ := eval I τs) (ρ := eval I σs)).symm
                    _ = (CtxTerm.head I τ Γ).reindex ((eval I τs).comp (eval I σs)) := by
                              rfl
                · calc
                    eval I (SimpleSubst.comp (SimpleSubst.tail σs) τs)
                        = (eval I τs).comp (eval I (SimpleSubst.tail σs)) := by
                              exact ih (σs := SimpleSubst.tail σs) (τs := τs)
                    _ = (eval I τs).comp ((eval I σs).comp (CtxHom.tail I τ Γ)) := by
                              simp [eval]
                    _ = ((eval I τs).comp (eval I σs)).comp (CtxHom.tail I τ Γ) := by
                              exact (CtxHom.comp_assoc (σ := eval I τs)
                                (ρ := eval I σs) (θ := CtxHom.tail I τ Γ)).symm
        _ = (eval I τs).comp (eval I σs) := by
              exact (CtxHom.cons_reconstruct (I := I) (Γ := Ξ) (Δ := Γ) (τ := τ)
                ((eval I τs).comp (eval I σs))).symm

end SimpleSubst

end SimpleTopologicalInterpretation

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
