import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzSimplePredicateSyntax

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

universe u v w

/--
Awodey-Butz proposition-level semantic operations staged as predicate terms in
the relevant proposition contexts.
-/
structure SimplePropositionalInterpretation
    (Base : Type u) (Const : Mettapedia.Logic.HOL.Ty Base → Type v)
    (X : Type w) [TopologicalSpace X] where
  toSimple : SimpleTopologicalInterpretation Base Const X
  topPred : SimpleTopologicalInterpretation.Pred toSimple []
  botPred : SimpleTopologicalInterpretation.Pred toSimple []
  andPred : SimpleTopologicalInterpretation.Pred toSimple [.prop, .prop]
  orPred : SimpleTopologicalInterpretation.Pred toSimple [.prop, .prop]
  impPred : SimpleTopologicalInterpretation.Pred toSimple [.prop, .prop]

namespace SimplePropositionalInterpretation

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

instance : Coe (SimplePropositionalInterpretation Base Const X)
    (SimpleTopologicalInterpretation Base Const X) where
  coe := SimplePropositionalInterpretation.toSimple

/-- Package two proposition terms as a substitution into the binary proposition context. -/
def pairSubst (I : SimplePropositionalInterpretation Base Const X)
    {Γ : List (SimpleTy Base)}
    (p q : SimpleTopologicalInterpretation.Pred I.toSimple Γ) :
    I.toSimple.CtxHom Γ [.prop, .prop] :=
  SimpleTopologicalInterpretation.CtxTerm.cons p
    (SimpleTopologicalInterpretation.CtxTerm.cons q
      (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ))

@[simp] theorem pairSubst_apply
    (I : SimplePropositionalInterpretation Base Const X)
    {Γ : List (SimpleTy Base)}
    (p q : SimpleTopologicalInterpretation.Pred I.toSimple Γ) :
    pairSubst I p q =
      SimpleTopologicalInterpretation.CtxTerm.cons p
        (SimpleTopologicalInterpretation.CtxTerm.cons q
          (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ)) :=
  rfl

@[simp] theorem pairSubst_reindex
    (I : SimplePropositionalInterpretation Base Const X)
    {Γ Δ : List (SimpleTy Base)}
    (p q : SimpleTopologicalInterpretation.Pred I.toSimple Γ)
    (σ : I.toSimple.CtxHom Δ Γ) :
    σ.comp (pairSubst I p q) = pairSubst I (p.reindex σ) (q.reindex σ) := by
  calc
    σ.comp (pairSubst I p q)
        = SimpleTopologicalInterpretation.CtxTerm.cons
            ((SimpleTopologicalInterpretation.CtxTerm.head I.toSimple .prop [.prop]).reindex
              (σ.comp (pairSubst I p q)))
            ((σ.comp (pairSubst I p q)).comp
              (SimpleTopologicalInterpretation.CtxHom.tail I.toSimple .prop [.prop])) := by
              symm
              exact SimpleTopologicalInterpretation.CtxHom.cons_reconstruct
                (I := I.toSimple) (Γ := Δ) (Δ := [.prop]) (τ := .prop)
                (σ := σ.comp (pairSubst I p q))
    _ = SimpleTopologicalInterpretation.CtxTerm.cons
          (p.reindex σ)
          ((σ.comp (pairSubst I p q)).comp
            (SimpleTopologicalInterpretation.CtxHom.tail I.toSimple .prop [.prop])) := by
            rfl
    _ = SimpleTopologicalInterpretation.CtxTerm.cons
          (p.reindex σ)
          (σ.comp
            (SimpleTopologicalInterpretation.CtxTerm.cons q
              (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ))) := by
            rw [SimpleTopologicalInterpretation.CtxHom.comp_assoc]
            simp [pairSubst]
    _ = SimpleTopologicalInterpretation.CtxTerm.cons
          (p.reindex σ)
          (SimpleTopologicalInterpretation.CtxTerm.cons
            (q.reindex σ)
            (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Δ)) := by
            congr 1
            calc
              σ.comp
                  (SimpleTopologicalInterpretation.CtxTerm.cons q
                    (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ))
                  = SimpleTopologicalInterpretation.CtxTerm.cons
                      ((SimpleTopologicalInterpretation.CtxTerm.head I.toSimple .prop []).reindex
                        (σ.comp
                          (SimpleTopologicalInterpretation.CtxTerm.cons q
                            (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ))))
                      ((σ.comp
                          (SimpleTopologicalInterpretation.CtxTerm.cons q
                            (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ))).comp
                        (SimpleTopologicalInterpretation.CtxHom.tail I.toSimple .prop [])) := by
                          symm
                          exact SimpleTopologicalInterpretation.CtxHom.cons_reconstruct
                            (I := I.toSimple) (Γ := Δ) (Δ := []) (τ := .prop)
                            (σ := σ.comp
                              (SimpleTopologicalInterpretation.CtxTerm.cons q
                                (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ)))
              _ = SimpleTopologicalInterpretation.CtxTerm.cons
                    (q.reindex σ)
                    ((σ.comp
                        (SimpleTopologicalInterpretation.CtxTerm.cons q
                          (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ))).comp
                      (SimpleTopologicalInterpretation.CtxHom.tail I.toSimple .prop [])) := by
                        rfl
              _ = SimpleTopologicalInterpretation.CtxTerm.cons
                    (q.reindex σ)
                    (σ.comp (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ)) := by
                        rw [SimpleTopologicalInterpretation.CtxHom.comp_assoc,
                          SimpleTopologicalInterpretation.CtxTerm.tail_cons]
              _ = SimpleTopologicalInterpretation.CtxTerm.cons
                    (q.reindex σ)
                    (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Δ) := by
                        congr 1
                        exact SimpleTopologicalInterpretation.CtxHom.toEmpty_eq_terminal
                          (I := I.toSimple)
                          (σ := σ.comp
                            (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ))
    _ = pairSubst I (p.reindex σ) (q.reindex σ) := by
          rfl

/-- Lift a closed proposition term to any context by reindexing along terminality. -/
def top (I : SimplePropositionalInterpretation Base Const X)
    (Γ : List (SimpleTy Base)) :
    SimpleTopologicalInterpretation.Pred I.toSimple Γ :=
  I.topPred.reindex (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ)

/-- Lift the designated false proposition term to any context. -/
def bot (I : SimplePropositionalInterpretation Base Const X)
    (Γ : List (SimpleTy Base)) :
    SimpleTopologicalInterpretation.Pred I.toSimple Γ :=
  I.botPred.reindex (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ)

/-- Apply the staged conjunction operation in any context. -/
def conj (I : SimplePropositionalInterpretation Base Const X)
    {Γ : List (SimpleTy Base)}
    (p q : SimpleTopologicalInterpretation.Pred I.toSimple Γ) :
    SimpleTopologicalInterpretation.Pred I.toSimple Γ :=
  I.andPred.reindex (pairSubst I p q)

/-- Apply the staged disjunction operation in any context. -/
def disj (I : SimplePropositionalInterpretation Base Const X)
    {Γ : List (SimpleTy Base)}
    (p q : SimpleTopologicalInterpretation.Pred I.toSimple Γ) :
    SimpleTopologicalInterpretation.Pred I.toSimple Γ :=
  I.orPred.reindex (pairSubst I p q)

/-- Apply the staged implication operation in any context. -/
def impl (I : SimplePropositionalInterpretation Base Const X)
    {Γ : List (SimpleTy Base)}
    (p q : SimpleTopologicalInterpretation.Pred I.toSimple Γ) :
    SimpleTopologicalInterpretation.Pred I.toSimple Γ :=
  I.impPred.reindex (pairSubst I p q)

@[simp] theorem top_reindex
    (I : SimplePropositionalInterpretation Base Const X)
    {Γ Δ : List (SimpleTy Base)} (σ : I.toSimple.CtxHom Δ Γ) :
    (I.top Γ).reindex σ = I.top Δ := by
  unfold top
  rw [SimpleTopologicalInterpretation.CtxTerm.reindex_comp]
  rw [SimpleTopologicalInterpretation.CtxHom.toEmpty_eq_terminal
    (I := I.toSimple)
    (σ := σ.comp (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ))]

@[simp] theorem bot_reindex
    (I : SimplePropositionalInterpretation Base Const X)
    {Γ Δ : List (SimpleTy Base)} (σ : I.toSimple.CtxHom Δ Γ) :
    (I.bot Γ).reindex σ = I.bot Δ := by
  unfold bot
  rw [SimpleTopologicalInterpretation.CtxTerm.reindex_comp]
  rw [SimpleTopologicalInterpretation.CtxHom.toEmpty_eq_terminal
    (I := I.toSimple)
    (σ := σ.comp (SimpleTopologicalInterpretation.CtxHom.terminal I.toSimple Γ))]

@[simp] theorem conj_reindex
    (I : SimplePropositionalInterpretation Base Const X)
    {Γ Δ : List (SimpleTy Base)}
    (p q : SimpleTopologicalInterpretation.Pred I.toSimple Γ)
    (σ : I.toSimple.CtxHom Δ Γ) :
    (I.conj p q).reindex σ = I.conj (p.reindex σ) (q.reindex σ) := by
  unfold conj
  rw [SimpleTopologicalInterpretation.CtxTerm.reindex_comp, pairSubst_reindex]

@[simp] theorem disj_reindex
    (I : SimplePropositionalInterpretation Base Const X)
    {Γ Δ : List (SimpleTy Base)}
    (p q : SimpleTopologicalInterpretation.Pred I.toSimple Γ)
    (σ : I.toSimple.CtxHom Δ Γ) :
    (I.disj p q).reindex σ = I.disj (p.reindex σ) (q.reindex σ) := by
  unfold disj
  rw [SimpleTopologicalInterpretation.CtxTerm.reindex_comp, pairSubst_reindex]

@[simp] theorem impl_reindex
    (I : SimplePropositionalInterpretation Base Const X)
    {Γ Δ : List (SimpleTy Base)}
    (p q : SimpleTopologicalInterpretation.Pred I.toSimple Γ)
    (σ : I.toSimple.CtxHom Δ Γ) :
    (I.impl p q).reindex σ = I.impl (p.reindex σ) (q.reindex σ) := by
  unfold impl
  rw [SimpleTopologicalInterpretation.CtxTerm.reindex_comp, pairSubst_reindex]

end SimplePropositionalInterpretation

/-- A proposition-only syntax on top of the live simple typed term fragment. -/
inductive SimplePropFormula
    (Base : Type u) (Const : Mettapedia.Logic.HOL.Ty Base → Type v) :
    List (SimpleTy Base) → Type (max u v) where
  | atom : SimpleTerm Base Const Γ .prop → SimplePropFormula Base Const Γ
  | top : SimplePropFormula Base Const Γ
  | bot : SimplePropFormula Base Const Γ
  | conj : SimplePropFormula Base Const Γ → SimplePropFormula Base Const Γ →
      SimplePropFormula Base Const Γ
  | disj : SimplePropFormula Base Const Γ → SimplePropFormula Base Const Γ →
      SimplePropFormula Base Const Γ
  | impl : SimplePropFormula Base Const Γ → SimplePropFormula Base Const Γ →
      SimplePropFormula Base Const Γ

namespace SimplePropFormula

variable {Base : Type u} {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
variable {Γ Δ : List (SimpleTy Base)}

/-- Substitute simple terms into a proposition formula. -/
def subst (σs : SimpleSubst Base Const Γ Δ) :
    SimplePropFormula Base Const Γ → SimplePropFormula Base Const Δ
  | .atom t => .atom (SimpleTerm.subst σs t)
  | .top => .top
  | .bot => .bot
  | .conj φ ψ => .conj (subst σs φ) (subst σs ψ)
  | .disj φ ψ => .disj (subst σs φ) (subst σs ψ)
  | .impl φ ψ => .impl (subst σs φ) (subst σs ψ)

namespace SimplePropositionalInterpretation

variable {X : Type w} [TopologicalSpace X]
variable (I : SimplePropositionalInterpretation Base Const X)
variable {Γ Δ : List (SimpleTy Base)}

/-- Evaluate the live proposition fragment in the staged Awodey-Butz semantics. -/
def eval : SimplePropFormula Base Const Γ →
    SimpleTopologicalInterpretation.Pred I.toSimple Γ
  | .atom t => SimpleTopologicalInterpretation.SimpleTerm.eval I.toSimple t
  | .top => I.top Γ
  | .bot => I.bot Γ
  | .conj φ ψ => I.conj (eval φ) (eval ψ)
  | .disj φ ψ => I.disj (eval φ) (eval ψ)
  | .impl φ ψ => I.impl (eval φ) (eval ψ)

@[simp] theorem eval_atom (t : SimpleTerm Base Const Γ .prop) :
    eval I (.atom t) = SimpleTopologicalInterpretation.SimpleTerm.eval I.toSimple t :=
  rfl

@[simp] theorem eval_top :
    eval I (.top : SimplePropFormula Base Const Γ) = I.top Γ :=
  rfl

@[simp] theorem eval_bot :
    eval I (.bot : SimplePropFormula Base Const Γ) = I.bot Γ :=
  rfl

@[simp] theorem eval_conj (φ ψ : SimplePropFormula Base Const Γ) :
    eval I (.conj φ ψ) = I.conj (eval I φ) (eval I ψ) :=
  rfl

@[simp] theorem eval_disj (φ ψ : SimplePropFormula Base Const Γ) :
    eval I (.disj φ ψ) = I.disj (eval I φ) (eval I ψ) :=
  rfl

@[simp] theorem eval_impl (φ ψ : SimplePropFormula Base Const Γ) :
    eval I (.impl φ ψ) = I.impl (eval I φ) (eval I ψ) :=
  rfl

@[simp] theorem eval_subst (σs : SimpleSubst Base Const Γ Δ)
    (φ : SimplePropFormula Base Const Γ) :
    eval I (subst σs φ) =
      (eval I φ).reindex
        (SimpleTopologicalInterpretation.SimpleSubst.eval I.toSimple σs) := by
  let σ := SimpleTopologicalInterpretation.SimpleSubst.eval I.toSimple σs
  induction φ with
  | atom t =>
      exact SimpleTopologicalInterpretation.SimpleSubst.term_eval_subst
        (I := I.toSimple) (σs := σs) (t := t)
  | top =>
      simpa only [eval, subst] using
        (SimplePropositionalInterpretation.top_reindex
          (I := I)
          (Γ := Γ) (Δ := Δ)
          (σ := σ)).symm
  | bot =>
      simpa only [eval, subst] using
        (SimplePropositionalInterpretation.bot_reindex
          (I := I)
          (Γ := Γ) (Δ := Δ)
          (σ := σ)).symm
  | conj φ ψ ihφ ihψ =>
      calc
        eval I (subst σs (.conj φ ψ))
            = I.conj (eval I (subst σs φ)) (eval I (subst σs ψ)) := by
                rfl
        _ = I.conj ((eval I φ).reindex σ) ((eval I ψ).reindex σ) := by
              rw [ihφ, ihψ]
        _ = (I.conj (eval I φ) (eval I ψ)).reindex σ := by
              symm
              exact SimplePropositionalInterpretation.conj_reindex
                (I := I) (p := eval I φ) (q := eval I ψ) (σ := σ)
        _ = (eval I (.conj φ ψ)).reindex σ := by
              rfl
  | disj φ ψ ihφ ihψ =>
      calc
        eval I (subst σs (.disj φ ψ))
            = I.disj (eval I (subst σs φ)) (eval I (subst σs ψ)) := by
                rfl
        _ = I.disj ((eval I φ).reindex σ) ((eval I ψ).reindex σ) := by
              rw [ihφ, ihψ]
        _ = (I.disj (eval I φ) (eval I ψ)).reindex σ := by
              symm
              exact SimplePropositionalInterpretation.disj_reindex
                (I := I) (p := eval I φ) (q := eval I ψ) (σ := σ)
        _ = (eval I (.disj φ ψ)).reindex σ := by
              rfl
  | impl φ ψ ihφ ihψ =>
      calc
        eval I (subst σs (.impl φ ψ))
            = I.impl (eval I (subst σs φ)) (eval I (subst σs ψ)) := by
                rfl
        _ = I.impl ((eval I φ).reindex σ) ((eval I ψ).reindex σ) := by
              rw [ihφ, ihψ]
        _ = (I.impl (eval I φ) (eval I ψ)).reindex σ := by
              symm
              exact SimplePropositionalInterpretation.impl_reindex
                (I := I) (p := eval I φ) (q := eval I ψ) (σ := σ)
        _ = (eval I (.impl φ ψ)).reindex σ := by
              rfl

end SimplePropositionalInterpretation

end SimplePropFormula

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
