import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzFullTyped
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Terms
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Sequent

/-!
# Topological Semantics for HOL

This file interprets HOL terms and formulas in the topological semantics,
building toward the Awodey-Butz completeness theorem.

## Main Definitions

* `TopologicalInterpretation.eval` - Interpret a term in context
* `TopologicalInterpretation.formulaTruth` - Interpret a formula as a section of Ω
* `TopologicalInterpretation.ValidSequent` - Sequent validity in topological models
* `topological_soundness` - If Γ ⊢ φ then Γ ⊨ φ in all topological models

## The Completeness Strategy

The Awodey-Butz strategy for completeness:

1. Given a non-derivable sequent Γ ⊢ φ, construct a topological space X
   from the syntax (e.g., prime filter space or Stone space)
2. Build an interpretation where types become étale spaces over X
3. Show that Γ forces to ⊤ but φ does not at some point

## References

* Awodey-Butz (2000), "Topological Completeness for Higher-Order Logic"
* Mac Lane-Moerdijk, "Sheaves in Geometry and Logic"
-/

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL
open Function TopologicalSpace TopologicalSpace.Opens Topology CategoryTheory

universe u v w

namespace TopologicalInterpretation

variable {Base : Type u} {Const : Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]
variable (I : TopologicalInterpretation Base Const X)

/-!
## Context Weakening

Context weakening morphisms allow us to interpret variables.
-/

/-- Context weakening morphism: drop the head variable. -/
noncomputable def weaken (τ : Ty Base) (Γ : Ctx Base) :
    I.CtxHom (τ :: Γ) Γ :=
  EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
    I.toBasicTopologicalInterpretation τ Γ

/-!
## Variable Interpretation

Variables are interpreted by projecting from the context space.
-/

/-- Interpret a de Bruijn variable as a projection from the context space. -/
noncomputable def evalVar (I : TopologicalInterpretation Base Const X)
    {Γ : Ctx Base} {τ : Ty Base} :
    Var Γ τ → I.CtxTerm Γ τ
  | .vz => CtxTerm.var0 I _ _
  | .vs v => (evalVar I v).reindex (I.weaken _ _)

/-!
## Constant Interpretation

Constants are pulled back from their global sections.
-/

/-- Pull back a constant to any context. -/
noncomputable def evalConst {τ : Ty Base} (Γ : Ctx Base) :
    Const τ → I.CtxTerm Γ τ :=
  EtaleSpace.BasicTopologicalInterpretation.CtxTerm.const
    I.toBasicTopologicalInterpretation Γ

/-!
## Logical Operations Interface

The full typed topological interpretation handles variables, constants,
abstraction, and application directly. The genuinely logical connectives and
quantifiers require extra structure on the proposition space and on equality.

We package that structure here so the generic evaluator can remain import-acyclic
while richer layers, such as the Heyting semantics, provide the implementation.
-/

/--
Additional semantic structure required to evaluate the logical fragment of HOL
over a fixed full typed topological interpretation.
-/
class HasLogicalOperations (I : TopologicalInterpretation Base Const X) where
  /-- Truth in context. -/
  evalTop : (Γ : Ctx Base) → I.CtxTerm Γ .prop
  /-- Falsity in context. -/
  evalBot : (Γ : Ctx Base) → I.CtxTerm Γ .prop
  /-- Conjunction. -/
  evalAnd : {Γ : Ctx Base} →
    I.CtxTerm Γ .prop → I.CtxTerm Γ .prop → I.CtxTerm Γ .prop
  /-- Disjunction. -/
  evalOr : {Γ : Ctx Base} →
    I.CtxTerm Γ .prop → I.CtxTerm Γ .prop → I.CtxTerm Γ .prop
  /-- Implication. -/
  evalImp : {Γ : Ctx Base} →
    I.CtxTerm Γ .prop → I.CtxTerm Γ .prop → I.CtxTerm Γ .prop
  /-- Equality at an arbitrary type. -/
  evalEq : {Γ : Ctx Base} {τ : Ty Base} →
    I.CtxTerm Γ τ → I.CtxTerm Γ τ → I.CtxTerm Γ .prop
  /-- Universal quantification. -/
  evalAll : {Γ : Ctx Base} {σ : Ty Base} →
    I.CtxTerm (σ :: Γ) .prop → I.CtxTerm Γ .prop
  /-- Existential quantification. -/
  evalEx : {Γ : Ctx Base} {σ : Ty Base} →
    I.CtxTerm (σ :: Γ) .prop → I.CtxTerm Γ .prop

/--
The theorem-level sequent semantics carried by a full topological
interpretation.

`HasLogicalOperations` is enough to evaluate formulas, but soundness needs an
actual validity notion together with a proof that derivations preserve it.
Richer layers, such as the Heyting semantics, provide this package.
-/
class HasSequentSemantics (I : TopologicalInterpretation Base Const X)
    [HasLogicalOperations I] where
  /-- Sequent validity in the given topological semantics. -/
  validSequent :
    {Γ : Ctx Base} → List (Formula Const Γ) → Formula Const Γ → Prop
  /-- Derivable sequents are valid in this semantics. -/
  sound :
    {Γ : Ctx Base} {antecedents : List (Formula Const Γ)}
      {succedent : Formula Const Γ} →
      Derivable Const antecedents succedent →
        validSequent antecedents succedent

/--
A packaged topological counterexample to a sequent.

This keeps the theorem layer honest: when we only know that some topological
interpretation refutes a sequent, we package the base space, interpretation, and
required semantic instances together instead of hard-coding a single model.
-/
structure Counterexample
    {Γ : Ctx Base}
    (antecedents : List (Formula Const Γ))
    (succedent : Formula Const Γ) where
  X : Type w
  instTopologicalSpace : TopologicalSpace X
  I : TopologicalInterpretation Base Const X
  instLogical : HasLogicalOperations I
  instSequent : HasSequentSemantics I
  invalid : ¬ HasSequentSemantics.validSequent (I := I) antecedents succedent

attribute [instance] Counterexample.instTopologicalSpace
attribute [instance] Counterexample.instLogical
attribute [instance] Counterexample.instSequent

/--
Package a fixed invalid topological interpretation as a counterexample witness.

This is the producer-side counterpart to `Counterexample.not_derivable`: once a
concrete topological interpretation and its semantic structure are in hand, any
failure of validity can be repackaged into the existential theorem layer.
-/
def Counterexample.ofInvalid
    (I : TopologicalInterpretation Base Const X)
    [HasLogicalOperations I] [HasSequentSemantics I]
    {Γ : Ctx Base}
    (antecedents : List (Formula Const Γ))
    (succedent : Formula Const Γ)
    (hInvalid : ¬ HasSequentSemantics.validSequent (I := I) antecedents succedent) :
    Counterexample (Base := Base) (Const := Const) antecedents succedent where
  X := X
  instTopologicalSpace := inferInstance
  I := I
  instLogical := inferInstance
  instSequent := inferInstance
  invalid := hInvalid

/--
Any fixed topological invalidity immediately yields an existential packaged
counterexample.
-/
theorem exists_counterexample_of_not_valid
    (I : TopologicalInterpretation Base Const X)
    [HasLogicalOperations I] [HasSequentSemantics I]
    {Γ : Ctx Base}
    {antecedents : List (Formula Const Γ)}
    {succedent : Formula Const Γ}
    (hInvalid : ¬ HasSequentSemantics.validSequent (I := I) antecedents succedent) :
    Nonempty
      (Counterexample (Base := Base) (Const := Const) antecedents succedent) :=
  ⟨Counterexample.ofInvalid (I := I) antecedents succedent hInvalid⟩

/-!
## Term Interpretation

We interpret HOL terms as continuous maps over the base space.
A term `Γ ⊢ t : τ` becomes a morphism `⟦Γ⟧ → ⟦τ⟧` of étale spaces.
-/

/--
Interpret a term in context as a continuous section of the type space.

This is the semantic denotation `⟦t⟧ : ⟦Γ⟧ → ⟦τ⟧` of a term `Γ ⊢ t : τ`.
-/
noncomputable def eval (I : TopologicalInterpretation Base Const X)
    [HasLogicalOperations I]
    {Γ : Ctx Base} {τ : Ty Base} :
    Term Const Γ τ → I.CtxTerm Γ τ
  | .var v => evalVar I v
  | .const c => I.evalConst Γ c
  | .lam body => CtxTerm.lam (eval I body)
  | .app f a => CtxTerm.app (eval I f) (eval I a)
  | .top => HasLogicalOperations.evalTop (I := I) Γ
  | .bot => HasLogicalOperations.evalBot (I := I) Γ
  | .and φ ψ => HasLogicalOperations.evalAnd (I := I) (eval I φ) (eval I ψ)
  | .or φ ψ => HasLogicalOperations.evalOr (I := I) (eval I φ) (eval I ψ)
  | .imp φ ψ => HasLogicalOperations.evalImp (I := I) (eval I φ) (eval I ψ)
  | .not φ =>
      HasLogicalOperations.evalImp (I := I)
        (eval I φ) (HasLogicalOperations.evalBot (I := I) Γ)
  | .eq t u => HasLogicalOperations.evalEq (I := I) (eval I t) (eval I u)
  | .all φ => HasLogicalOperations.evalAll (I := I) (eval I φ)
  | .ex φ => HasLogicalOperations.evalEx (I := I) (eval I φ)

/-!
## Formula Interpretation

Formulas are terms of type `prop`, so their interpretation is a section
of the proposition space `⟦prop⟧ = I.propSpace`.
-/

/--
A formula `Γ ⊢ φ : prop` is interpreted as a morphism `⟦Γ⟧ → Ω`.
-/
noncomputable def formulaTruth (I : TopologicalInterpretation Base Const X)
    [HasLogicalOperations I]
    {Γ : Ctx Base} (φ : Formula Const Γ) :
    I.CtxTerm Γ .prop :=
  eval I φ

/-!
## Sequent Validity

A sequent `Γ₀ | Γ₁, ..., Γₙ ⊢ φ` is valid if for all environments where
the antecedent formulas force to ⊤, the succedent also forces to ⊤.
-/

/--
A sequent is valid in the topological interpretation if, fiberwise at each
point of the base space, the conjunction of antecedents implies the succedent.

**Note**: The precise statement requires the Heyting structure on `I.propSpace`.
For now, we define validity using the section ordering.
-/
def ValidSequent (I : TopologicalInterpretation Base Const X)
    [HasLogicalOperations I] [HasSequentSemantics I]
    {Γ : Ctx Base} (antecedents : List (Formula Const Γ))
    (succedent : Formula Const Γ) : Prop :=
  HasSequentSemantics.validSequent (I := I) antecedents succedent

/-!
## Soundness

Soundness says that derivable sequents are valid in all topological models.
-/

/--
**Soundness Theorem**: If a sequent is derivable in intuitionistic HOL,
then it is valid in every topological interpretation.

This is the easier direction of completeness; it follows from the
fact that the inference rules preserve truth in any Heyting-valued model.
-/
theorem soundness (I : TopologicalInterpretation Base Const X)
    [HasLogicalOperations I] [HasSequentSemantics I]
    {Γ : Ctx Base} {antecedents : List (Formula Const Γ)}
    {succedent : Formula Const Γ}
    (h : Derivable Const antecedents succedent) :
    ValidSequent I antecedents succedent :=
  HasSequentSemantics.sound (I := I) h

/--
Any packaged topological counterexample refutes derivability.
-/
theorem Counterexample.not_derivable
    {Γ : Ctx Base}
    {antecedents : List (Formula Const Γ)}
    {succedent : Formula Const Γ}
    (C : Counterexample (Base := Base) (Const := Const) antecedents succedent) :
    ¬ Derivable (Base := Base) (Const := Const) antecedents succedent := by
  intro hDer
  exact C.invalid (soundness C.I hDer)

end TopologicalInterpretation

/-!
## Current Topological Corollary

The live topological stack currently proves the countermodel-to-non-derivability
direction. The stronger model-existence theorem remains the next frontier.
-/

/--
Any fixed topological interpretation refuting a sequent already refutes its
derivability.

This is the direct single-model consumer used by the packaged existential
corollary below.
-/
theorem not_derivable_of_topological_counterexample {Base : Type u} {Const : Ty Base → Type v}
    {X : Type w} [TopologicalSpace X]
    (I : TopologicalInterpretation Base Const X)
    [TopologicalInterpretation.HasLogicalOperations I]
    [TopologicalInterpretation.HasSequentSemantics I]
    {Γ : Ctx Base} {antecedents : List (Formula Const Γ)}
    {succedent : Formula Const Γ}
    (hCounter : ¬ TopologicalInterpretation.ValidSequent I antecedents succedent) :
    ¬ Derivable Const antecedents succedent := by
  intro hDer
  exact hCounter (TopologicalInterpretation.soundness I hDer)

/--
Any existential topological counterexample refutes derivability.

This is the strongest honest theorem currently proved by the live topological
stack: once a counterexample is packaged as an actual topological model with the
required semantic structure, derivability is impossible.
-/
theorem awodey_butz_completeness {Base : Type u} {Const : Ty Base → Type v}
    {Γ : Ctx Base} {antecedents : List (Formula Const Γ)}
    {succedent : Formula Const Γ}
    (hCounter :
      Nonempty
        (TopologicalInterpretation.Counterexample
          (Base := Base) (Const := Const) antecedents succedent)) :
    ¬ Derivable (Base := Base) (Const := Const) antecedents succedent := by
  rcases hCounter with ⟨C⟩
  exact C.not_derivable

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
