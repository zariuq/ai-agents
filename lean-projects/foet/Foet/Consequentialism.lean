import Foet.UtilitarianToValue
import Foet.UtilitarianToVirtue

set_option autoImplicit false

namespace Foet

universe u v

/-
Consequentialism (ESOWIKI): coarse, Lean-first.

In the ontology, consequentialism says the moral status of an action depends only on
its consequences.  At this stage we keep “consequences” abstract as a signature `C`,
and say the evaluators (utility / moral value / virtue-aspect) are functions of that
signature.

This gives us a place to hang *type-checkable plumbing properties* before we import a
full SUMO `Consequence` hierarchy.
-/

def ConsequenceSignature (World : Type u) (C : Type v) : Type (max u v) :=
  World → Formula World → C

def ConsequentialistUtility {World : Type u} {C : Type v}
    (semU : UtilityAssignmentSemantics World) (conseq : ConsequenceSignature World C) : Prop :=
  ∀ w φ ψ, conseq w φ = conseq w ψ → semU.utility w φ = semU.utility w ψ

def ConsequentialistValue {World : Type u} {C : Type v}
    (semV : ValueSemantics World) (conseq : ConsequenceSignature World C) : Prop :=
  ∀ w φ ψ, conseq w φ = conseq w ψ → ∀ m, semV.morally m φ w ↔ semV.morally m ψ w

def ConsequentialistVirtueTarget {World : Type u} {C : Type v}
    (semT : VirtueTargetSemantics World) (conseq : ConsequenceSignature World C) : Prop :=
  ∀ w φ ψ, conseq w φ = conseq w ψ → ∀ a, semT.targets a φ w ↔ semT.targets a ψ w

theorem consequentialistValue_of_consequentialistUtility {World : Type u} {C : Type v}
    (semU : UtilityAssignmentSemantics World) (conseq : ConsequenceSignature World C) :
    ConsequentialistUtility semU conseq →
      ConsequentialistValue (valueSemanticsOfUtility World semU) conseq := by
  intro hU w φ ψ hEq m
  have hUtil : semU.utility w φ = semU.utility w ψ :=
    hU w φ ψ hEq
  cases m <;> simp [valueSemanticsOfUtility, hUtil]

theorem consequentialistVirtueTarget_of_consequentialistUtility {World : Type u} {C : Type v}
    (semU : UtilityAssignmentSemantics World) (conseq : ConsequenceSignature World C) :
    ConsequentialistUtility semU conseq →
      ConsequentialistVirtueTarget (virtueTargetSemanticsOfUtility World semU) conseq := by
  intro hU w φ ψ hEq a
  have hUtil : semU.utility w φ = semU.utility w ψ :=
    hU w φ ψ hEq
  cases a <;> simp [virtueTargetSemanticsOfUtility, virtueAspectToMoralValue, hUtil]

end Foet

