import Foet.Consequentialism

set_option autoImplicit false

namespace Foet

universe u

/-
Hedonistic utilitarianism (ESOWIKI): utility is net pleasure minus pain.

We model this as a refinement of the utilitarian utility evaluator, with an explicit
pleasure/pain decomposition.
-/

structure HedonisticUtilitySemantics (World : Type u) : Type (max u 1) where
  pleasure : World → Formula World → Int
  pain : World → Formula World → Int

def HedonisticUtilitySemantics.toUtilityAssignmentSemantics (World : Type u)
    (semH : HedonisticUtilitySemantics World) : UtilityAssignmentSemantics World :=
  ⟨fun w φ => semH.pleasure w φ - semH.pain w φ⟩

def HedonisticUtilitySemantics.signature (World : Type u)
    (semH : HedonisticUtilitySemantics World) : ConsequenceSignature World (Int × Int) :=
  fun w φ => (semH.pleasure w φ, semH.pain w φ)

theorem hedonistic_consequentialist {World : Type u} (semH : HedonisticUtilitySemantics World) :
    ConsequentialistUtility (semH.toUtilityAssignmentSemantics World) (semH.signature World) := by
  intro w φ ψ hEq
  have hPleasure : semH.pleasure w φ = semH.pleasure w ψ := by
    have : (semH.pleasure w φ, semH.pain w φ) = (semH.pleasure w ψ, semH.pain w ψ) := hEq
    exact congrArg Prod.fst this
  have hPain : semH.pain w φ = semH.pain w ψ := by
    have : (semH.pleasure w φ, semH.pain w φ) = (semH.pleasure w ψ, semH.pain w ψ) := hEq
    exact congrArg Prod.snd this
  simp [HedonisticUtilitySemantics.toUtilityAssignmentSemantics, hPleasure, hPain]

end Foet

