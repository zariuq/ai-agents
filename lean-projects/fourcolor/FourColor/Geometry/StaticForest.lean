import FourColor.Triangulation

namespace FourColor
namespace Geometry

open scoped BigOperators
open Classical

noncomputable section

-- Variable declarations omitted - types are inferred from usage

/--
Core data for the “static dual forest” transport path: a single fixed
spanning forest on the interior faces together with the parity and peel
witness needed to build `LeafPeelData`.
-/
structure StaticDual
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] where
  zero : ZeroBoundaryData V E
  gamma : Color := (1, 0)
  internalFaces : Finset (Finset E)
  boundary_mem_zero :
    ∀ {f}, f ∈ internalFaces →
      faceBoundaryChain (γ := gamma) f ∈ zero.zeroBoundarySet
  tight :
    ∀ {x}, x ∈ zero.zeroBoundarySet → support₁ x = ∅ → x = zeroChain (E := E)
  peelWitness :
    ∀ {x : E → Color},
      x ∈ zero.zeroBoundarySet →
      support₁ x ≠ ∅ →
      ∃ f ∈ internalFaces, ∃ x',
        x' ∈ zero.zeroBoundarySet ∧
        x = x' + faceBoundaryChain (γ := gamma) f ∧
        Finset.card (support₁ x') < Finset.card (support₁ x)

namespace StaticDual

variable [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E]

/-- Convert a `StaticDual` witness to `LeafPeelData`. -/
def toLeafPeelData (D : StaticDual (V := V) (E := E)) :
    LeafPeelData V E where
  zero := D.zero
  gamma := D.gamma
  internalFaces := D.internalFaces
  boundary_mem_zero := D.boundary_mem_zero
  tight := D.tight
  peel := by
    intro x hx hsupp
    classical
    exact D.peelWitness hx hsupp

end StaticDual

end -- noncomputable section
end Geometry
end FourColor
