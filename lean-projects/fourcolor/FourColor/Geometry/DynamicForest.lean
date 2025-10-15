import FourColor.Triangulation
import FourColor.Geometry.Disk
import FourColor.GraphTheory.SpanningForest
import FourColor.KernelExtras
import Mathlib

namespace FourColor
namespace Geometry

open scoped BigOperators
open Classical

noncomputable section

/-
The **dynamic dual forest** transport path packages exactly the hypotheses
required to recover the `LeafPeelData` expected by Lemma 4.5.  The dynamic
approach supplies, for every finite set `S` of faces, a spanning forest
`forestOn S`; the leaf-peel witness is extracted locally from that forest.

This file sets up the interface.  Proving that a concrete planar disc
embedded graph satisfies these hypotheses is deferred to later development.
-/

variables {V E : Type*}

namespace DynamicForest

open Geometry
open Finset
open GraphTheory

/-- Bundle for the dynamic-forest peel construction using the dynamic dual forest argument. -/
structure Data
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] where
  G : DiskGeometry V E
  gamma : Color := (1,0)
  gamma_eq : gamma = (1,0)  -- Constraint: gamma must be (1,0) for support₁ to work correctly
  E2 : ∀ {e}, e ∉ G.D.boundaryEdges → (G.facesIncidence e).card ≤ 2  -- Two-incidence axiom
  /-- Tightness input: if a zero-boundary chain has empty γ-support (γ=(1,0)), it is zero. -/
  tight : ∀ {x : E → Color}, x ∈ G.D.zeroBoundarySet → support₁ x = ∅ → x = zeroChain

variable [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E]

/-- Faces that meet the current γ-support (support₁). -/
def facesTouching (D : Data (V := V) (E := E)) (x : E → Color) : Finset (Finset E) :=
  D.G.internalFaces.filter (fun f => (f ∩ support₁ x).Nonempty)

/-- If `f` belongs to `facesTouching x`, then `f` meets `support₁ x`. -/
lemma facesTouching_mem_implies_inter_nonempty
  (D : Data (V := V) (E := E)) {x : E → Color} {f : Finset E}
  (hfS : f ∈ facesTouching (D := D) x) :
  (f ∩ support₁ x).Nonempty := by
  classical
  unfold facesTouching at hfS
  simpa using (Finset.mem_filter.mp hfS).2

/-- Induced dual adjacency on a face subset `S`. -/
def adjOn (D : Data (V := V) (E := E)) (S : Finset (Finset E)) (f g : Finset E) : Prop :=
  f ∈ S ∧ g ∈ S ∧ D.G.adj f g

/-- Degree of a face `f` in the induced dual relation on `S`. -/
noncomputable def degreeOn (D : Data (V := V) (E := E)) (S : Finset (Finset E)) (f : Finset E) : Nat :=
  ((S.erase f).filter (fun g => D.G.adj f g)).card

-- (Removed unused heavy lemma; use GraphTheory.exists_leaf_face or
-- GraphTheory.exists_leaf_face_trivial where needed.)

/-- Package the dynamic-forest construction as `LeafPeelData`. -/
def toLeafPeelData (D : Data (V := V) (E := E)) :
    LeafPeelData V E where
  zero := D.G.D
  gamma := D.gamma
  internalFaces := D.G.internalFaces
  boundary_mem_zero := (D.G.faceBoundary_zeroBoundary (γ := D.gamma))
  tight := by
    intro x hx hsupp₁
    exact D.tight hx hsupp₁
  peel := by
    intro x hx hsupp
    classical
    -- Use the aggregated witness from Disk (which internally builds purified sum but returns single face)
    rcases D.G.exists_agg_peel_witness D.E2 (x := x) hx hsupp with
      ⟨f, hf, x', hx', hx_eq, hlt⟩
    exact ⟨f, hf, x', hx', by
      -- gamma is (1,0) by construction of D
      simpa [D.gamma_eq] using hx_eq, hlt⟩

/-- Package the dynamic-forest construction as `LeafPeelSumData` (multi-face peel version).
This is the **direct** formulation that matches the paper's approach (§4.2, Lemma 4.8). -/
def toLeafPeelSumData (D : Data (V := V) (E := E)) :
    LeafPeelSumData V E where
  zero := D.G.D
  gamma := D.gamma
  internalFaces := D.G.internalFaces
  boundary_mem_zero_sum := by
    intro S hS
    exact D.G.toggleSum_mem_zero hS
  tight := by
    intro x hx hsupp₁
    exact D.tight hx hsupp₁
  peel_sum := by
    intro x hx hsupp
    classical
    -- Use the multi-face aggregated witness from Disk
    rcases D.G.exists_agg_peel_witness_sum D.E2 (x := x) hx hsupp with
      ⟨S₀, hS₀_ne, hS₀_sub, x', hx', hx_eq, hlt⟩
    exact ⟨S₀, hS₀_ne, hS₀_sub, x', hx', by
      -- Rewrite using toggleSum definition
      rw [hx_eq]
      congr 1
      -- DiskGeometry.toggleSum G (1,0) S₀ = ∑ f ∈ S₀, faceBoundaryChain (γ := (1,0)) f
      unfold DiskGeometry.toggleSum
      -- gamma is (1,0) by construction of D
      simp [D.gamma_eq], hlt⟩

end DynamicForest

end -- noncomputable section
end Geometry
end FourColor
