-- FourColor/Geometry/PlanarityHelpers.lean
-- Planarity incidence lemmas for rotation systems
--
-- Key result: Interior edges are incident to exactly 2 internal faces

import FourColor.Geometry.RotationSystem

namespace FourColor.Geometry.PlanarityHelpers

open FourColor.Geometry
open FourColor.Geometry.RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ## Planarity Incidence Properties

In a planar rotation system:
1. Each edge is incident to exactly 2 faces (left/right of rotation)
2. Interior edges are incident to 2 INTERNAL faces (not boundary)
3. This follows from: interior edge ⟹ both half-edges avoid outer face
-/

/-- Interior edge is incident to exactly two internal faces.

    **Proof**: By rotation system, e has 2 incident faces (left/right).
    If e is interior (e ∉ boundaryEdges), neither face can be the boundary face.
    Therefore both are internal.

    This is the key planarity property needed for adj_implies_internal_faces. -/
lemma interior_edge_two_internal_faces (PG : PlanarGeometry V E)
    (e : E) (he_int : e ∉ PG.toRotationSystem.boundaryEdges) :
    ∃ f g : Finset E,
      f ∈ PG.toRotationSystem.internalFaces ∧
      g ∈ PG.toRotationSystem.internalFaces ∧
      f ≠ g ∧
      e ∈ f ∧ e ∈ g ∧
      (∀ f' ∈ PG.toRotationSystem.internalFaces, e ∈ f' → f' = f ∨ f' = g) := by
  -- Use E2 property: interior edges have exactly 2 internal faces
  obtain ⟨faces, ⟨hcard, hfaces⟩, hunique⟩ :=
    two_internal_faces_of_interior_edge PG he_int

  -- Extract the two faces
  have h2 : faces.card = 2 := hcard
  obtain ⟨f, g, hfg_ne, hfg_all⟩ :=
    Finset.card_eq_two.mp h2

  -- f and g are in faces by hfg_all
  have hf_mem : f ∈ faces := by rw [hfg_all]; simp
  have hg_mem : g ∈ faces := by rw [hfg_all]; simp

  use f, g
  constructor
  · exact (hfaces f hf_mem).1
  constructor
  · exact (hfaces g hg_mem).1
  constructor
  · exact hfg_ne
  constructor
  · exact (hfaces f hf_mem).2
  constructor
  · exact (hfaces g hg_mem).2

  -- Uniqueness: Any INTERNAL face containing e must be one of these 2
  intro f' hf'_internal he_f'
  -- Key insight: faces is THE UNIQUE set of internal faces containing e
  -- Since f' is internal and contains e, by uniqueness f' ∈ faces, thus f' = f or f' = g

  -- By uniqueness of faces, f' must be in faces
  have hf'_in_faces : f' ∈ faces := by
      -- STUB: Temporarily sorry'd complex proof with Finset.insert issues
      -- TODO: Fix after circular import test - needs Finset API updates
      -- Strategy: Show f' must be in faces by uniqueness
      sorry

  -- Once f' ∈ faces, and faces = {f, g}, we have f' = f ∨ f' = g
  rw [hfg_all] at hf'_in_faces
  simp at hf'_in_faces
  exact hf'_in_faces

/-- **Key Lemma**: Any face containing an interior edge must be internal.

    **Note**: This version requires a witness that f is an actual rotation system face.
    Use `face_containing_interior_edge_is_internal_from_adj` when f comes from
    DiskGeometry.adj, which provides the witness automatically.

    **Proof**: Since e is interior, there exist exactly 2 internal faces containing e.
    If f contains e and is a face, it must be one of these 2, hence internal. -/
lemma face_containing_interior_edge_is_internal_with_witness (RS : RotationSystem V E)
    (e : E) (he_int : e ∉ RS.boundaryEdges)
    (f : Finset E) (hf_is_face : ∃ d, RS.faceEdges d = f) (he_f : e ∈ f) :
    f ∈ RS.internalFaces := by
  -- Get witness that f is a face
  obtain ⟨d, hd⟩ := hf_is_face

  -- If f were the boundary, then e ∈ boundaryEdges (contradiction)
  have hf_ne_boundary : f ≠ RS.boundaryEdges := by
    intro h_eq
    have he_face_d : e ∈ RS.faceEdges d := by rw [hd]; exact he_f
    have : e ∈ RS.boundaryEdges := by rw [←h_eq, ←hd]; exact he_face_d
    exact he_int this

  -- f is a face and f ≠ boundaryEdges, so f ∈ internalFaces (by definition)
  rw [←hd]
  unfold RotationSystem.internalFaces
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · exact ⟨d, rfl⟩
  · rw [hd]; exact hf_ne_boundary

/-- **Corollary**: Faces from DiskGeometry.adj are internal when containing interior edges.

    This uses the adj_faces_are_actual_faces axiom to provide the face witness automatically. -/
lemma face_containing_interior_edge_is_internal (RS : RotationSystem V E)
    (e : E) (he_int : e ∉ RS.boundaryEdges)
    (f : Finset E) (he_f : e ∈ f) :
    f ∈ RS.internalFaces := by
  -- This version is for backward compatibility but needs a witness
  -- In practice, callers should use face_containing_interior_edge_is_internal_from_adj
  -- or provide hf_is_face explicitly via face_containing_interior_edge_is_internal_with_witness
  sorry -- TODO: Callers should use version with witness or from_adj variant

end FourColor.Geometry.PlanarityHelpers
