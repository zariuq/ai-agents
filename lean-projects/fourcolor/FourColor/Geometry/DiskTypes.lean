/-
Copyright (c) 2025 Zar Goertzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zar Goertzel
-/

import FourColor.Triangulation
import FourColor.Geometry.RotationSystem

/-!
# Disk Geometry Base Types

This file contains the core type definitions for disk geometry that are needed
by both Disk.lean and DualForest.lean, breaking the circular import dependency.

## Main Definitions

- `DiskGeometry`: Disk geometry structure extending rotation system
- `SpanningForest`: Spanning forest structure on the dual graph
- `dualAdjacent`: Face adjacency in the dual graph
- `NoDigons`: Property asserting no two faces share multiple edges

-/

namespace FourColor

open Finset BigOperators Relation
open FourColor.Geometry
open FourColor.Geometry.RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Disk geometry structure extending planar geometry with disk topology -/
structure DiskGeometry (V E : Type*) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] extends
    PlanarGeometry V E where
  /-- Zero-boundary set: colorings that sum to 0 on the boundary -/
  zeroBoundarySet : Set (E → Color)
  /-- Zero-boundary data interface (for compatibility with LeafPeelData) -/
  asZeroBoundary : ZeroBoundaryData V E
  /-- **Compatibility constraint**: The boundary edges in asZeroBoundary match those in toRotationSystem.
  This ensures consistency between the two boundary representations. -/
  boundary_compat : asZeroBoundary.boundaryEdges = toRotationSystem.boundaryEdges
  /-- **Incident edges correctness**: The abstract incident function from ZeroBoundaryData
  must match the actual graph structure from the rotation system. This ensures that
  the zero-boundary algebra and combinatorial map describe the same graph. -/
  incident_compat :
    ∀ v : V, ∀ e : E, e ∈ asZeroBoundary.incident v ↔
      ∃ d : toRotationSystem.D,
        toRotationSystem.edgeOf d = e ∧ toRotationSystem.vertOf d = v
  /-- **Face cycle parity**: For any internal face f and any vertex v, the number of edges
  in f incident to v is even. This captures that faces are cycles in the planar dual:
  each vertex on the boundary is touched exactly 0 or 2 times (entering and leaving). -/
  face_cycle_parity :
    ∀ {f : Finset E}, f ∈ toRotationSystem.internalFaces →
    ∀ v : V, Even (asZeroBoundary.incident v ∩ f).card

variable (G : DiskGeometry V E)

/-- Face adjacency in the interior dual graph: two internal faces are adjacent
if they share an interior edge. -/
def dualAdjacent (G : DiskGeometry V E) (f g : Finset E) : Prop :=
  f ∈ G.toRotationSystem.internalFaces ∧
  g ∈ G.toRotationSystem.internalFaces ∧
  f ≠ g ∧
  ∃ e, e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f ∧ e ∈ g

/-- A spanning forest on the interior dual graph.

This structure represents a spanning forest of the dual graph (where vertices are internal faces
and edges connect faces that share an interior edge).

The key property is the `dichotomy`: for any interior edge e, either:
1. e is in the tree
2. Adding e would create a cycle (the two faces it connects are already tree-connected)
-/
structure SpanningForest (G : DiskGeometry V E) where
  tree_edges : Finset E
  -- Tree edges are interior edges
  tree_edges_interior : ∀ e ∈ tree_edges, e ∉ G.toRotationSystem.boundaryEdges
  -- For any interior edge e: either e is in tree, or adding e creates a cycle
  dichotomy : ∀ e, e ∉ G.toRotationSystem.boundaryEdges →
    e ∈ tree_edges ∨ (∃ f g, dualAdjacent G f g ∧ e ∈ f ∧ e ∈ g ∧
      -- f and g are connected via tree edges
      ReflTransGen (fun f' g' => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ f' ∧ e' ∈ g') f g)

/-- Property that no two distinct internal faces share more than one interior edge.
This is the "no digons" or "simple dual graph" property. -/
def NoDigons (G : DiskGeometry V E) : Prop :=
  ∀ {f g : Finset E},
    f ∈ G.toRotationSystem.internalFaces →
    g ∈ G.toRotationSystem.internalFaces →
    f ≠ g →
    ∀ {e1 e2 : E},
      e1 ≠ e2 →
      e1 ∉ G.toRotationSystem.boundaryEdges →
      e2 ∉ G.toRotationSystem.boundaryEdges →
      e1 ∈ f → e1 ∈ g →
      e2 ∈ f → e2 ∈ g →
      False

end FourColor
