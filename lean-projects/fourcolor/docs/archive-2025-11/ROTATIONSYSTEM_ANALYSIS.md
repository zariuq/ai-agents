# RotationSystem Foundational Properties Analysis

**Date**: 2025-11-17
**Finding**: The foundational sorries in RotationSystem.lean are not easily provable - they appear to be fundamental characterizing properties of planar embeddings that should be axioms.

---

## The Three Foundational Properties

### 1. `planarity_interior_edges` (line 88-93)
**What it says**: For interior edges, the two darts belong to different faces.

**Why it's fundamental**: This is THE defining property of a planar embedding. It says that edges don't cross - each interior edge separates two distinct faces. This property distinguishes planar from non-planar rotation systems.

**Can it be proved?**: NO - this is a characterizing axiom of planar embeddings. The rotation system structure alone doesn't guarantee planarity.

**Recommendation**: Should be an axiom or part of the RotationSystem structure for planar embeddings.

### 2. `no_parallel_edges` (line 103-121)
**What it says**: Different edges have different vertex pairs (simple graph property).

**Why it's needed**: The Four Color Theorem applies to simple planar graphs. Multi-edges would break many downstream proofs.

**Can it be proved?**: NO - this is a constraint on the type of graphs we're considering. The rotation system structure doesn't prevent parallel edges.

**Recommendation**: Should be an axiom or constraint in the RotationSystem structure.

### 3. `boundary_edge_both_outer` (line 125-151)
**What it says**: If an edge is on the boundary, both its darts belong to the outer face.

**Progress made**: Partial proof started, but requires a lemma about dart pairing that's also unproven.

**Blocker**: Need `dartsOn_eq_pair` lemma (line 206-209, commented out with sorry).

**Can it be proved?**: MAYBE - but requires proving that the two darts of an edge are exactly {d, α(d)}, which requires careful analysis of the edge_fiber_two axiom.

---

## Additional Unproven Properties

### 4. `dartsOn_eq_pair` (line 206-209, commented out)
**What it says**: The darts of edge e are exactly {d, α(d)} for any dart d of e.

**Why it's hard**: While edge_fiber_two says each edge has exactly 2 darts, and edge_alpha says α preserves edges, proving they form exactly this pair requires showing no other dart has the same edge.

### 5. `darts_of_edge` (line 169)
**Status**: Has sorry, extracts the two darts of an edge.

### 6. `edge_not_in_boundary` (line 907)
**Status**: Has sorry, complex boundary property.

---

## The Real Issue

These properties aren't "bugs to fix" - they're **fundamental axioms** about planar embeddings that the author left as sorries instead of making explicit axioms.

The rotation system structure provides:
- Darts, edges, vertices
- α (edge flip) and ρ (vertex rotation) permutations
- Basic properties like involutive α, edge preservation

But it does NOT guarantee:
- Planarity (edges don't cross)
- Simplicity (no parallel edges)
- Specific face boundary properties

---

## Recommendation

Instead of trying to prove these from first principles (which is impossible), we should either:

### Option A: Make them axioms
```lean
axiom planarity_interior_edges (RS : RotationSystem V E) : ...
axiom no_parallel_edges (RS : RotationSystem V E) : ...
axiom boundary_edge_both_outer (RS : RotationSystem V E) : ...
```

### Option B: Add them to the RotationSystem structure
```lean
structure RotationSystem ... where
  ...
  -- Planarity axioms
  planar_interior : ∀ e d, edgeOf d = e → e ∉ boundaryEdges → ...
  simple_graph : ∀ e e' d d', ...
  boundary_property : ∀ e d, ...
```

### Option C: Create PlanarRotationSystem type
```lean
structure PlanarRotationSystem extends RotationSystem where
  planar_interior : ...
  simple_graph : ...
  boundary_property : ...
```

---

## Why This Matters

**Everything** in the Four Color Theorem formalization depends on these properties:
- NoDigons depends on no_parallel_edges
- Disk properties depend on planarity_interior_edges
- SpanningForest depends on face separation properties

If we don't have these as proven or axiomatic properties, the entire formalization is built on sand.

---

## Conclusion

The foundational sorries in RotationSystem aren't bugs - they're unacknowledged axioms. They represent fundamental properties of planar embeddings that cannot be derived from the basic rotation system structure. They should be explicitly stated as axioms rather than left as sorries.

**Mario Carneiro would say**: "If it's an axiom, call it an axiom. Don't hide axioms as sorries."