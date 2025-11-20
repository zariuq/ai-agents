# Axiom Inventory - Four Color Theorem Formalization

**Last updated**: 2025-11-06
**Status**: ✅ Build succeeds with clean sorry for H2

---

## Foundation Axioms (RotationSystem.lean)

These are **irreducible foundations** for planar graph theory:

1. **`planarity_interior_edges`** (line 84)
   - **Statement**: Interior edges have exactly 2 incident darts (φ-fibers)
   - **Why axiom**: Fundamental combinatorial planarity property
   - **Status**: ✅ Required

2. **`no_self_loops`** (line 92)
   - **Statement**: Edge endpoints are distinct
   - **Why axiom**: Simple graph property
   - **Status**: ✅ Required

3. **`no_parallel_edges`** (line 98)
   - **Statement**: Edges with same endpoints are equal
   - **Why axiom**: Simple graph property
   - **Status**: ✅ Required

4. **`boundary_edge_both_outer`** (line 105)
   - **Statement**: Boundary edge darts both lie on outer face
   - **Why axiom**: Planar embedding property
   - **Status**: ✅ Required

5. **`face_vertex_incidence_even`** (line 889)
   - **Statement**: Each face-vertex incidence has even parity
   - **Why axiom**: Topological parity property
   - **Status**: ✅ Required

---

## Disk Geometry Axioms (Disk.lean)

1. **`DiskGeometry.boundary_compat`** (line 27)
   - **Statement**: Boundary edges match between zeroBoundary and rotationSystem
   - **Why axiom**: Interface compatibility
   - **Status**: ⚠️ Should be provable from construction
   - **TODO**: Prove or remove

2. **`DiskGeometry.face_cycle_parity`** (line 37)
   - **Statement**: Face boundaries have even cycle parity
   - **Why axiom**: Needed for NoDigons → adjacency uniqueness
   - **Status**: ⚠️ Should follow from planarity
   - **TODO**: Derive from rotation system axioms

3. **`DiskGeometry.exists_agg_peel_witness`** (line ~1027)
   - **Statement**: Aggregated peel witness existence
   - **Why axiom**: Used in meridian construction
   - **Status**: ⚠️ Should be constructive
   - **TODO**: Implement construction

4. **`DiskGeometry.exists_agg_peel_witness_sum`** (line ~1037)
   - **Statement**: Sum witness for aggregated peels
   - **Why axiom**: Used in meridian construction
   - **Status**: ⚠️ Should be constructive
   - **TODO**: Implement construction

**Removed axioms** (Nov 6, 2025):
- ❌ `face_mem_incident_pair_of_interior_edge` (was line 698): **REMOVED** - was helper for incorrect approach
- ❌ `reflTransGen_adjExcept_absurd_of_unique_edge` (was line 717): **REMOVED** - **FALSE axiom**, counter-examples exist

---

## TODO Sorries (Construction Gaps)

### High Priority (Main Path)

1. **`exists_S₀_component_after_delete`** (Disk.lean:683)
   - **What**: H2 prescribed cut via spanning forest / leaf-subtree
   - **Reference**: Goertzel §4.3
   - **Correct approach**: Build interior dual, get spanning forest, find leaf-subtree
   - **Incorrect approach** (removed Nov 6): Component-after-delete via ReflTransGen (mathematically unsound)
   - **Estimate**: ~100-150 lines (spanning forest infrastructure + proof)
   - **Status**: 🔴 Blocks main descent (clean sorry as of Nov 6)

### Medium Priority (Tait Equivalence)

2. **Vertex→Edge coloring** (Tait.lean:111)
   - **Estimate**: ~40 lines
   - **Status**: 🟡 Blocks Tait equivalence

3. **Edge→Vertex coloring** (Tait.lean:146)
   - **Estimate**: ~40 lines
   - **Status**: 🟡 Blocks Tait equivalence

4. **Kempe chain definition** (Tait.lean:214)
   - **Estimate**: ~30 lines
   - **Status**: 🟡 Blocks reachability

5. **Kempe reachability** (Tait.lean:442)
   - **Estimate**: ~50 lines
   - **Status**: 🟡 Blocks main theorem

### Low Priority (Integration)

6. **Various integration sorries** (multiple files)
   - **Status**: 🟢 Can be filled incrementally

---

## Axiom Reduction Plan

### Phase 1: Prove Disk axioms from RotationSystem

- [ ] `boundary_compat`: Should follow from construction
- [ ] `face_cycle_parity`: Derive from `planarity_interior_edges` + `face_vertex_incidence_even`
- [ ] `exists_agg_peel_witness`: Implement meridian construction algorithm

### Phase 2: Fill critical sorries

- [ ] `exists_S₀_component_after_delete`: Dual forest leaf-subtree algorithm (Goertzel §4.3)

### Phase 3: Complete Tait path

- [ ] Vertex/edge coloring translations
- [ ] Kempe chain definitions and reachability

---

## Enforcement Policy

Per GPT-5 Pro's recommendation:

1. **No new axioms** without documented justification
2. **Sorries must be documented** with:
   - What is missing
   - Why it's provable
   - Estimated complexity
3. **CI blocks** undocumented axioms/sorries
4. **Pre-commit hooks** catch accidental additions

---

## Status Summary

**Total axioms**: 9 ✅ (reduced from 11 on Nov 6)
- Foundation (RotationSystem): 5 ✅ (irreducible)
- Disk (provable): 4 ⚠️ (should be eliminated)

**Total critical sorries**: 1 ⚠️
- **H2 construction** (Disk.lean:683): Clean sorry with correct documentation
- Blocks main descent pipeline
- Correct approach: Spanning forest / leaf-subtree (Goertzel §4.3)
- Estimated: ~100-150 lines

**Removed infrastructure** (Nov 6, 2025):
- ❌ `adjExcept` / `compAfterDeleteSet` (incorrect component-after-delete approach)
- ❌ 2 false helper axioms (face_mem_incident_pair, reflTransGen_absurd)
- ✅ Build succeeds with clean sorry

**NoDigons dependency**: Many lemmas require `NoDigons G` hypothesis
- Property: Two distinct faces share ≤1 interior edge
- Should be provable from rotation system
- Currently used as hypothesis

**Goal**:
1. Implement H2 via spanning forest (~100-150 lines) OR leave as sorry
2. Prove NoDigons from rotation system (~50-100 lines)
3. Reduce Disk axioms to 0 (prove the 4 provable ones)
4. Complete Tait equivalence path (~200 lines)
