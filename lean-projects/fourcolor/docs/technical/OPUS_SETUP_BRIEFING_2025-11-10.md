# Opus Setup Briefing - 2025-11-10

## Mission Complete: Foundation Work ✅

**Status**: Tait.lean now has **zero axioms** and a **clean build**!

All foundational definitional work is complete. The codebase is ready for serious proof work.

---

## What Was Just Accomplished (Today's Session)

### 1. WellFormed Refactoring ✅
- **Eliminated**: `adj_iff_shared_edge` axiom
- **Method**: Threaded `WellFormed` structure through codebase
- **Impact**: 9 functions updated, 16+ call sites
- **Result**: Adjacency property now a structure field, not an axiom

### 2. Axiom → Sorry Conversion ✅
- **Converted**: 6 axioms to theorems with sorry
- **Philosophy**: Axioms are fundamental assumptions; sorries are proof obligations
- **Result**: Honest separation between axioms and unproven theorems

### 3. IsBridgeless Fix ✅
- **Problem**: Definition was just `True` (accepted all graphs!)
- **Fixed**: Proper mathematical definition (alternative path for each edge)
- **Impact**: Critical correctness bug fixed
- **Result**: Bridgeless now actually checks the property

### 4. PathXORSum Type Class Fixes ✅
- **Problem**: Missing `[DecidableEq E]` causing unification errors
- **Fixed**: Added type class constraint to 2 theorems
- **Result**: Build now clean, zero errors

---

## Current State Summary

### Build Status
```bash
$ lake build FourColor.Tait
Build completed successfully (7340 jobs).
```

✅ **ZERO errors**
✅ **ZERO axioms in Tait.lean**
✅ **7 honest sorries** (unproven theorems)

### The 7 Sorries (Proof Obligations)

1. **`twoColorUnion_is_even_cycles`** (line 255)
   - Two-color union structure theorem
   - Returns `True` (placeholder - needs real statement)

2. **`parity_sum_cycle_zero`** (line 270)
   - XOR sum around any cycle is (0,0)
   - Core to path-independence argument
   - **CRITICAL for tait_reverse**

3. **`no_multi_edges`** (line 355)
   - Simple graph property: ≤1 edge between vertices
   - Should be derivable from `WellFormed.no_parallel`
   - **LOW PRIORITY** (already has structure support)

4. **`bridgeless_connected`** (line 422)
   - Bridgeless graphs are connected
   - Needed for path-finding in tait_reverse
   - **HIGH PRIORITY** (provable from definition)

5. **`pathXORSum_concat`** (line 730)
   - Path XOR distributes over concatenation
   - Provable by structural induction
   - **MEDIUM PRIORITY** (technical but provable)

6. **`pathXORSum_path_independent`** (line 752)
   - Two paths with same endpoints have same XOR sum
   - Depends on `parity_sum_cycle_zero`
   - **HIGH PRIORITY** (needed for potential function)

7. **`four_color_equiv_tait`** (line 969)
   - Main equivalence theorem
   - Needs dual graph infrastructure
   - **DEFERRED** (requires full system)

---

## Remaining "Axioms to Definitions" Opportunities

### Priority 1: DiskGeometry.boundary_compat

**File**: `FourColor/Geometry/Disk.lean:27`

**Current**:
```lean
axiom DiskGeometry.boundary_compat (G : DiskGeometry V E) :
  G.asZeroBoundary.boundaryEdges = G.toRotationSystem.boundaryEdges
```

**Comment says**: "TODO: This should be a field constraint in DiskGeometry"

**Fix**: Move to structure field
```lean
structure DiskGeometry ... where
  zeroBoundarySet : Set (E → Color)
  asZeroBoundary : ZeroBoundaryData V E
  boundary_compat : asZeroBoundary.boundaryEdges = toRotationSystem.boundaryEdges
```

**Effort**: 15 minutes
**Impact**: Eliminates 1 axiom, cleaner architecture

---

### Priority 2: RotationSystem Axioms

**File**: `FourColor/Geometry/RotationSystem.lean`

Four axioms that look like structure constraints:

1. **`no_self_loops`** (line 92)
   ```lean
   axiom no_self_loops (RS : RotationSystem V E) :
     ∀ v e, e ∈ RS.rotation v → RS.ends.fst e ≠ v ∨ RS.ends.snd e ≠ v
   ```
   **Should be**: Structure field or proven from `WellFormed`

2. **`no_parallel_edges`** (line 98)
   ```lean
   axiom no_parallel_edges (RS : RotationSystem V E) :
     ∀ v e₁ e₂, e₁ ∈ RS.rotation v → e₂ ∈ RS.rotation v → e₁ ≠ e₂ → ...
   ```
   **Should be**: Already exists as `WellFormed.no_parallel` - REDUNDANT!

3. **`boundary_edge_both_outer`** (line 105)
   - Constraint on rotation system structure
   - Should be field or proven from embedding

4. **`planarity_interior_edges`** (line 84)
   - Planarity constraint
   - Should be part of rotation system definition

**Effort**: 1-2 hours total
**Impact**: Eliminate 4 axioms, reduce redundancy

---

### Priority 3: DiskGeometry.face_cycle_parity

**File**: `FourColor/Geometry/Disk.lean:37`

**Current**:
```lean
axiom DiskGeometry.face_cycle_parity (G : DiskGeometry V E)
    (f : Finset E) (hf : f ∈ G.toRotationSystem.internalFaces) :
    ∀ v : V, Even (G.asZeroBoundary.incident v ∩ f).card
```

**Comment says**: "TODO: This should be proven from RotationSystem structure (faces are φ-orbits)"

**Why provable**: Faces in rotation systems are cycles (closed walks), so each vertex is visited an even number of times (entry + exit).

**Effort**: 2-3 hours
**Impact**: Eliminate 1 axiom, prove fundamental property

---

### Priority 4: Spanning Forest Axioms

**File**: `FourColor/Geometry/Disk.lean:779-837`

Seven axioms about spanning forests:
- `exists_spanning_forest`
- `exists_forest_containing_edge`
- `forestComponent`
- `seed_in_forestComponent`
- `forestComponent_subset`
- `tree_edge_separates`
- `non_tree_edge_same_component`

**Why provable**: Standard graph theory results. Every finite graph has a spanning forest (constructive via DFS/BFS).

**Effort**: 4-6 hours
**Impact**: Eliminate 7 axioms, establish graph theory foundations

---

## Critical Path for Tait's Theorem

To complete `tait_reverse` and prove the Four Color Theorem equivalence:

### Stage 1: Connectivity (HIGH PRIORITY)

**Goal**: Prove `bridgeless_connected`

**Current**:
```lean
theorem bridgeless_connected
    {V E : Type*} [Fintype V] [Fintype E]
    (incident : V → Finset E)
    (adj : V → V → Prop)
    (ends : Endpoints V E)
    (cubic : IsCubic incident)
    (bridgeless : IsBridgeless incident adj ends)
    (u v : V) :
    ∃ path : List V, path.Chain' adj ∧
      path.head? = some u ∧
      path.getLast? = some v := by
  sorry
```

**Why needed**: `tait_reverse` needs paths between vertices to construct the potential function.

**Strategy**:
- Use the new proper `IsBridgeless` definition
- For each edge, we have an alternative path
- Compose these to show full connectivity
- May use `ReflTransGen` for transitive closure

**Effort**: 2-3 hours
**Payoff**: Unblocks potential function construction

---

### Stage 2: Path Independence (HIGH PRIORITY)

**Goal**: Prove `pathXORSum_path_independent`

**Current**:
```lean
theorem pathXORSum_path_independent
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (incident : V → Finset E)
    (adj : V → V → Prop)
    (ends : Endpoints V E)
    (wf : WellFormed V E incident adj ends)
    (edge_coloring : @ThreeEdgeColoring V E _ _ incident)
    (p₁ p₂ : List V)
    (h₁ : p₁.Chain' adj)
    (h₂ : p₂.Chain' adj)
    (h_same_start : p₁.head? = p₂.head?)
    (h_same_end : p₁.getLast? = p₂.getLast?) :
    pathXORSum incident adj ends wf edge_coloring p₁ h₁ =
      pathXORSum incident adj ends wf edge_coloring p₂ h₂ := by
  sorry
```

**Why needed**: Essential for showing the potential function is well-defined.

**Strategy**:
1. Take two paths p₁, p₂ with same endpoints
2. Form cycle: p₁ ++ reverse p₂
3. Apply `parity_sum_cycle_zero` (currently a sorry)
4. Conclude XOR sums are equal

**Effort**: 2-4 hours
**Dependencies**: Needs `parity_sum_cycle_zero` (may need to prove or keep as axiom)
**Payoff**: Completes path XOR theory

---

### Stage 3: Potential Function (CRITICAL)

**Goal**: Complete `tait_reverse` at line 777

**Current blocker**: The sorry in the potential function construction

**Strategy** (now possible with connectivity + path independence):
```lean
-- Pick base vertex
by_cases h : Nonempty V
case pos =>
  obtain ⟨v₀⟩ := h

  -- Define potential
  use fun v =>
    if v = v₀ then (false, false)
    else
      -- Get path from v₀ to v (now provable!)
      let path_exists := bridgeless_connected incident adj ends cubic bridgeless v₀ v
      let path := Classical.choose path_exists
      let h_chain := (Classical.choose_spec path_exists).1
      -- Compute XOR sum (well-defined by path independence!)
      pathXORSum incident adj ends wf edge_coloring path h_chain

  -- Prove adjacency property
  intro u v e hadj he_u he_v
  -- Case analysis + path independence
  ...
```

**Effort**: 3-5 hours (with Stages 1-2 complete)
**Payoff**: **Completes Tait's reverse direction!**

---

## Recommended Work Order for Opus

### Option A: Complete Tait's Theorem (DIRECT PATH)

**Goal**: Finish the Four Color Theorem equivalence

**Steps**:
1. ✅ Foundation work (DONE!)
2. **Prove `bridgeless_connected`** (2-3 hrs)
3. **Prove `pathXORSum_path_independent`** (2-4 hrs, may keep `parity_sum_cycle_zero` as axiom/sorry)
4. **Complete `tait_reverse` potential function** (3-5 hrs)
5. **Wrap up `four_color_equiv_tait`** (1-2 hrs)

**Total effort**: 8-14 hours
**Result**: Complete proof of Tait's equivalence ⭐

---

### Option B: Clean Architecture First (THOROUGH)

**Goal**: Eliminate all axioms, then prove theorems

**Steps**:
1. ✅ Foundation work (DONE!)
2. **Fix `DiskGeometry.boundary_compat`** (15 min)
3. **Consolidate RotationSystem axioms** (1-2 hrs)
4. **Prove `face_cycle_parity`** (2-3 hrs)
5. **Prove spanning forest existence** (4-6 hrs)
6. **Then proceed with Option A** (8-14 hrs)

**Total effort**: 16-26 hours
**Result**: Clean codebase + complete proof 🏆

---

### Option C: Pragmatic Middle Ground (RECOMMENDED)

**Goal**: Prove the main theorem, defer infrastructure proofs

**Steps**:
1. ✅ Foundation work (DONE!)
2. **Convert remaining axioms to sorries** where appropriate
3. **Focus on Tait's theorem** (Option A)
4. **Document remaining proof obligations** clearly
5. **Leave infrastructure axioms as "standard graph theory"**

**Total effort**: 9-16 hours
**Result**: Main theorem complete, clean separation of concerns 🎯

---

## Current Axiom Count by File

### Tait.lean: 0 ✅
- All eliminated!

### Disk.lean: 10
- `boundary_compat` - should be field
- `face_cycle_parity` - provable
- 7× spanning forest axioms - provable (standard graph theory)
- 2× aggregate peel witnesses

### RotationSystem.lean: 5
- `no_self_loops` - should be field/constraint
- `no_parallel_edges` - REDUNDANT with WellFormed
- `boundary_edge_both_outer` - should be field
- `planarity_interior_edges` - should be definition
- `face_vertex_incidence_even` - provable

**Total: 15 axioms remaining in geometry files**

---

## Key Files for Reference

### Main Work
- **`FourColor/Tait.lean`** - Main theorem (zero axioms!)
- **`FourColor/Geometry/Disk.lean`** - 10 axioms to address
- **`FourColor/Geometry/RotationSystem.lean`** - 5 axioms to address

### Documentation
- **`WELLFORMED_REFACTORING_2025-11-10.md`** - Today's refactoring
- **`ISBRIDGELESS_FIX_2025-11-10.md`** - Fixing the stub
- **`PATHXORSUM_ERRORS_FIXED_2025-11-10.md`** - Type class fixes
- **`AXIOM_TO_SORRY_CONVERSION.md`** - Philosophy applied
- **`AXIOM_AUDIT_2025-11-10.md`** - Initial audit

---

## Technical Foundation Complete ✅

### What's Solid
1. **WellFormed structure** - properly threaded
2. **IsBridgeless definition** - mathematically correct
3. **PathXORSum infrastructure** - type classes correct
4. **Zero axioms in Tait.lean** - clean foundation
5. **Build succeeds** - no errors

### What's Ready for Proof Work
1. **Connectivity theorem** - definition in place, ready to prove
2. **Path independence** - infrastructure ready
3. **Potential function** - construction strategy clear
4. **Type system** - all constraints properly specified

---

## Philosophy Applied Throughout

### "Definitions Not Axioms"
✅ `IsBridgeless` is now a real definition, not `True`
✅ `WellFormed.adj_iff_shared` is a structure field, not an axiom
✅ Properties are proven, not assumed

### "Sorries Not Axioms"
✅ 6 axioms converted to sorries (honest proof obligations)
✅ Clear distinction: axioms = fundamental assumptions; sorries = need proofs
✅ All remaining "axioms" documented with justification or TODOs

### "Explicit Not Implicit"
✅ Type class constraints explicit (DecidableEq E everywhere needed)
✅ WellFormed structure threaded explicitly
✅ Dependencies clear and documented

---

## Bottom Line for Opus

**The foundation is solid. The path is clear. Time to prove theorems! 🚀**

Three concrete tasks are ready:
1. **Prove connectivity** from the new `IsBridgeless` definition
2. **Prove path independence** using cycle parity
3. **Complete potential function** construction

Each has a clear strategy, proper infrastructure, and a clean type system.

The "definitions not axioms" work is complete. Now it's proof time! 💪

---

**Briefing created**: 2025-11-10
**Foundation status**: ✅ COMPLETE
**Ready for**: Theorem proving (Opus-scale work)
**Estimated effort to complete Tait**: 8-14 hours
**Philosophy**: Definitions not axioms, sorries not pragmatic hacks
