# Session 2025-11-06: Cleanup of Incorrect H2 Component-After-Delete Approach

**Date**: 2025-11-06
**Duration**: ~1 hour
**Goal**: Remove incorrect component-after-delete infrastructure based on GPT-5 Pro's clarification
**Status**: ✅ **COMPLETE** - Build succeeds with clean sorry for H2

---

## Executive Summary

Based on GPT-5 Pro's clarification, we removed the incorrect component-after-delete infrastructure
that was attempting to construct `cutEdges G S' = {e0}` using ReflTransGen reachability.
The approach was mathematically unsound - the helper axiom claiming "faces sharing only e0 cannot
be connected via paths avoiding e0" is **FALSE**.

**What was removed**:
- `adjExcept` definition (restricted face adjacency)
- `compAfterDeleteSet` definition (reachability set)
- Transport lemmas (4 lemmas, ~50 lines)
- False helper axioms (2 axioms, ~30 lines)
- Complex timeout-prone proof (~160 lines)

**What remains**:
- Clean `sorry` for H2 with correct documentation
- Working support-aware bridge `cutEdges₁_filter_of_component_singleton`
- Working H3 descent lemma
- Complete aggregated peel pipeline

---

## Background: The Incorrect Approach

### What We Tried (Nov 5-6, 2025)

Following an initial interpretation of GPT-5 Pro's guidance, we implemented:

1. **`adjExcept G e0 f g`**: Two faces adjacent via interior edge ≠ e0
2. **`compAfterDeleteSet G e0 f0`**: Faces reachable from f0 via `adjExcept` paths
3. **Proof strategy**: Show `cutEdges G S' = {e0}` where S' = faces reachable from f0 avoiding e0

### The Fatal Flaw

The proof relied on a helper axiom:
```lean
axiom reflTransGen_adjExcept_absurd_of_unique_edge
    -- If f0, g0 share only e0, then ¬ ReflTransGen (adjExcept G e0) f0 g0
```

**This axiom is FALSE**. Two faces can share only one interior edge yet still be connected
by paths avoiding that edge in the dual graph. Counter-example:

```
   f0 --- e1 --- f1
    |             |
   e0            e2
    |             |
   g0 --- e3 --- f2
```

Here f0 and g0 share only e0, but f0 → f1 → f2 → g0 is a valid path avoiding e0.

---

## GPT-5 Pro's Clarification (Nov 6, 2025)

> **TL;DR**: The "support‑aware bridge" lemma is valid and already implemented...
> What doesn't hold: the attempt to get `cutEdges G S' = {e0}` by taking the component
> after deleting e0 in the dual. The helper axiom `reflTransGen_adjExcept_absurd_of_unique_edge`
> is **generally false**.

**What actually works**:
1. ✅ H2 produces S' with `cutEdges G S' = {e0}` (via spanning forest, not ReflTransGen)
2. ✅ Bridge lemma `cutEdges₁_filter_of_component_singleton` transports to support-aware
3. ✅ H3 `aggregated_toggle_strict_descent_at_prescribed_cut` performs descent

**Correct H2 construction** (per GPT-5 Pro):
- Use **spanning forest / leaf-subtree** approach from Goertzel §4.3
- Build interior dual graph
- Get spanning forest T
- Find leaf-subtree containing one face incident to e0
- That subtree's face-set has e0 as unique cut edge

---

## Changes Made

### 1. Removed Incorrect Infrastructure (Disk.lean:638-730)

**Deleted**:
```lean
-- adjExcept definition (~10 lines)
def adjExcept (G : DiskGeometry V E) (e0 : E) (f g : Finset E) : Prop :=
  f ∈ G.toRotationSystem.internalFaces ∧
  g ∈ G.toRotationSystem.internalFaces ∧
  (∃ e, e ≠ e0 ∧ e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f ∧ e ∈ g)

-- compAfterDeleteSet definition (~10 lines)
noncomputable def compAfterDeleteSet (G : DiskGeometry V E) (e0 : E) (f0 : Finset E) :
    Finset (Finset E) := ...

-- Transport lemmas (~50 lines total)
lemma seed_in_compAfterDeleteSet ...
lemma compAfterDeleteSet_subset_internalFaces ...
lemma mem_compAfterDeleteSet_iff ...
lemma compAfterDeleteSet_closed_under_adjExcept ...
```

**Replaced with**:
```lean
/-! ### REMOVED: Incorrect Component-After-Delete Infrastructure

⚠️ **Per GPT-5 Pro clarification (Nov 6, 2025)**: The component-after-delete approach using
`adjExcept` and `ReflTransGen` does NOT provide a valid way to construct a set S' with
`cutEdges G S' = {e0}`.

**Why this approach fails**: Two faces f0, g0 that share only edge e0 can still be connected
by paths avoiding e0 in the dual graph. The attempted helper axiom
`reflTransGen_adjExcept_absurd_of_unique_edge` is **generally false**.

**Working architecture**:
- H2 produces S' with `cutEdges G S' = {e0}` (sorry below)
- Support-aware bridge `cutEdges₁_filter_of_component_singleton` transports to cutEdges₁
- H3 performs descent
-/
```

### 2. Removed False Helper Axioms (Disk.lean:666-703)

**Deleted**:
```lean
axiom reflTransGen_adjExcept_absurd_of_unique_edge
    (hNoDigons : NoDigons G)
    {e0 : E} {f0 g0 : Finset E}
    ...
    (hpath : ReflTransGen (adjExcept G e0) f0 g0) :
    False

lemma not_adjExcept_of_unique_shared_edge
    (hNoDigons : NoDigons G)
    {e0 : E} {f g : Finset E}
    ...
```

### 3. Simplified H2 Lemma (Disk.lean:683-692)

**Before** (~160 lines):
- Complex case analysis proof
- Relied on removed infrastructure
- Timeout errors (200000 heartbeats)
- Mathematically unsound

**After** (~10 lines):
```lean
lemma exists_S₀_component_after_delete
    (hNoDigons : NoDigons G)
    {e0 : E} (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges) :
    ∃ S' : Finset (Finset E),
      S' ⊆ G.toRotationSystem.internalFaces ∧
      S'.Nonempty ∧
      cutEdges G S' = {e0} := by
  -- TODO: Implement via spanning forest leaf-subtree (Goertzel §4.3)
  -- Estimated: ~100-150 lines (spanning forest infrastructure + leaf-subtree construction)
  sorry
```

---

## Working Architecture (Confirmed)

### Pipeline Flow

```
H2: exists_S₀_component_after_delete
  ↓ (produces S' with cutEdges G S' = {e0})

Bridge: cutEdges₁_filter_of_component_singleton
  ↓ (filters to support, transports singleton cut)

H3: aggregated_toggle_strict_descent_at_prescribed_cut
  ↓ (applies aggregated peel, strict descent)

Result: support₁ (x + toggleSum G (1,0) S₀) < support₁ x
```

### Key Lemmas Status

1. ✅ **`cutEdges₁_filter_of_component_singleton`** (line 702):
   - **Working**: Support-aware bridge lemma
   - **Purpose**: Transport singleton cut from cutEdges to cutEdges₁
   - **Key insight**: Support edges survive filtering (incident faces touch support)

2. ✅ **`aggregated_toggle_strict_descent_at_prescribed_cut`** (line 795):
   - **Working**: H3 descent lemma
   - **Purpose**: Given singleton cutEdges₁, prove strict support descent
   - **Status**: Complete proof

3. ⚠️ **`exists_S₀_component_after_delete`** (line 683):
   - **Status**: Clean `sorry` with correct documentation
   - **TODO**: Implement via spanning forest / leaf-subtree
   - **Estimate**: ~100-150 lines

---

## Build Status

**Before cleanup**:
- Timeouts at lines 786, 755
- Unknown identifiers (adjExcept, compAfterDeleteSet, etc.)
- Application type mismatches
- Deterministic timeout (200000 heartbeats)

**After cleanup**:
```bash
$ lake build FourColor.Geometry.Disk
✅ Build completed successfully (7339 jobs).
```

**Warnings** (all minor):
- Line 683: declaration uses 'sorry' (expected, documented)
- Several unused variable warnings (can be cleaned up later)
- Deprecated `Finset.not_mem_empty` (use `Finset.notMem_empty`)

---

## Axiom Inventory After Cleanup

### Foundation Axioms (RotationSystem.lean) - Unchanged

5 irreducible axioms:
1. `planarity_interior_edges`
2. `no_self_loops`
3. `no_parallel_edges`
4. `boundary_edge_both_outer`
5. `face_vertex_incidence_even`

### Disk Axioms - **REDUCED**

**Before** (Nov 5):
- 4 provable axioms (boundary_compat, face_cycle_parity, etc.)
- 2 FALSE helper axioms (face_mem_incident_pair, reflTransGen_absurd)
- **Total**: 11 axioms

**After** (Nov 6):
- 4 provable axioms (unchanged - these are legitimate TODOs)
- 0 helper axioms (removed the FALSE ones)
- **Total**: 9 axioms

### Critical Sorries - **UNCHANGED**

**H2 construction** (Disk.lean:683):
- `exists_S₀_component_after_delete`: ~100-150 lines via spanning forest
- This is the ONLY blocker for the main descent pipeline

---

## Key Insights

### 1. Mathematical Correctness > Implementation Speed

The component-after-delete approach seemed elegant but was mathematically flawed.
Better to have a clean `sorry` with correct documentation than unsound infrastructure.

### 2. Helper Axioms Are Dangerous

The two helper axioms seemed plausible:
- "Face in incident pair" - actually provable (~20 lines)
- "ReflTransGen absurdity" - **FALSE**, counter-examples exist

Lesson: Scrutinize axioms, especially "helper" ones that feel like they should be obvious.

### 3. Trust Expert Guidance

GPT-5 Pro identified the flaw immediately. The counter-example (faces sharing one edge
can still be path-connected avoiding that edge) is subtle but fatal.

---

## Next Steps

### Immediate (Completed)

- ✅ Remove adjExcept/compAfterDeleteSet infrastructure
- ✅ Remove false helper axioms
- ✅ Replace complex proof with clean sorry
- ✅ Verify build succeeds
- ✅ Document session

### Short Term (This Session)

- Update AXIOMS.md to reflect cleanup
- Update question document for GPT-5 Pro (remove H2 proof complexity question)
- Consider: Should we ask GPT-5 Pro about spanning forest approach?

### Medium Term (Future Work)

**Option A: Implement H2 via spanning forest**
- Build interior dual graph infrastructure
- Implement spanning forest algorithm
- Construct leaf-subtree
- Prove singleton cut property
- **Estimate**: ~100-150 lines, 2-3 sessions

**Option B: Leave H2 as sorry, focus on other tasks**
- Complete Tait equivalence path (~200 lines)
- Prove provable Disk axioms (~100-150 lines)
- Integration work

**Recommendation**: Consult with user / GPT-5 Pro on priorities.

---

## Files Modified

**Modified**:
1. `/home/zar/claude/lean-projects/fourcolor/FourColor/Geometry/Disk.lean`
   - Lines 638-692: Removed ~180 lines, added ~30 lines of documentation + clean sorry
   - Net change: -150 lines

**Created**:
1. `/home/zar/claude/lean-projects/fourcolor/docs/SESSION_2025-11-06_CLEANUP_INCORRECT_H2.md` - This document

**To be updated**:
1. `/home/zar/claude/lean-projects/fourcolor/AXIOMS.md` - Reflect axiom reduction
2. `/home/zar/claude/lean-projects/fourcolor/docs/QUESTION_FOR_GPT5_H2_PROOF_COMPLEXITY.md` - Update/deprecate

---

## Credit

**GPT-5 Pro (Oruži)**: Mathematical insight identifying the flaw in component-after-delete approach

**Claude Code (Robo Mario)**: Implementation of cleanup, documentation

**Philosophy**: "Measure twice, cut once" - Better to remove unsound infrastructure than
continue building on false foundations.

---

## Conclusion

Successfully cleaned up incorrect infrastructure based on GPT-5 Pro's guidance. The codebase
now has:

- ✅ Clean, documented sorry for H2 construction
- ✅ Working support-aware bridge lemma
- ✅ Working H3 descent lemma
- ✅ Build succeeds
- ✅ Reduced axiom count (11 → 9)
- ✅ Honest documentation of what works and what doesn't

**Status**: Ready for either H2 implementation (spanning forest) or continuation of other tasks.

**Build**: ✅ Succeeds with clean sorry

**Next**: User decision on priorities (implement H2 vs other tasks).
