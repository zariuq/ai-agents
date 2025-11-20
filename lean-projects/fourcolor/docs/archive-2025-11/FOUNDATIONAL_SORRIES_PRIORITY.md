# Foundational Sorries - Priority Order for Four Color Theorem

**Date**: 2025-11-17
**Principle**: Fill sorries from the ground up to avoid building on false foundations
**Current State**: 0 axioms (fixed!), 78 sorries

---

## Most Foundational Sorries (Fill These FIRST!)

These are in **RotationSystem.lean** - the very foundation of our planar graph representation:

### Priority 1: Core RotationSystem Properties (lines 88-111)

1. **`interior_edge_distinct_faces`** (line 93)
   - What: Interior edges separate distinct faces
   - Why foundational: Core property of planar embeddings
   - Difficulty: Medium - needs face definition understanding
   - Dependencies: NONE - this is bedrock

2. **`no_parallel_edges`** (line 102)
   - What: At most one edge between any vertex pair
   - Why foundational: Required for simple graph properties
   - Difficulty: Easy-Medium - follows from rotation system axioms
   - Dependencies: NONE - this is bedrock

3. **`boundary_edge_both_outer`** (line 111)
   - What: Boundary edges belong to outer face
   - Why foundational: Defines what boundary means
   - Difficulty: Easy - definitional
   - Dependencies: NONE - this is bedrock

### Priority 2: More RotationSystem Properties (lines 169, 907)

4. **`darts_of_edge`** (line 169)
   - What: Extract the two darts of an edge
   - Difficulty: Easy - use edge_fiber_two axiom

5. **`edge_not_in_boundary`** (line 907)
   - What: Some complex boundary property
   - Difficulty: Unknown - needs investigation

---

## Why These Matter

**Everything depends on RotationSystem!**

```
RotationSystem.lean (5 foundational sorries)
    ↓
DiskGeometry (uses RotationSystem)
    ↓
Disk.lean (31 sorries - but depend on RotationSystem)
    ↓
SpanningForest.lean (1 sorry - depends on everything)
    ↓
Four Color Theorem
```

If RotationSystem has false properties, EVERYTHING built on it is potentially wrong!

---

## Next Layer: Disk.lean Sorries

After filling RotationSystem sorries, these are next:

### Priority 3: Basic Disk Properties (Disk.lean)

- Line 31: `edgesCutBy_subset`
- Line 823: H2 property about prescribed cuts
- Line 842: `filter_set_partition`
- Line 849: Property about face touching
- Line 862: `exists_bridge_dart`

---

## Current Progress

### What We Fixed Today:
- ❌ Removed axiom for fundamental_cycle_property (was line 99)
- ✅ Replaced with lemma + sorry (correct approach)
- ✅ Build still succeeds

### Foundation Status:
```
Layer 0 (RotationSystem): 5 sorries - CRITICAL TO FIX
Layer 1 (Disk): 31 sorries - Fix after Layer 0
Layer 2 (SpanningForest): 1 sorry - Fix after Layer 1
Layer 3+ (Higher theorems): ~40 sorries - Fix last
```

---

## The Right Order

**Mario Carneiro would say**: "Start at the bottom. A theorem is only as strong as its weakest foundation."

1. First prove **ALL** RotationSystem sorries
2. Then prove basic Disk properties
3. Then prove SpanningForest (including fundamental_cycle_property)
4. Finally tackle higher-level theorems

This ensures we never build false theorems on unproven foundations.

---

## Estimated Time

### RotationSystem (5 sorries): 2-4 hours total
- `interior_edge_distinct_faces`: 30-60 min
- `no_parallel_edges`: 20-30 min
- `boundary_edge_both_outer`: 10-20 min
- `darts_of_edge`: 10-15 min
- `edge_not_in_boundary`: 30-60 min

### Why Worth It:
Once these are proven, we have a **verified foundation** for planar graph theory in Lean!

---

## Next Action

Start with `interior_edge_distinct_faces` at line 88-93 of RotationSystem.lean.
This is THE most foundational property - everything else builds on it.