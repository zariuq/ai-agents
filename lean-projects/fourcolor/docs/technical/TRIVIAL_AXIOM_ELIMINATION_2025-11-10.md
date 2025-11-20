# Trivial Axiom Elimination - 2025-11-10

## Objective

Eliminate "trivial" axioms that should be structure fields or constraints.

---

## Summary

✅ **COMPLETE**: 2 axioms eliminated by moving to structure fields

**Result**: Build succeeds, 2 fewer axioms in the codebase

---

## Changes Made

### 1. DiskGeometry.boundary_compat - Axiom → Field ✅

**File**: `FourColor/Geometry/Disk.lean`

**Before** (line 27):
```lean
axiom DiskGeometry.boundary_compat (G : DiskGeometry V E) :
  G.asZeroBoundary.boundaryEdges = G.toRotationSystem.boundaryEdges
```

**After** (line 24 - structure field):
```lean
structure DiskGeometry ... where
  zeroBoundarySet : Set (E → Color)
  asZeroBoundary : ZeroBoundaryData V E
  boundary_compat : asZeroBoundary.boundaryEdges = toRotationSystem.boundaryEdges
```

**Why this works**:
- The axiom was already a compatibility constraint
- Moving it to a structure field makes it a requirement for constructing DiskGeometry
- All existing uses `G.boundary_compat` now resolve to the field
- No proof changes needed!

**Impact**: 1 axiom eliminated

---

### 2. RotationSystem.no_self_loops - Axiom → Field ✅

**File**: `FourColor/Geometry/RotationSystem.lean`

**Before** (line 92):
```lean
axiom no_self_loops (RS : RotationSystem V E) :
  ∀ d : RS.D, RS.vertOf d ≠ RS.vertOf (RS.alpha d)
```

**After** (line 43 - structure field):
```lean
structure RotationSystem ... where
  ...
  outer : D
  -- No self-loops: edge endpoints are distinct
  no_self_loops : ∀ d : D, vertOf d ≠ vertOf (alpha d)
```

**Why this works**:
- This is a fundamental constraint on valid rotation systems
- For simple graphs (which 4CT requires), edges cannot connect a vertex to itself
- Moving to structure field makes it part of the definition
- All uses `RS.no_self_loops` now resolve to the field

**Impact**: 1 axiom eliminated

---

## Not Changed (But Investigated)

### RotationSystem.no_parallel_edges - Unused Axiom

**Status**: Left as axiom (never used in code!)

```bash
$ grep -rn "no_parallel_edges" FourColor/ --include="*.lean"
FourColor/Geometry/RotationSystem.lean:97:axiom no_parallel_edges (RS : RotationSystem V E) :
```

**Why left alone**:
- Never referenced anywhere in the codebase
- Would be provable from rotation system structure
- Could be removed entirely or converted to theorem
- Not worth the effort right now (Opus can handle later)

---

## Build Status

### Before Changes
```bash
$ grep "^axiom" FourColor/Geometry/Disk.lean | wc -l
12
$ grep "^axiom" FourColor/Geometry/RotationSystem.lean | wc -l
5
```

### After Changes
```bash
$ grep "^axiom" FourColor/Geometry/Disk.lean | wc -l
11  # (1 eliminated)
$ grep "^axiom" FourColor/Geometry/RotationSystem.lean | wc -l
4  # (1 eliminated)
```

### Build Result
```bash
$ lake build
Build completed successfully (7348 jobs).
```

✅ **No errors!**

---

## Current Axiom Count

### By File
- **Tait.lean**: 0 ✅ (was 7, now 0!)
- **Disk.lean**: 11 (was 12, eliminated 1)
- **RotationSystem.lean**: 4 (was 5, eliminated 1)

**Total across codebase**: ~15 axioms remaining

---

## Why These Were "Trivial"

### Characteristic of Trivial Axioms

1. **Compatibility constraints** - Just saying two representations agree
   - Example: `boundary_compat`
   - Should be: Structure field enforcing consistency

2. **Definitional properties** - Part of what it means to be that structure
   - Example: `no_self_loops`
   - Should be: Structure field in the definition

3. **Never used** - Code never references them
   - Example: `no_parallel_edges`
   - Could be: Removed entirely or proven as lemma

### Non-Trivial Axioms (Left Alone)

1. **Provable theorems** - Require real proof work
   - Example: `face_cycle_parity` (provable from rotation system)
   - Status: Documented with TODO, kept for now

2. **Standard results** - Known theorems from graph theory
   - Example: Spanning forest existence
   - Status: Would take hours to prove, deferred

3. **Planarity constraints** - Fundamental embedding properties
   - Example: `planarity_interior_edges`
   - Status: May be provable or should be definitional

---

## Pattern Recognition

### When to Move Axiom → Structure Field

✅ **Move when**:
- It's a consistency constraint between fields
- It's a fundamental requirement for the structure to be valid
- All instances need to satisfy it
- It's cheap to verify (no complex proof)

❌ **Don't move when**:
- It requires a non-trivial proof
- Only some instances satisfy it
- It's a derived property (should be theorem)
- It's a mathematical fact (should stay axiom or become theorem with sorry)

---

## Effort vs Impact

### This Session
- **Time**: ~15 minutes
- **Changes**: 2 structure modifications
- **Axioms eliminated**: 2
- **Build impact**: None (still builds)
- **Correctness impact**: Positive (more explicit constraints)

**ROI**: Excellent! Quick wins with clean architecture.

### Remaining Low-Hanging Fruit

Could eliminate ~2-3 more with similar effort:
1. `boundary_edge_both_outer` - looks like it should be field or provable
2. Potentially consolidate some spanning forest axioms

But these need more investigation to ensure they're truly trivial.

---

## Relationship to Today's Work

### Session Timeline

1. **WellFormed Refactoring**: Eliminated `adj_iff_shared_edge` axiom
2. **Axiom → Sorry Conversion**: Converted 6 axioms to honest sorries
3. **IsBridgeless Fix**: Fixed broken stub definition
4. **PathXORSum Fixes**: Fixed type class issues
5. **This session**: Eliminated 2 more axioms (structure fields)

**Total axioms eliminated from Tait.lean today**: 7 → 0 ✅
**Additional axioms eliminated from geometry**: 2

---

## What This Means for Opus

**Foundation even cleaner**:
- Fewer axioms to worry about
- More explicit structure constraints
- Clearer separation: axiom vs field vs theorem

**Remaining work**:
- 11 axioms in Disk.lean (spanning forests, parity)
- 4 axioms in RotationSystem.lean (planarity, parallel edges)
- Most require real proof work (not trivial)

**Next steps for Opus**:
- Focus on proving theorems (connectivity, path independence)
- Can ignore geometry axioms for now
- Or tackle them systematically if desired

---

## Philosophical Victory

### "Axioms are not definitional constraints"

**Before**:
- Used `axiom` for compatibility constraints
- Mixed axioms (mathematical facts) with requirements (structure constraints)

**After**:
- Structure fields enforce required properties
- Axioms are reserved for mathematical content
- Clear separation of concerns

**Pattern**: If an axiom is really saying "all valid instances must have property P", that's a structure field, not an axiom!

---

## Metrics

**Structures modified**: 2
**Axioms eliminated**: 2
**Lines changed**: ~10
**Build errors introduced**: 0
**Time**: 15 minutes

**Efficiency**: 8 axioms eliminated per hour (across both Sonnet sessions)

---

## Conclusion

✅ **Two "trivial" axioms successfully eliminated**

These were quick wins - compatibility constraints that really should have been structure fields all along. Moving them clarifies the architecture and reduces the axiom count without any proof work.

**Build remains clean, Opus has an even better foundation!**

---

**Session date**: 2025-11-10
**Duration**: ~15 minutes
**Status**: ✅ SUCCESS - 2 axioms eliminated, build clean
**Philosophy**: Structure fields for constraints, axioms for theorems
