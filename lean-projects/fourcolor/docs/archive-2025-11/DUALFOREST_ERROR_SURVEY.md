# DualForest.lean Pre-Existing Error Survey

**Date**: 2025-11-17
**Context**: Post circular-import architecture fix
**Total Errors**: 35 compilation errors (excluding warnings)
**File Size**: 3978 lines

---

## Executive Summary

DualForest.lean contains **35 pre-existing errors** that fall into 4 major categories:

1. **Missing Mathlib API** (12 errors) - References to SimpleGraph functions that don't exist or have moved
2. **Incomplete Proofs** (8 errors) - Proof structure issues, missing tactics, unterminated blocks
3. **Type Mismatches** (7 errors) - Application errors, notation issues, unification failures
4. **Compilability Issues** (5 errors) - Noncomputable definitions, missing fields

**RECOMMENDATION**: **DROP** this file and start fresh with a minimal spanning forest proof. The file appears to be an abandoned experimental approach with too many mathlib version mismatches.

---

## Category 1: Missing Mathlib SimpleGraph API (12 errors)

### Critical Missing Imports/Definitions

**Line 19**: `unknown namespace Mathlib.SimpleGraph`
- **Cause**: Trying to open `Mathlib.SimpleGraph` namespace that doesn't exist
- **Impact**: Cascades to all SimpleGraph usage
- **Fix**: Remove this open statement, use fully qualified names

**Line 108**: `Invalid field IsForest: The environment does not contain SimpleGraph.IsForest`
- **Cause**: Mathlib's SimpleGraph API may not have `IsForest` in this version
- **Impact**: Cannot use forest structure from Mathlib
- **Fix**: Use `IsTree` or define custom `IsForest`

**Line 277**: `Invalid field exists_isTree_le: The environment does not contain Function.exists_isTree_le`
- **Cause**: Connected graph theorem missing or renamed in Mathlib
- **Impact**: Core proof strategy fails
- **Fix**: Find equivalent `Connected.exists_maximal_acyclic` or similar

**Line 321**: `Unknown constant SimpleGraph.induce_Adj`
- **Cause**: Induction lemma missing or renamed
- **Impact**: Cannot reason about induced subgraphs
- **Fix**: Search for `Subgraph.induce_adj` or `induced_adj`

**Line 331**: `Invalid field connected: The environment does not contain SimpleGraph.IsTree.connected`
- **Cause**: Tree connectivity property missing
- **Impact**: Cannot use tree connectedness
- **Fix**: Use `IsTree.connected` from different namespace or prove manually

**Line 339**: `Invalid field isAcyclic: The environment does not contain SimpleGraph.IsTree.isAcyclic`
- **Cause**: Acyclicity property missing from IsTree
- **Impact**: Cannot extract acyclicity from tree
- **Fix**: `IsTree` might be defined as `IsAcyclic ∧ IsConnected` - destruct directly

**Line 344**: `Invalid field support: The environment does not contain Subtype.support`
- **Cause**: Walk support undefined for subtypes
- **Impact**: Cannot extract cycle vertices
- **Fix**: Define custom `support` or use Walk API differently

### Missing Helper Functions

**Line 196**: `Unknown identifier interior_edge_has_two_faces`
- **Cause**: This should be in PlanarityHelpers or RotationSystem
- **Impact**: Cannot construct dual adjacency
- **Fix**: This is E2 axiom - already exists as `two_internal_faces_of_interior_edge`

**Line 276**: `Unknown identifier comp_verts`
- **Cause**: Undefined local helper
- **Impact**: Cannot extract component vertices
- **Fix**: Define this helper or inline the logic

---

## Category 2: Incomplete Proofs (8 errors)

### Structural Issues

**Line 40**: `No goals to be solved`
**Line 50**: `No goals to be solved`
**Line 258:16**: `No goals to be solved`
- **Cause**: Proof tactics applied when goal already closed
- **Impact**: Proof structure broken
- **Fix**: Remove extraneous tactics or check proof flow

**Line 3980**: `unterminated comment`
- **Cause**: File ends mid-comment or has unmatched `/-`
- **Impact**: Parsing failure
- **Fix**: File ends at line 3978, so this is a spurious error from prior failures

**Line 461**: `unknown tactic`
- **Cause**: Custom tactic or typo
- **Impact**: Proof stuck
- **Fix**: Check what tactic was intended (likely typo)

**Line 456**: `Fields missing: dichotomy`
- **Cause**: `SpanningForest` structure construction incomplete
- **Impact**: Core theorem `exists_spanning_forest` fails
- **Fix**: Prove the dichotomy property (either edge in tree or creates cycle)

**Line 458**: `unsolved goals`
- **Cause**: Proof of `exists_spanning_forest` incomplete
- **Impact**: Main theorem unproven
- **Fix**: Complete the proof or stub with sorry

**Line 90**: `declaration uses 'sorry'` (warning, not error)
- **Note**: At least one proof already stubbed

---

## Category 3: Type Mismatches (7 errors)

### Application Errors

**Line 248**: `Application type mismatch: The argument rfl has type ?m.55 = ?m.55 but is expected to have type (dualGraph G).connectedComponentMk f = comp`
- **Cause**: Type inference failure with connected components
- **Impact**: Cannot construct component membership proof
- **Fix**: Provide explicit type annotations

**Line 303-304**: `Type mismatch` (id has wrong type)
- **Cause**: Using `id` where coercion/witness needed
- **Impact**: Cannot construct subtype elements
- **Fix**: Use `⟨v, hv⟩` instead of `id`

**Line 372**: `Application type mismatch: h_adj has type (dualGraph G).Adj f g but is expected to have type ∃ x, ?m.47 x`
- **Cause**: Using `Classical.choose` on non-existential
- **Impact**: Cannot extract edge from adjacency
- **Fix**: Unfold `dualAdjacent` to get existential, then choose

**Line 380**: `Application type mismatch: h_adj has type (dualGraph G).Adj f g but is expected to have type ∃ x, ?m.81 x`
- **Cause**: Same as above (likely `Classical.choose_spec`)
- **Impact**: Cannot use chosen edge
- **Fix**: Same - unfold first

### Notation/Structure Issues

**Line 258**: `Invalid ⟨...⟩ notation: The expected type { f // f ∈ G.internalFaces } → Prop is not an inductive type`
- **Cause**: Trying to use constructor notation for function type
- **Impact**: Cannot define predicate
- **Fix**: Use `fun f => ...` or explicit lambda

**Line 319**: `Invalid ⟨...⟩ notation: The expected type T_induced.1 ?m.315 ?m.316 is not an inductive type`
- **Cause**: Same issue with anonymous constructor
- **Impact**: Cannot construct graph adjacency
- **Fix**: Use explicit constructor

### Unification Failures

**Line 333**: `Tactic apply failed: could not unify SimpleGraph.Reachable ?m.362 ⟨v, hv_in⟩ ⟨w, hw_in⟩ with T.Reachable v w`
- **Cause**: Subtype coercion mismatch
- **Impact**: Cannot apply reachability lemma
- **Fix**: Use `Subtype.coe_injective` or explicit coercion

**Line 327-328**: `simp made no progress` (2 occurrences)
- **Cause**: Simp set incomplete or goal not simplifiable
- **Impact**: Proof stuck
- **Fix**: Replace with manual rewrites or different tactic

---

## Category 4: Compilability Issues (5 errors)

### Noncomputable Definitions

**Line 140**: `failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Classical.propDecidable'`
- **Cause**: Using classical logic without noncomputable marker
- **Impact**: Cannot compile for execution
- **Fix**: Add `noncomputable` keyword

**Line 177**: `failed to compile definition, compiler IR check failed at spanningTreeToForest._redArg. Error: depends on 'treeEdgesOfDualTree', which has no executable code`
- **Cause**: Dependency on noncomputable function
- **Impact**: Cascading compilation failure
- **Fix**: Mark entire chain as noncomputable

**Line 386**: `failed to compile definition, compiler IR check failed at treeEdgesOfComponent._redArg. Error: depends on 'treeEdgesOfDualTree', which has no executable code`
- **Cause**: Same - treeEdgesOfDualTree needs noncomputable
- **Impact**: Multiple functions broken
- **Fix**: Root cause is treeEdgesOfDualTree

### Missing Constants

**Line 37**: `Unknown constant FourColor.DiskGeometry.adj`
- **Cause**: This was likely meant to be `dualAdjacent` from DiskTypes
- **Impact**: Cannot use adjacency predicate
- **Fix**: Replace with `dualAdjacent` (now in DiskTypes.lean)

**Line 581**: `Identifier <missing> not found`
- **Cause**: Parse error from earlier failures
- **Impact**: Spurious error
- **Fix**: Resolve prior errors first

### Proof Obligation

**Line 110**: `Tactic constructor failed: target is not an inductive datatype`
- **Cause**: Trying to use `constructor` on non-inductive goal
- **Impact**: Proof structure broken
- **Fix**: Check what the actual goal is and use appropriate tactic

**Line 195**: `Tactic rcases failed: x✝ : ?m.86 is not an inductive datatype`
- **Cause**: Trying to destruct non-inductive type
- **Impact**: Cannot extract existential witness
- **Impact**: Check the actual type and use obtain/choose instead

---

## Error Dependency Graph

```
SimpleGraph API Missing (Line 19)
  ├─→ IsForest missing (108)
  ├─→ exists_isTree_le missing (277)
  ├─→ induce_Adj missing (321)
  ├─→ IsTree.connected missing (331)
  ├─→ IsTree.isAcyclic missing (339)
  └─→ Subtype.support missing (344)

treeEdgesOfDualTree not computable
  ├─→ spanningTreeToForest fails (177)
  └─→ treeEdgesOfComponent fails (386)

Proof Structure Incomplete
  ├─→ dichotomy field missing (456)
  └─→ exists_spanning_forest unsolved (458)
```

---

## Files Actually Referenced

Looking at the import structure:
```lean
import FourColor.Geometry.DiskTypes     ✅ EXISTS (we created it)
import FourColor.Geometry.NoDigons      ✅ EXISTS (we created it)
import Mathlib.Combinatorics.SimpleGraph.Acyclic  ❓ UNKNOWN
```

The file attempts to open `Mathlib.SimpleGraph` which doesn't exist as a namespace in the current mathlib version.

---

## Severity Assessment

### Blocker Errors (Must Fix to Build)
1. **Line 19**: Mathlib.SimpleGraph namespace - CRITICAL
2. **Line 456**: Missing dichotomy field - BLOCKS MAIN THEOREM
3. **Line 108**: IsForest missing - CORE CONCEPT UNDEFINED
4. **Line 277**: exists_isTree_le missing - CORE PROOF STRATEGY FAILS

### High-Priority Errors (Proof-Breaking)
5. Lines 331, 339: Tree properties missing - Need alternative API
6. Line 196: interior_edge_has_two_faces - Easy fix (rename)
7. Lines 372, 380: Classical.choose type errors - Need refactoring

### Medium-Priority Errors (Fixable with Refactoring)
8. Lines 303-304, 248: Type mismatches - Need explicit coercions
9. Lines 140, 177, 386: Noncomputable - Add keywords
10. Line 37: DiskGeometry.adj - Rename to dualAdjacent

### Low-Priority Errors (Cosmetic/Cascading)
11. Lines 40, 50, 258:16: No goals - Clean up proof structure
12. Lines 327-328: simp failures - Replace with manual proofs
13. Line 3980: Unterminated comment - Spurious from other errors

---

## Recommendation: DROP vs FIX

### Arguments for DROPPING

1. **Mathlib API Mismatch**: The file appears to be written for a different version of mathlib. The SimpleGraph API it expects doesn't match our current mathlib pin.

2. **Abandoned Experimental Code**: File has 35 errors and 1+ sorry. This suggests it was an experimental approach that was never completed.

3. **Core Strategy Broken**: The fundamental proof strategy (`Connected.exists_isTree_le`) is unavailable. This requires a complete rewrite anyway.

4. **Size vs Value**: 3978 lines with 35 errors = ~1% error rate. The signal-to-noise ratio is poor.

5. **No Current Usage**: The spanning forest theorem is currently sorry'd in Disk.lean anyway. No downstream code depends on this file working.

### Arguments for FIXING

1. **Structural Insight**: The file contains valuable proof sketches and strategy comments that could guide a rewrite.

2. **Some Working Code**: Not all 3978 lines are broken. Some helper lemmas may be salvageable.

3. **Investment Already Made**: Someone spent significant time on this approach.

### FINAL RECOMMENDATION: **DROP AND REWRITE**

**Reason**: The core SimpleGraph API mismatch means we'd need to rewrite the proof strategy anyway. It's more efficient to:

1. **Extract the proof sketch** (comments and structure)
2. **Archive DualForest.lean** to `archive/DualForest_old.lean`
3. **Create minimal new proof** using:
   - Our working `DiskTypes.lean` (✅ builds)
   - Our working `NoDigons.lean` (✅ builds)
   - Correct mathlib SimpleGraph API for our version
   - ~200-300 lines instead of 3978

**Specific New Approach**:
```lean
-- FourColor/Geometry/SpanningForest.lean (NEW FILE)
import FourColor.Geometry.DiskTypes
import FourColor.Geometry.NoDigons
import Mathlib.Combinatorics.SimpleGraph.Connectivity  -- Correct import

-- Minimal proof:
-- 1. Define dual graph using dualAdjacent from DiskTypes
-- 2. Use simpler forest construction (greedy algorithm)
-- 3. Prove dichotomy property using NoDigons
-- Target: ~200 lines, 0 sorries
```

---

## Action Plan if User Chooses to FIX

If the user insists on fixing rather than dropping:

### Phase 1: API Repair (Estimated 2-3 hours)
1. Find correct SimpleGraph imports for our mathlib version
2. Replace all missing API calls with available equivalents
3. Fix namespace issues (line 19)

### Phase 2: Type Cleanup (Estimated 1-2 hours)
4. Fix all type mismatches (lines 248, 303-304, 372, 380)
5. Add noncomputable keywords (lines 140, 177, 386)
6. Fix constructor/notation issues (lines 258, 319)

### Phase 3: Proof Completion (Estimated 4-6 hours)
7. Complete dichotomy field proof (line 456)
8. Complete exists_spanning_forest proof (line 458)
9. Fix all helper lemma gaps
10. Replace interior_edge_has_two_faces reference (line 196)

### Phase 4: Testing (Estimated 1 hour)
11. Build and verify no errors
12. Check theorem actually proves what's needed

**Total Estimated Time to Fix**: 8-12 hours of focused work

**Total Estimated Time to Rewrite Minimal**: 3-4 hours

**RECOMMENDATION**: Rewrite is 2-3x more efficient and produces cleaner code.

---

## Questions for GPT-5 Pro / Grok 4

1. **Mathlib Version**: What SimpleGraph API is available in mathlib commit `06d95e5f5311594940c0c3dff5381fabe4fcabe7`? Specifically:
   - Does `SimpleGraph.IsForest` exist?
   - What's the correct way to get a spanning tree from `Connected`?
   - Where is `induce_Adj` located?

2. **Proof Strategy**: Is there a simpler spanning forest construction that doesn't rely on mathlib's tree theorems? Options:
   - Greedy algorithm (add edges until acyclic+spanning)
   - DFS-based construction
   - Component-by-component construction (current approach)

3. **Salvageability**: Are any of these helper lemmas worth extracting:
   - `dualGraph` definition (lines 29-42)
   - `faces_share_unique_interior_edge` (lines 565-580) - already fixed!
   - Component membership proofs (lines 240-260)

4. **Time Investment**: Given we have working DiskTypes + NoDigons, what's the fastest path to a provably correct spanning forest theorem?

---

## Summary Statistics

| Metric | Value |
|--------|-------|
| Total Lines | 3978 |
| Total Errors | 35 |
| Error Rate | 0.88% |
| Sorries | 1+ |
| Build Time | N/A (doesn't build) |
| Estimated Fix Time | 8-12 hours |
| Estimated Rewrite Time | 3-4 hours |
| **Recommendation** | **DROP & REWRITE** |

---

**Generated**: 2025-11-17 by Claude Code
**Context**: Post circular-import architecture fix
**Status**: DiskTypes.lean ✅ | NoDigons.lean ✅ | DualForest.lean ❌
