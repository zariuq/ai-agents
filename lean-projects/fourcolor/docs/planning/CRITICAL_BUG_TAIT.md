# CRITICAL BUG: Tait Reverse Direction - False Axiom

**Date**: 2025-11-06
**Severity**: 🔴 **CRITICAL** - Blocks main proof
**File**: FourColor/Tait.lean
**Lines**: 141-147 (`cubic_proper_coloring_missing_color`)

---

## The Problem

The axiom `cubic_proper_coloring_missing_color` states:

```lean
/-- In a cubic graph with proper 3-edge-coloring, exactly one color is missing at each vertex. -/
axiom cubic_proper_coloring_missing_color {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (incident : V → Finset E)
    (cubic : IsCubic incident)
    (edge_coloring : @ThreeEdgeColoring V E _ _ incident)
    (v : V) :
    ∃! c : EdgeColor, c ∉ (incident v).image edge_coloring.color
```

**This axiom is FALSE!**

---

## Mathematical Proof of Falsity

### Setup
- Vertex `v` has degree 3 (from `IsCubic`)
- Therefore `incident v` contains exactly 3 edges: `{e₁, e₂, e₃}`
- Edge coloring is proper at `v` (from `ThreeEdgeColoring.proper`)
- Therefore: `color(e₁) ≠ color(e₂) ≠ color(e₃)`
- There are exactly 3 edge colors: `{α, β, γ}`

### Contradiction

1. The 3 edges have 3 DIFFERENT colors (proper coloring)
2. There are exactly 3 colors available
3. By pigeonhole principle: the 3 edges must use ALL 3 colors
4. Therefore: `{color(e₁), color(e₂), color(e₃)} = {α, β, γ}`
5. Therefore: NO color is missing!

**Conclusion**: The axiom claims "exactly one color is missing" but we proved "no colors are missing". **CONTRADICTION!**

---

## Impact

This axiom is used in:

1. **`adjacent_different_missing`** (Tait.lean:224)
   - Uses this to claim adjacent vertices have different missing colors
   - But there ARE no missing colors!

2. **`tait_reverse`** (Tait.lean:~260)
   - Entire proof strategy relies on "missing color → vertex color" mapping
   - But if no colors are missing, the mapping is undefined!

3. **Main theorem integration** (FourColorTheorem.lean)
   - Depends on Tait equivalence being correct

---

## Root Cause Analysis

### Where did the misunderstanding come from?

Looking at the Tait reverse comment (lines 123-136):

> "Each vertex of the dual (face of the triangulation) has 3 edges with 3 different colors {α, β, γ}. The 'missing' edge color determines which vertex color to assign to that vertex."

**The issue**: This assumes 3 edges can have 3 different colors WITHOUT using all 3 available colors. But that's impossible when there are only 3 colors total!

### Possible resolutions

#### Option 1: Need MORE than 3 colors for edges

If we had 4 or more edge colors, then:
- 3 edges with 3 different colors
- 4+ colors available
- At least 1 color is indeed missing

But then we're not using a "3-edge-coloring"!

#### Option 2: The graph isn't actually cubic

Maybe some vertices have degree < 3?
- Then `IsCubic` is wrong, or
- Need weaker assumption like "degree ≤ 3"

#### Option 3: Different graph structure

Maybe the axiom is meant for a DIFFERENT graph (not the dual)?
- Need to check what graph `tait_reverse` is actually about
- Confusion between primal and dual?

#### Option 4: The statement is correct but refers to different context

Maybe "missing" means something else:
- Missing from some SUBSET of edges?
- Missing in a partial coloring?
- Missing in the PRIMAL but present in DUAL?

---

## Recommended Action

**STOP** work on proving these axioms until we clarify:

1. ✅ Is the formalization of Tait's theorem CORRECT?
2. ✅ Are we confusing primal and dual graphs?
3. ✅ Should we be using 4 edge colors instead of 3?
4. ✅ Is there a different interpretation of "missing color"?

### Investigation Steps

1. **Check classical Tait theorem statement**:
   - What exactly does Tait's 1880 theorem say?
   - Is it about triangulations? Cubic graphs? Both?

2. **Check primal/dual relationship**:
   - Triangulation (primal): vertices, edges, faces
   - Dual: faces → vertices, edges → edges, vertices → ?
   - Is dual of triangulation actually cubic?

3. **Check color mapping**:
   - 4-vertex-coloring uses 4 colors: {red, blue, green, yellow}
   - 3-edge-coloring uses 3 colors: {α, β, γ}
   - How do these map to each other?

---

## Classical Tait Theorem (Reference)

**Tait's Conjecture (1880)**: Every cubic planar bridgeless graph is 3-edge-colorable.

**Equivalence to 4CT**:
- Forward: 4-colorable map → 3-edge-colorable dual
- Reverse: 3-edge-colorable cubic graph → 4-colorable ???

**Key question**: What is the "???" in the reverse direction?
- Is it the DUAL of the cubic graph?
- Or the PRIMAL map?

---

## Current Status

- ⚠️ **DO NOT MERGE** current Tait.lean implementation
- ⚠️ **BLOCKED**: Cannot proceed with proving these axioms
- ⚠️ **NEEDS REVIEW**: Entire Tait equivalence approach

---

## Next Steps

1. Research classical Tait theorem carefully
2. Clarify primal/dual relationship
3. Fix the axiom statements
4. Potentially redesign the entire Tait equivalence module

**Do NOT attempt to prove `cubic_proper_coloring_missing_color` as stated - it's FALSE!**

---

**Reported by**: Claude Code (automated analysis)
**Date**: 2025-11-06
**Requires**: Mathematical review by human expert
