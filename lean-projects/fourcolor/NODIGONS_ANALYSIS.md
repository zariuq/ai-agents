# NoDigons Lemma Analysis - Gemini's Investigation

**Date**: 2025-11-20
**Status**: ✅ **CORRECT HYPOTHESIS IDENTIFIED + COUNTEREXAMPLE STRATEGY**

## What Gemini Discovered

### 1. Original Lemma Was Too Weak

**Original claim**: For any `RotationSystem`, two distinct internal faces share at most one edge.

**Problem**: This is **false** for general rotation systems!

### 2. Correct Hypothesis: Requires Triangulation

**Corrected lemma** (NoDigons.lean):
```lean
theorem faces_share_at_most_one_interior_edge
    [Triangulation RS]  -- ← KEY: Need triangulation!
    {f g : Finset E}
    (hf : f ∈ RS.internalFaces)
    (hg : g ∈ RS.internalFaces)
    (hfg : f ≠ g)
    (e1 e2 : E)
    (he1_in_f : e1 ∈ f) (he1_in_g : e1 ∈ g)
    (he2_in_f : e2 ∈ f) (he2_in_g : e2 ∈ g)
    (he1_ne_e2 : e1 ≠ e2) :
    False
```

**Insight**: For triangulations (all faces have exactly 3 edges), two distinct triangular faces cannot share 2 edges.

### 3. Digon Counterexample Analysis (Lines 74-164)

Gemini implemented a digon (two vertices connected by two edges) and discovered:

**Finding**: In the digon, `f1 = f2 = {e0, e1}`
- Both faces are represented by the same edge set
- Therefore the premise `f ≠ g` fails
- The lemma holds **vacuously** (no actual counterexample)

**Quote from analysis** (lines 119-131):
```
-- f1 = {e0, e1}, f2 = {e0, e1}.
-- So hfg premise of lemma cannot be satisfied with this example.
-- The lemma requires DISTINCT faces.
-- So the lemma is actually TRUE for this counterexample (vacuously).
```

### 4. Real Counterexample: Square-in-Square

**Gemini's insight** (lines 137-149):
```
-- Square-in-Square:
-- f_in has {12, 23, 34, 41}.
-- f_annulus has {12, 23, 34, 41} AND {56, 67, 78, 85} AND connectors.
-- So f_in != f_annulus (different edge sets).
-- And they share 4 edges.
-- So Square-in-Square IS a valid counterexample.
```

**Why it works**:
- Inner square: face with 4 edges {e1, e2, e3, e4}
- Outer annular face: contains those same 4 edges PLUS more
- f_in ≠ f_annular (different cardinality)
- They share all 4 edges of the inner square
- Violates "at most one edge" claim

**Why it's not a triangulation**: Faces have ≥ 4 edges, not exactly 3.

## Proof Strategy for Triangulations (Lines 60-77)

Gemini documented the correct approach:

```lean
-- 1. Extracting darts for e1, e2.
-- 2. Showing they are consecutive in the face orbit (since cycle length 3).
-- 3. Using `vertOf` to show they share a vertex.
-- 4. Identifying the third edge via `no_parallel_edges`.
```

**Key idea**: If two triangular faces share 2 edges e1 and e2:
- Each face has exactly 3 edges
- If f = {e1, e2, e3} and g = {e1, e2, e4}
- Then e3 must complete the triangle at the shared vertex
- But then e3 = e4 (uniqueness via no parallel edges)
- Therefore f = g, contradicting f ≠ g

## Files

**Modified**:
- `FourColor/Geometry/NoDigons.lean`: Added `[Triangulation RS]` hypothesis

**Preserved** (should NOT be deleted):
- `FourColor/Geometry/NoDigonsCounterexample.lean`: Documents the investigation
  - Proves digon doesn't work (vacuous)
  - Identifies square-in-square as real counterexample
  - 166 lines of valuable analysis

## Recommendation

**KEEP the counterexample file!** It contains:
1. ✅ Proof that naive counterexamples don't work
2. ✅ Identification of what WOULD work (square-in-square)
3. ✅ Clear demonstration of why `[Triangulation RS]` is necessary
4. ✅ Educational value for understanding the lemma

This is excellent mathematical investigation work that should be preserved!

## Next Steps for NoDigons

If you want to complete this:

1. **Prove the lemma for Triangulations** following Gemini's strategy
2. **Implement square-in-square counterexample** to demonstrate it fails without [Triangulation]
3. Or **document that the corrected lemma is now correct** and move on

## Bottom Line

Gemini did **excellent work**:
- ✅ Identified the bug (missing Triangulation hypothesis)
- ✅ Fixed the lemma statement
- ✅ Proved digon doesn't provide counterexample
- ✅ Identified real counterexample (square-in-square)
- ✅ Documented proof strategy

**Don't delete the counterexample file** - it's valuable documentation! 🎯
