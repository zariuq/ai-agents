# H3 Strict Descent - Mario Carneiro Analysis

**Date**: 2025-11-04
**Context**: Working on `aggregated_toggle_strict_descent_at_prescribed_cut₁` (Disk.lean:579)

---

## The Remaining Sorry (Line 646)

### Situation

We have:
- `S₀ ⊆ facesTouching₁ G x` (faces that touch `support₁ x`)
- `cutEdges₁ G x S₀ = {e0}` (unique cut edge in support)
- `e ≠ e0` and `e ∉ support₁ x` and `e` is internal

Need to show: `(toggleSum G (1,0) S₀ e).fst = 0`

### What We Know

1. `(toggleSum e).fst ≠ 0` iff `e ∈ cutEdges G S₀` (by `toggleSum_supported_on_cuts_10`)
2. `cutEdges G S₀` = edges in exactly one face of `S₀`
3. `cutEdges₁ G x S₀` = `cutEdges G S₀` filtered to `support₁ x ∩ internal edges`

### The Question

**Can there exist an edge `e` such that**:
- `e ∈ cutEdges G S₀` (appears in exactly one face of `S₀`)
- `e ∉ support₁ x` (not in the first-coordinate support)
- `e ∉ boundaryEdges` (internal edge)
- `e ≠ e0`

### Analysis

If such an `e` exists, it would be in `cutEdges G S₀ \ cutEdges₁ G x S₀`. This is **logically possible** given just the hypotheses we have!

Consider:
- Face `f ∈ S₀` touches `support₁ x` at edge `e'`
- Same face `f` contains edge `e` on its "outer boundary"
- Edge `e` might not be in `support₁ x`
- If `e` appears in no other face of `S₀`, then `e ∈ cutEdges G S₀`

### The Missing Property

We need one of:

**Option A**: Prove directly from graph topology
```lean
lemma cutEdges_of_facesTouching₁_in_support
    {S₀ : Finset (Finset E)} (hS₀ : S₀ ⊆ facesTouching₁ G x) :
    e ∈ cutEdges G S₀ → e ∉ boundaryEdges → e ∈ support₁ x
```

**Proof idea**: If face `f` contains both an edge in `support₁ x` and an edge `e ∉ support₁ x`, and `e` is a cut edge... (needs planarity/face cycle properties)

**Option B**: Strengthen H2 to provide more structure
```lean
-- H2 should guarantee that S₀ is a "proper leaf-subtree" where:
-- All cut edges of S₀ are actually in support₁ x (except possibly boundary)
```

**Option C**: Use that `cutEdges₁ = {e0}` is a UNIQUE cut in support
```lean
-- If cutEdges₁ = {e0}, maybe this already implies
-- that cutEdges G S₀ \ {e0} consists only of boundary edges?
-- This would need the structure from H2's construction
```

### Recommendation

This is a **graph theory fact** that requires either:
1. Properties of planar dual graphs and face cycles
2. The specific leaf-subtree construction from H2
3. A topological/connectivity argument

**Best approach**: When implementing H2, ensure the constructed `S₀` satisfies:
```lean
∀ e ∈ cutEdges G S₀, e ∉ boundaryEdges → e ∈ support₁ x
```

This should follow from H2's "leaf-subtree" construction via graph connectivity.

---

## Conclusion

The H3 proof is **structurally complete** modulo this one graph theory fact. The proof architecture using `support₁_add_toggles_singleton` and `toggleSum_supported_on_cuts₁_10` is sound.

The remaining sorry is a well-isolated graph theory lemma (~15-20 lines) that connects:
- Geometric properties of `facesTouching₁`
- Topological properties of cut edges
- Structure guaranteed by H2's construction

This is exactly the kind of fact that should be proven as a helper lemma for the H2/H3 integration.
