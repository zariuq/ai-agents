# CRITICAL FINDING: Lemma is False - Formal Counterexample

**Date**: 2025-11-10
**Status**: 🔴 **FALSE LEMMA IDENTIFIED**

---

## The False Claim

**Lemma statement** (in `Tait.lean`):
```lean
lemma cycle_color_alternates :
  In any cycle of a 3-edge-colored cubic graph,
  each color appears an EVEN number of times
```

**Reality**: This is **mathematically FALSE**.

---

## Explicit Counterexample

### The Graph: K₄ (Complete Graph on 4 Vertices)

- **Structure**: 4 vertices, each with degree 3 (cubic ✓)
- **Edge count**: 6 edges
- **Coloring**: A proper 3-edge-coloring exists (K₄ is Class 1)
  - Color α: 2 edges
  - Color β: 2 edges
  - Color γ: 2 edges
  - Each vertex is incident to one edge of each color ✓

### The Counterexample Cycle: Any 3-Cycle (Triangle)

**Example**: Take vertices {v₀, v₁, v₂} with edges:
- (v₀, v₁): color α
- (v₁, v₂): color β
- (v₂, v₀): color γ

**Color counts on this cycle**:
- count(α) = 1 (ODD ✗)
- count(β) = 1 (ODD ✗)
- count(γ) = 1 (ODD ✗)

**Conclusion**: Each color appears an ODD number of times, contradicting the lemma.

---

## Why the 2-Regularity Argument Fails

### What IS True
- Removing color c from a cubic graph gives degree 2 at each vertex ✓
- The remaining subgraph is 2-regular ✓

### What Is FALSE
- The claim that gaps between 2-regular segments "pair up evenly" in an arbitrary cycle ✗

### The Specific Failure in the Triangle

**Removing color α from the triangle**:
- Remaining edges: (v₁, v₂) in color β, (v₂, v₀) in color γ
- This forms **two disjoint paths**, not a single cycle
- The "gaps" (where we removed α edges) don't form a pairing
- We get exactly **1 gap** between the two paths, which is odd

**The error in the proof strategy**: The proof assumes that the intersection of an arbitrary cycle with the 2-regular non-c-subgraph creates a structure where gaps pair up. This is **false** for triangles and other short cycles.

---

## Why This Breaks the Entire Proof

The lemma `cycle_color_alternates` is used by:
```
color_parity_in_cycle
  └─ uses cycle_color_alternates
```

And `color_parity_in_cycle` is the foundation for:
```
parity_sum_cycle_zero (main F₂² theorem)
  └─ depends on color_parity_in_cycle
```

**Impact**: If `cycle_color_alternates` is false, then `parity_sum_cycle_zero` cannot be proven using this approach.

---

## What Should Replace This?

The lemma needs **major revision**. Options:

### Option 1: Restrict to Even-Length Cycles
```
lemma cycle_color_alternates_even_length :
  In any EVEN-LENGTH cycle of a 3-edge-colored cubic graph,
  each color appears an even number of times
```
**Issue**: K₄ triangles are odd-length, so this might help, but need to verify.

### Option 2: Add Structural Constraint
```
lemma cycle_color_alternates_via_decomposition :
  If the cycle is a fundamental cycle in some standard decomposition,
  then colors appear evenly
```

### Option 3: Reformulate Goal Entirely
Maybe the actual Tait theorem proof doesn't need this exact parity claim.
The path-independence goal (`parity_sum_cycle_zero`) might need a different approach.

---

## Formal Recording in Code

Both the lemma and theorem have been marked as FALSE in `/home/zar/claude/lean-projects/fourcolor/FourColor/Tait.lean`:

```lean
/-- FALSE LEMMA: ... [K₄ counterexample detailed] ... -/
lemma cycle_color_alternates : ... := by
  sorry -- IMPOSSIBLE to prove
```

```lean
/-- The attempted theorem is FALSE. See comment above. -/
theorem color_parity_in_cycle : ... := by
  sorry -- IMPOSSIBLE: counterexample exists
```

---

## Next Steps

1. **Understand actual theorem requirement**: What does Tait's theorem actually need from the parity claim?
2. **Find correct formulation**: Can we restrict to a specific cycle type that preserves the parity property?
3. **Alternative approach**: Is there a completely different line of proof that avoids this false lemma?

**Status**: Awaiting guidance on how to reformulate the proof strategy.
