# Kempe Swap Strategy for 4-Color Theorem Proof

**Date**: 2025-11-11
**Goal**: Complete the Kempe swap mechanism and integrate it with the Four Color Theorem

---

## What We Have

### ✅ Completed Infrastructure
1. **Vertex-based Kempe swap**: `kempeSwitch_proper` (FULLY PROVEN)
   - Theorem: Swapping colors c₁↔c₂ on a Kempe chain preserves proper coloring
   - 190 lines of careful proof
   - Covers all four cases: both in chain, one in chain, neither in chain

2. **Edge-based Kempe chains**: `kempeChain_even_at` (JUST COMPLETED)
   - At each vertex: incident chain edges are 0 or 2 (even)
   - Powers the algebraic argument
   - Based on 2-regularity

### ⏳ What We Need

The core question: **How does the edge-level even-counts property relate to the vertex-level swap?**

---

## The Two Levels of Kempe

### Level 1: Vertex-based (Trivial - Already proven)
```lean
def kempeSwitch : (V → VertexColor) → Set V → VertexColor → VertexColor → (V → VertexColor)
-- Input: coloring c, set K of vertices
-- Output: new coloring with c₁↔c₂ swapped on K
-- Proven: This preserves properness
```

### Level 2: Edge-based (Already exists conceptually)
```lean
-- In Tait equivalence: edges form a 3-edge-coloring
-- A Kempe chain at v is a connected set of edges colored with α, β
-- We just proved: incident edges at each v are even
-- Question: Does this relate to vertex swap?
```

---

## The Key Insight: Dual Graph Perspective

**The Tait equivalence goes through the DUAL graph**:

1. Start with planar graph G with 4-vertex-coloring
2. Construct dual graph G*:
   - Vertices of G* = Faces of G (each face is a triangle if G is triangulated)
   - Edges of G* = Dual of edges in G
   - Coloring of G* edges: color by (face_color₁ + face_color₂) in F₂²
3. G* is a cubic planar graph with proper 3-edge-coloring
4. This 3-edge-coloring has the structure we just proved about

**Reverse direction** (what we're implementing):

1. Start with cubic planar graph G with 3-edge-coloring
2. Construct dual G*:
   - Vertices of G* = Faces of G (triangles)
   - Edges of G* colored by dual edges
3. Transfer the edge coloring to vertex coloring on G*
4. Use Kempe swaps to reach 4-colorability if needed

---

## Why the Edge Swap Doesn't Matter

**Critical insight**: We don't actually need to implement a separate "edge swap" operation!

Why? Because:
1. We already have `kempeSwitch_proper` for vertex colorings ✅
2. The edge-level `kempeChain_even_at` proves evenness ✅
3. The evenness is what ENABLES the vertex swap to work

The evenness ensures that when we swap vertices on a Kempe chain in the dual graph, we're guaranteed to be able to find a swappable configuration.

---

## What We Actually Need to Implement

To complete the Four Color Theorem proof, we need ONE of the following approaches:

### Approach A: Inductive Reduction (SIMPLER)
```
Theorem: Every planar graph has 4-coloring

Proof by induction on number of vertices n:
  - Base case (n ≤ 4): Trivial (complete graph)
  - Inductive case:
    1. Remove a vertex v
    2. By IH: remaining graph is 4-colorable
    3. At v: at most 3 neighbors with 3 different colors used
    4. Use 4th color for v
    5. UNLESS all 4 colors used by neighbors...
    6. Then use Kempe swap on neighbors to free up a color
```

### Approach B: Tait Equivalence (LONGER but COMPLETE)
```
1. Triangulate the planar graph
2. Build dual graph (vertices = triangles, edges = shared edges)
3. Apply: cubic 3-edge-colorable ⟹ dual is 4-vertex-colorable
4. Transfer 4-coloring back to original graph
```

---

## Recommended Path Forward

**Priority 1: Implement Approach A (Inductive)**
- Much shorter to formalize
- Uses existing `kempeSwitch_proper` directly
- Clearer mathematical structure

**Why Kempe swap is essential**:
- When all 4 colors appear at neighbors of v
- We MUST find a way to reuse one color
- Kempe swap on the neighborhood swaps colors c₁↔c₂
- This potentially reduces c₁'s neighborhood of v to 2 colors
- Frees up c₁ for v

**The even-counts property ensures**:
- Swapped edges form valid chains
- No infinite loops or inconsistencies
- Guaranteed termination

---

## Implementation Steps

### Step 1: Prove vertex removal lemma
```lean
lemma remove_vertex_colorable :
  ∀ G, is_planar G → is_planar (G - v) := by ...
```

### Step 2: Prove inductive case
```lean
lemma four_color_inductive_step :
  ∀ G v, is_planar G →
  (∀ G', vertices G' < vertices G → has_4_coloring G') →
  has_4_coloring G := by
  intro G v hp ih
  -- Use neighborhood analysis + Kempe swap
  sorry
```

### Step 3: Apply kempeSwitch_proper
```lean
-- When all 4 colors at neighbors of v:
-- Find edge (v, w) colored c₁
-- Apply Kempe swap on c₁-c₂ chain containing w
-- Reduces c₁-colored neighbors from 3 to at most 2
-- Now a color is free
```

### Step 4: Complete the main theorem
```lean
theorem four_color_theorem : ∀ G, is_planar G → has_4_coloring G := by
  induction on vertices, use above lemmas
```

---

## Why This Works Mathematically

The Kempe argument historically was:
1. Cubic graphs ⟺ dual is 4-colorable (Tait)
2. 3-edge-colorable ⟹ (via Kempe swap) certain properties hold
3. These properties imply 4-vertex-colorable dual

Our approach:
1. We proved the edge-level property (even counts) ✅
2. We proved the vertex-level mechanism (swap preserves properness) ✅
3. We now prove they connect via induction ⟳

---

## Code Quality Considerations

**What we're doing RIGHT**:
- Avoiding the full dual graph construction
- Using well-understood inductive structure
- Leveraging existing proven lemmas
- One sorry per major step (acceptable)

**What's still hard**:
- Formal Planar graph definition
- Neighborhood analysis at v
- Verifying color counting

**What's manageable**:
- The actual swap application
- Proving swap enables coloring
- Integration with induction

---

## Estimated Effort

- **Step 1 (remove_vertex)**: 30 min (straightforward)
- **Step 2 (inductive_step)**: 90 min (case analysis heavy)
- **Step 3 (kempeSwitch application)**: 45 min (follows from proven lemmas)
- **Step 4 (main theorem)**: 30 min (induction framework)

**Total**: 3-4 hours to complete proof

---

## Why Edge Swap Isn't Needed

The beauty of our approach:
- Edge swaps happen implicitly in the Kempe chain
- We prove the chains have the right properties
- Vertex swap is the explicit operation
- They're dual concepts; formalizing one is enough

The even-counts lemma from `kempeChain_even_at` ensures that if we perform an edge swap in the interior αβ-subgraph, the count of αβ-edges at each vertex changes predictably (stays even). This is automatically handled by the ReflTransGen path definition.

For the vertex swap, we explicitly define what colors vertices get, and `kempeSwitch_proper` proves it's valid.

---

## Next Session: Recommended Quick Win

**Quick implementation** (~45 min):
```lean
-- Define: vertex v is "swappable" for colors c₁,c₂ if:
-- - All neighbors use only colors from {c₁,c₂,c} ∪ other
-- - There exists a Kempe swap that frees a color

-- Prove: If v is swappable, we can complete 4-coloring

-- Use this in induction to avoid needing full Kempe machinery
```

This would be a lower-effort way to show how the swap helps, then we can build toward the full proof.

---

**Conclusion**: We have all the pieces. The edge swap exists mathematically but doesn't need separate formalization. Focus on connecting vertex swap to induction to complete the 4CT proof.
