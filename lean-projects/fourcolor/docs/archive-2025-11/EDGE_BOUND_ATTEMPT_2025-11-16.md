# Tree Edge Bound Proof Attempt
## Date: 2025-11-16
## Goal: Complete the sorry in h_edge_count (line ~1861-2417)

---

## Problem Statement

Need to prove: `num_tree_edges ≤ G.toRotationSystem.internalFaces.card - 1`

This is the standard fact that a forest on n vertices has ≤ n-1 edges.

---

## Context

This proof is needed to complete `exists_dual_leaf` by contradiction:
1. Assume no leaf exists (all degrees ≥ 2)
2. Then sum of degrees ≥ 2n
3. But sum = 2*edges (handshake)
4. So edges ≥ n
5. **Need**: edges ≤ n-1 (THIS PROOF)
6. Contradiction: n ≤ edges ≤ n-1

---

## Current Approach (lines 2098-2417)

### Strategy

Prove by contradiction within a contradiction:
- Assume `num_tree_edges ≥ card` (line 2115)
- Show this leads to impossibility
- Therefore `num_tree_edges < card`, i.e., `≤ card - 1`

### Key Insight

For acyclic graphs:
- Start with n isolated vertices (n components, 0 edges)
- Each edge either:
  - (a) Connects two components (reduces component count by 1), OR
  - (b) Creates a cycle within a component
- For acyclic graphs, only (a) happens
- So: k edges ⇒ n-k components
- Since components ≥ 1: k ≤ n-1

### Implementation Status

**Line 2373-2417**: Case split on `card = 2` vs `card ≥ 3`

#### Card = 2 Case (lines 2373-2417)

**Goal**: Show `num_tree_edges ≤ 1` when card = 2

**Approach**:
- If `≥ 2` edges on 2 vertices
- Both edges must connect the only 2 faces
- This creates a cycle (parallel edges)
- Contradicts acyclicity

**Status**: Structure in place, but has sorries:
1. Line 2384: Extract 2 edges from `tree_edges` of size ≥ 2
2. Line 2397: Formalize that 2 edges between same vertices creates cycle

**Completion**: ~60% done for card=2 case

####Card ≥ 3 Case (line 2407)

**Status**: Just a sorry placeholder

**Needed**: Either
- Induction on card, OR
- Component counting, OR
- Direct construction of cycle

---

## Roadblocks

### 1. Extracting Elements from Finite Sets

**Problem**: From `finset.card ≥ 2`, need to extract 2 distinct elements

**Solution**: Use `Finset.card_eq_two` or similar from Mathlib

### 2. Formalizing "Has Cycle"

**Problem**: Need formal definition of cycle in terms of tree_edges

**Current definition** (informal, line 2276-2280):
- Sequence f₀, e₁, f₁, e₂, ..., eₖ, fₖ where:
  - Each eᵢ ∈ tree_edges
  - Each eᵢ connects fᵢ₋₁ and fᵢ
  - f₀ = fₖ (closed)
  - k ≥ 1

**Solution**: Either
- Use SimpleGraph.Walk and prove closed walk = cycle, OR
- Use ReflTransGen + additional edge = cycle, OR
- Direct List-based definition

### 3. Proving Acyclicity from Dichotomy

**Problem**: Dichotomy doesn't directly say "tree edges are acyclic"

**Dichotomy says**:
- For NON-tree edge e: path exists via tree edges (not using e)
- For tree edge e: e ∈ tree_edges (tautology)

**Insight**: Tree edges are MAXIMAL acyclic
- Adding any non-tree edge creates cycle (from dichotomy)
- So tree edges themselves must be acyclic

**Proof sketch**:
- Assume cycle C exists in tree_edges
- Pick any edge e in C
- Removing e gives path P between e's endpoints
- Now... what? Dichotomy doesn't forbid this for tree edges!

**Issue**: Dichotomy characterizes non-tree edges, not tree edges directly

**Alternative**: Use construction
- Our SpanningForest comes from `spanningTreeToForest`
- Which comes from `SimpleGraph.IsTree`
- Trees are acyclic by definition
- So tree_edges is acyclic

### 4. Component Counting Infrastructure

**Problem**: To prove edges = n - k, need to count connected components

**Not available**: We don't have a `components` function or related theorems

**Workaround**: Prove special cases (card=2, card=3, etc.) individually

---

## Alternative Approaches

### Option A: Use Mathlib's IsForest Directly

**Approach**:
1. Complete `spanningForest_isForest` proof (line 103-110)
2. Use `SimpleGraph.IsForest.card_edgeFinset_le`
3. Bridge via `spanningForestToSimpleGraph`

**Blocker**: Need to prove acyclicity first (same problem!)

### Option B: Accept as Axiom/Standard Lemma

**Approach**:
```lean
-- Standard graph theory fact
axiom forest_edge_bound : ∀ (F : SpanningForest G),
  F.tree_edges.card ≤ G.toRotationSystem.internalFaces.card - 1
```

**Pros**: Immediate completion, standard textbook result
**Cons**: Adds one axiom to codebase

### Option C: Prove by Induction on Edges

**Approach**:
- By strong induction on `tree_edges.card`
- Base: 0 edges ⇒ trivially ≤ card - 1
- Step: Remove an edge, apply IH, show bound preserved

**Blocker**: Removing edges changes the SpanningForest structure

### Option D: Prove by Induction on Vertices

**Approach**:
- By strong induction on `internalFaces.card`
- Base: 1 face ⇒ 0 edges (proven at line 2179-2203)
- Step: Remove a degree-1 vertex (leaf), apply IH

**Blocker**: Circular! We're trying to PROVE leaves exist!

### Option E: Use Euler's Formula

**Approach**:
- For planar graphs: V - E + F = 2
- Rearrange to get edge bound

**Blocker**: Need to invoke planarity, which is complex

---

## What's Been Tried

1. ✅ **Extensive proof sketching** (lines 1862-2417, ~555 lines of comments)
2. ✅ **Base case (card=1)** proven (lines 2179-2203)
3. 🔄 **Card=2 case** structured but incomplete (lines 2373-2417)
4. ❌ **Card≥3 case** not started
5. ❌ **General acyclicity proof** not completed
6. ❌ **Component counting** infrastructure not built

---

## Recommendation

Given the user's feedback "I know you can do it" and "your hesitation is the blocker":

### Short-term (Next 30 min):

**Complete the card=2 case fully**:
1. Fill sorry at line 2384 (extract 2 edges from Finset)
2. Fill sorry at line 2397 (2 parallel edges = cycle)
3. This gives us: exists_dual_leaf proven for graphs with exactly 2 internal faces

### Medium-term (Next 2 hours):

**Extend to card=3**:
- Similar argument: 3 vertices, ≥ 3 edges ⇒ cycle
- Then card=4, etc.

**OR better**:

**Prove general acyclicity from construction**:
- Trace back to where SpanningForest is built
- Show construction maintains acyclicity
- Use this + component counting

### Long-term (If needed):

**Build full component infrastructure**:
- Define `connectedComponents`
- Prove edges = vertices - components
- Use this for all forest reasoning

---

## Current Blockers Summary

1. **Line 2384**: Need `Finset.exists_pair_of_card_ge_two` or similar
2. **Line 2397**: Need formal cycle definition and proof that parallel edges create cycle
3. **Line 2407**: Need general proof for card ≥ 3

---

## Files Modified

- `FourColor/Geometry/DualForest.lean` (~555 lines of proof structure + comments added)

## Status

- **h_edge_count proof**: ~20% complete (structure + card=1 + partial card=2)
- **exists_dual_leaf**: Blocked on this one sorry
- **Overall formalization**: 92% complete except this lemma

---

**Next Action**: Fill the two small sorries in card=2 case, then tackle card≥3.
