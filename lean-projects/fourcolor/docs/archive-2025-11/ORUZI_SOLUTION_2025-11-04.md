# Oruži's Solution: Component-After-Delete for H2/H3

**Date**: 2025-11-04
**Credit**: Oruži's brilliant insight that resolved the H2/H3 blocker

---

## The Problem

I was stuck trying to prove:
```lean
If S₀ ⊆ facesTouching₁ G x and e ∈ cutEdges G S₀ (internal),
then e ∈ support₁ x
```

This was **blocking H3 strict descent** because I needed to show that `(toggleSum e).fst = 0` for edges outside the support.

## The Insight

**This property is FALSE in general!**

Oruži explained: A face can touch `support₁ x` at one edge while having other edges outside the support. If we build `S₀` via reachability across support edges only, non-support boundary edges can appear in exactly one face of `S₀`, making them cut edges.

## The Solution: Component-After-Delete

**Don't try to prove the impossible. Instead, construct S₀ differently!**

### New H2 Construction

Instead of using `facesTouching₁`, construct `S₀` as the **dual component after deleting e₀**:

1. Pick one face `f₀` incident to interior edge `e₀`
2. Let `S₀` = all faces reachable from `f₀` without crossing `e₀` in the dual graph
3. **Result**: `cutEdges G S₀ = {e0}` **by construction**!

### Why This Works

- **For e₀**: Exactly one of its two incident faces is in `S₀` → `e₀ ∈ cutEdges`
- **For e ≠ e₀** (interior): Both incident faces are reachable together (can cross that edge) → either both in `S₀` or both out → `e ∉ cutEdges`
- **Result**: `cutEdges G S₀ = {e0}` exactly!

### Implementation

Added to `Disk.lean`:

```lean
-- Dual adjacency excluding e0
def adjExcept (e0 : E) (f g : Finset E) : Prop :=
  f ∈ G.toRotationSystem.internalFaces ∧
  g ∈ G.toRotationSystem.internalFaces ∧
  ∃ e, e ≠ e0 ∧ e ∉ G.toRotationSystem.boundaryEdges ∧ e ∈ f ∧ e ∈ g

-- Component after deleting e0
def compAfterDeleteSet (e0 : E) (f0 : Finset E) : Set (Finset E) :=
  { f | f ∈ G.toRotationSystem.internalFaces ∧
        Relation.ReflTransGen (adjExcept (G := G) e0) f0 f }

-- H2: Existence lemma
lemma exists_S₀_component_after_delete
    {e0 : E} (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges) :
    ∃ S₀ : Finset (Finset E),
      S₀ ⊆ G.toRotationSystem.internalFaces ∧
      S₀.Nonempty ∧
      cutEdges G S₀ = {e0}
```

## Impact on H3

**H3 becomes trivial!**

The old H3 (`aggregated_toggle_strict_descent_at_prescribed_cut₁`) tried to use:
- `S₀ ⊆ facesTouching₁` (support-aware)
- `cutEdges₁ G x S₀ = {e0}` (filtered to support)

The **new H3** uses:
- `S₀ ⊆ internalFaces` (support-agnostic)
- `cutEdges G S₀ = {e0}` (EXACT cut edges)

With `cutEdges = {e0}` exactly, we know:
- `(toggleSum e).fst ≠ 0` iff `e = e0` (by `toggleSum_supported_on_cuts_10`)
- Apply `support₁_add_toggles_singleton` to get `support₁ (x + toggleSum) = support₁ x \ {e0}`
- **Strict descent achieved!**

## The Blocked Proof Is Gone

I was trying to prove (at line 646):
```lean
e ∉ support₁ x → (toggleSum e).fst = 0  -- for e ≠ e0
```

**With the new construction, this follows immediately** from `cutEdges = {e0}`:
- If `e ≠ e0`, then `e ∉ cutEdges`
- Therefore `(toggleSum e).fst = 0` by `toggleSum_supported_on_cuts_10`
- **No need to reason about support at all!**

## Alignment with Goertzel v3

This perfectly matches v3's **aggregated peel** approach:

- v3 §4.2-4.4: Use multi-face toggles for strict descent
- v3: Component structure in the dual gives clean algebraic witnesses
- Our implementation: `LeafPeelSumData` + `toggleSum` + component-after-delete

The construction is:
- ✅ **Linear/algebraic** (no global graph search)
- ✅ **Finitary** (finite reachability relation)
- ✅ **ATP-friendly** (uses "two faces per interior edge" + reachability)

## Remaining Work

### H2: One Graph Theory Sorry (line 609)
Prove: `cutEdges G S₀ = {e0}`

**Strategy**:
1. (⊆): Show any cut edge must be e0
   - If `e ≠ e0` is a cut edge, it has two incident faces
   - Use `two_internal_faces_of_interior_edge`
   - By `adjExcept` definition, both faces are reachable together
   - Contradiction
2. (⊇): Show e0 is a cut edge
   - f0 (seed) is in S₀
   - The other face across e0 is NOT reachable (can't cross e0)
   - Therefore e0 has exactly one incident face in S₀

**Estimated**: ~40-50 lines of standard graph theory

### H3: Already Structured
The non-support-aware version `aggregated_toggle_strict_descent_at_prescribed_cut` exists and just needs the pointwise toggle lemma, which is complete.

### Legacy Compatibility (line 624)
Connect old support-aware H2 to new version (optional, for compatibility)

## Key Takeaway

**Sometimes the problem isn't solvable - you need to change the problem!**

Instead of proving `cutEdges ⊆ support` (false), we construct S₀ so that `cutEdges = {e0}` exactly. This makes everything downstream trivial.

This is the essence of the Mario Carneiro / Oruži approach: find the right statement, and the proof becomes mechanical.

---

## Migration Checklist

- [x] Add `adjExcept` and `compAfterDeleteSet` definitions
- [x] Add `exists_S₀_component_after_delete` structure
- [ ] Complete H2 graph theory proof (cutEdges = {e0})
- [ ] Verify H3 non-support-aware path
- [ ] Update documentation to prefer component-after-delete
- [ ] Mark old support-aware versions as legacy

**Status**: Infrastructure complete, ~50 lines of graph theory remaining for full H2/H3 completion!
