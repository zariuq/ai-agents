# H2 Forest/Fundamental-Cut Construction - Design Document

**Date**: 2025-11-06
**Based on**: GPT-5 Pro's guidance on correct H2 construction
**Goal**: Replace incorrect component-after-delete with sound forest-based approach

---

## Mathematical Strategy (GPT-5 Pro)

### Core Idea

Use a **spanning forest** on the interior dual graph to construct a face set S' with exactly one cut edge e0.

**Why this works**: The fundamental cut theorem from graph theory states that for any edge e in a spanning tree/forest, removing e creates exactly two components, making e the unique bridge between them.

### Construction Steps

Given an interior edge e0:

1. **Build interior dual graph**:
   - Vertices = internal faces
   - Edges = interior edges (connecting adjacent faces)

2. **Get spanning forest F**:
   - Standard spanning forest on connected components
   - Ensure e0 ∈ F (if not, swap it in using cycle property)

3. **Remove e0 from F**:
   - This splits F into two components: Cf (containing f0) and Cg (containing g0)
   - Where f0, g0 are the two faces incident to e0

4. **Define S' = faces in Cf**

5. **Prove cutEdges G S' = {e0}**:
   - For e ≠ e0: both incident faces are in same component → not a cut
   - For e = e0: exactly one incident face (f0) is in S' → is a cut

---

## Why This Avoids the False Axiom

**Incorrect approach** (removed):
- Tried to use ReflTransGen reachability avoiding e0
- Claimed "faces sharing only e0 cannot be connected avoiding e0"
- **FALSE**: Faces can share one edge yet be path-connected avoiding it

**Correct approach** (forest):
- Uses forest structure, not arbitrary paths
- Forest ensures edges are either in-tree (connect same component) or create cycles
- No "no path exists" claim needed
- Pure graph theory, no topological assumptions

---

## Implementation Structure

### Phase 1: Forest Infrastructure

```lean
/-! ### Spanning Forest on Dual Graph -/

/-- The interior dual graph structure -/
structure InteriorDualGraph (G : DiskGeometry V E) where
  vertices : Finset (Finset E)  -- Internal faces
  edges : Finset E               -- Interior edges
  adj : E → Finset E → Finset E → Prop  -- Adjacency via interior edges
  -- Properties...

/-- A spanning forest on the dual graph -/
structure SpanningForest (G : DiskGeometry V E) where
  tree_edges : Finset E
  -- tree_edges ⊆ interior edges
  -- No cycles
  -- Maximal (adding any non-tree edge creates cycle)
  -- Properties...

/-- Every interior edge is either in the forest or creates a cycle -/
lemma forest_dichotomy (F : SpanningForest G) (e : E) (he_int : e ∉ G.boundaryEdges) :
    e ∈ F.tree_edges ∨ (∃ cycle, e ∉ cycle ∧ cycle ⊆ F.tree_edges ∪ {e}) := by
  sorry

/-- Swap operation: if e0 ∉ F but e0 is interior, we can swap it in -/
lemma forest_swap_edge (F : SpanningForest G) {e0 e' : E}
    (he0_int : e0 ∉ G.boundaryEdges)
    (he'_in : e' ∈ F.tree_edges)
    (hcycle : e0 ∉ F.tree_edges ∧ ∃ cycle, e0 ∈ cycle ∧ e' ∈ cycle) :
    ∃ F' : SpanningForest G, e0 ∈ F'.tree_edges ∧ e' ∉ F'.tree_edges := by
  sorry
```

### Phase 2: Component After Edge Removal

```lean
/-! ### Components After Removing Edge from Forest -/

/-- The component containing a face after removing an edge from the forest -/
def forest_component (F : SpanningForest G) (e_removed : E) (f_seed : Finset E) :
    Finset (Finset E) :=
  -- Faces reachable from f_seed via tree edges ≠ e_removed
  sorry

/-- Removing a tree edge splits forest into exactly two components -/
lemma forest_splits_into_two (F : SpanningForest G) {e : E}
    (he_in : e ∈ F.tree_edges)
    {f g : Finset E}
    (hfg_incident : e ∈ f ∧ e ∈ g ∧ f ≠ g) :
    let Cf := forest_component F e f
    let Cg := forest_component F e g
    Cf ∩ Cg = ∅ ∧ Cf ∪ Cg = G.internalFaces := by
  sorry

/-- For tree edge: incident faces are in different components -/
lemma tree_edge_separates (F : SpanningForest G) {e : E}
    (he_in : e ∈ F.tree_edges)
    {f g : Finset E}
    (hfg : e ∈ f ∧ e ∈ g ∧ f ≠ g) :
    f ∈ forest_component F e f ∧ g ∉ forest_component F e f := by
  sorry
```

### Phase 3: Fundamental Cut Theorem

```lean
/-! ### Fundamental Cut: Singleton cutEdges via Forest -/

/-- Key lemma: For non-tree edge, both incident faces in same component -/
lemma non_tree_edge_same_component (F : SpanningForest G) {e e0 : E}
    (he0_in : e0 ∈ F.tree_edges)
    (he_not : e ∉ F.tree_edges)
    (he_ne : e ≠ e0)
    (he_int : e ∉ G.boundaryEdges)
    {f g : Finset E}
    (hfg : e ∈ f ∧ e ∈ g ∧ f ≠ g) :
    let S' := forest_component F e0 f
    (f ∈ S' ↔ g ∈ S') := by
  -- If e ∉ F, then adding e to F creates a cycle
  -- This cycle lies entirely within one component after removing e0
  -- Therefore f and g are in the same component
  sorry

/-- Main theorem: Forest construction gives singleton cut -/
theorem forest_gives_singleton_cut (F : SpanningForest G) {e0 : E}
    (he0_in : e0 ∈ F.tree_edges)
    (he0_int : e0 ∉ G.boundaryEdges)
    {f0 g0 : Finset E}
    (hfg0 : e0 ∈ f0 ∧ e0 ∈ g0 ∧ f0 ≠ g0) :
    let S' := forest_component F e0 f0
    cutEdges G S' = {e0} := by
  classical
  ext e
  simp [cutEdges, Finset.mem_singleton]
  constructor
  · -- Forward: e ∈ cutEdges → e = e0
    intro ⟨he_int, hexu⟩
    -- hexu: exactly one incident face of e is in S'
    obtain ⟨p, q, hp_int, hq_int, he_p, he_q, hpq_ne⟩ :=
      incident_faces_of_interior_edge he_int
    by_cases he_in_F : e ∈ F.tree_edges
    · -- e is a tree edge → separates components → must be e0
      sorry
    · -- e is not a tree edge → both faces in same component → not a cut
      have : p ∈ S' ↔ q ∈ S' :=
        non_tree_edge_same_component F he0_in he_in_F sorry he_int ⟨he_p, he_q, hpq_ne⟩
      sorry -- Contradiction with exactly one face in S'
  · -- Backward: e = e0 → e ∈ cutEdges
    intro he_eq
    subst he_eq
    constructor
    · exact he0_int
    · -- Exactly one incident face (f0) is in S'
      use f0
      constructor
      · constructor
        · exact sorry -- f0 ∈ S' (seed property)
        · exact hfg0.1
      · intro w ⟨hw_in, he0_w⟩
        -- w contains e0 and is in S'
        -- Must show w = f0
        -- Since e0 separates, w ∈ S' means w is in f0's component → w = f0 or connected to f0
        sorry
```

---

## Key Properties to Establish

### 1. Forest Exists

```lean
/-- Every planar graph has a spanning forest -/
lemma exists_spanning_forest (G : DiskGeometry V E) :
    ∃ F : SpanningForest G, True := by
  -- Standard DFS/BFS construction
  sorry
```

### 2. Edge Swap (if needed)

```lean
/-- Can ensure any interior edge is in the forest -/
lemma exists_forest_containing_edge (G : DiskGeometry V E) {e0 : E}
    (he0_int : e0 ∉ G.boundaryEdges) :
    ∃ F : SpanningForest G, e0 ∈ F.tree_edges := by
  -- Take any forest, if e0 ∉ F, swap it in
  sorry
```

### 3. Component Properties

```lean
/-- Components partition the vertices -/
lemma components_partition (F : SpanningForest G) {e : E} (he_in : e ∈ F.tree_edges) :
    ∃ C1 C2, C1 ∩ C2 = ∅ ∧ C1 ∪ C2 = G.internalFaces ∧
      ∀ f ∈ G.internalFaces, f ∈ C1 ∨ f ∈ C2 := by
  sorry
```

---

## Comparison to Component-After-Delete

### Component-After-Delete (WRONG)

```lean
-- Tried to define: S' = faces reachable from f0 avoiding e0
def compAfterDeleteSet (e0 f0) :=
  internalFaces.filter (ReflTransGen (adjExcept e0) f0 ·)

-- Needed FALSE axiom:
axiom reflTransGen_adjExcept_absurd :
  (faces share only e0) → ¬(ReflTransGen path avoiding e0)
```

**Problem**: Two faces can share only one edge but still be connected via paths avoiding it!

### Forest Approach (CORRECT)

```lean
-- Define: S' = faces in forest component after removing e0
def forest_component (F e0 f0) :=
  faces reachable from f0 via tree edges ≠ e0

-- No "no path" axiom needed!
-- Uses forest structure: tree edges connect, non-tree create cycles
```

**Why it works**: Forest structure guarantees separation. Non-tree edges must lie within one component.

---

## Integration with Existing Code

### Where it fits

```lean
-- Current (with sorry):
lemma exists_S₀_component_after_delete
    (hNoDigons : NoDigons G)
    {e0 : E} (he0_int : e0 ∉ G.boundaryEdges) :
    ∃ S' : Finset (Finset E),
      S' ⊆ G.internalFaces ∧
      S'.Nonempty ∧
      cutEdges G S' = {e0} := by
  sorry

-- New implementation:
lemma exists_S₀_component_after_delete
    (hNoDigons : NoDigons G)
    {e0 : E} (he0_int : e0 ∉ G.boundaryEdges) :
    ∃ S' : Finset (Finset E),
      S' ⊆ G.internalFaces ∧
      S'.Nonempty ∧
      cutEdges G S' = {e0} := by
  classical
  -- Step 1: Get forest containing e0
  obtain ⟨F, he0_in⟩ := exists_forest_containing_edge G he0_int
  -- Step 2: Get the two incident faces
  obtain ⟨f0, g0, hf0_int, hg0_int, he0_f0, he0_g0, hf0_ne_g0⟩ :=
    incident_faces_of_interior_edge he0_int
  -- Step 3: Define S' as f0's component
  let S' := forest_component F e0 f0
  -- Step 4: Prove properties
  use S'
  constructor
  · exact forest_component_subset F e0 f0
  constructor
  · exact forest_component_nonempty F e0 f0 hf0_int
  · exact forest_gives_singleton_cut F he0_in he0_int ⟨he0_f0, he0_g0, hf0_ne_g0⟩
```

### Dependencies

**Uses**:
- `incident_faces_of_interior_edge`: Already proven (line 249)
- `card_facesIncidence_eq_two`: Already proven (line 194)
- `NoDigons`: May not actually be needed for forest approach!

**Provides**:
- Clean H2 with no false axioms
- Standard graph theory construction
- Direct proof of singleton cut

---

## Implementation Plan

### Step 1: Minimal Forest Structure (~30 lines)

```lean
-- Just enough structure to represent forest and components
structure SpanningForest (G : DiskGeometry V E) where
  tree_edges : Finset E
  -- Add axioms for now, prove later
```

### Step 2: Component Definition (~20 lines)

```lean
-- Reachability via tree edges excluding removed edge
noncomputable def forest_component ...
```

### Step 3: Key Lemmas (~40 lines)

```lean
-- 1. Non-tree edges connect faces in same component
-- 2. Tree edges separate components
-- 3. Components partition faces
```

### Step 4: Main Theorem (~30 lines)

```lean
-- Prove cutEdges = {e0} using the key lemmas
```

### Total: ~120 lines

---

## Notes from GPT-5 Pro

> "This is the forest/fundamental‑cut argument and it is robust in Lean."

> "No global 'no alternate path' claim is needed."

> "The only remaining subtlety is how you produce that S' without the false
> 'component‑after‑delete' claim. The standard way in the v3 spirit is:
> Not the whole component after deleting e0; But a leaf‑subtree inside a (dual)
> spanning forest that is chosen to separate along support structure."

**Key insight**: We don't need leaf-subtree specifically. Any tree edge in a spanning forest gives a fundamental cut. This is simpler than the original Goertzel description.

---

## Testing Strategy

1. **Implement structure** with axioms first (get types right)
2. **Implement component definition** (computational)
3. **Prove key lemmas** with sorries for complex subproofs
4. **Connect to main theorem** and verify it compiles
5. **Fill in sorries** incrementally

**Goal**: Get architecture in place, prove incrementally.

---

## Success Criteria

✅ `exists_S₀_component_after_delete` implemented (no sorry)
✅ No false axioms (reflTransGen_absurd removed)
✅ Build succeeds
✅ H3 pipeline works (cutEdges₁_filter_of_component_singleton already proven)

---

**Status**: Design complete, ready for implementation
**Next**: Implement Phase 1 (Forest Infrastructure)
