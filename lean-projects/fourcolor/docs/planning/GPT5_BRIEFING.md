# GPT-5 Pro Briefing: Completing Tait's Equivalence Theorem

## Environment Setup

**Lean Version**: 4.24.0-rc1
```bash
$ lean --version
Lean (version 4.24.0-rc1, x86_64-unknown-linux-gnu, commit 48f7e53ce2fd, Release)
```

**Mathlib Commit**: `06d95e5f5311594940c0c3dff5381fabe4fcabe7`

**Working Directory**: `/home/zar/claude/lean-projects/fourcolor`

**Primary File**: `FourColor/Tait.lean`

## Current State

### What's Complete ✅
1. **`tait_forward` theorem** (line 244-331): Proves that 4-vertex-coloring → 3-edge-coloring
   - 100% complete, no sorries
   - Uses TriangleNeighborhood interface to extract third color at each vertex
   - XOR arithmetic in F₂² = Bool × Bool

2. **XOR Infrastructure**:
   - `Bits.add_self` (line 130-132): Proves `x + x = (0,0)` in F₂²
   - `bits_add_right_cancel` (line 134-138): Proves `a + b = a ↔ b = (0,0)`
   - Used exhaustive case analysis with `decide` tactic

3. **Axioms Added**:
   - `parity_sum_cycle_zero` (line 226-230): Path-independence of XOR sums around cycles
   - `adj_iff_shared_edge` (line 235-240): Adjacency ↔ shared edge relationship

### What Remains 🔴

**Three sorries remaining**:

1. **Line 436**: Potential function construction in `tait_reverse`
   ```lean
   have h_potential_exists : ∃ (potential : V → Bool × Bool),
     (∀ u v e, adj u v → e ∈ incident u → e ∈ incident v →
       potential v = potential u + EdgeColor.toBits (edge_coloring.color e)) := by
     sorry
   ```
   This is the core blocker - requires proving graph connectivity from bridgeless property,
   path-finding infrastructure, and the parity axiom for path-independence.

2. **Line 512**: Forward direction wrapper in `four_color_equiv_tait` (4CT ⟹ 3-edge-colorable)
   ```lean
   sorry
   ```

3. **Line 536**: Reverse direction wrapper in `four_color_equiv_tait` (3-edge-colorable ⟹ 4CT)
   ```lean
   sorry
   ```
   These wrappers require dual graph infrastructure.

## The Challenge: Potential Function Construction

### Mathematical Idea

Given a 3-edge-coloring of a cubic bridgeless graph, construct a vertex labeling `potential : V → F₂²` such that:
- Adjacent vertices differ by the XOR of the connecting edge's color
- `potential v = potential u + EdgeColor.toBits (edge_coloring.color e)`

**Construction Strategy**:
1. Pick arbitrary base vertex `v₀`, set `potential v₀ = (0,0)`
2. For any vertex `v`, pick path `v₀ → v₁ → v₂ → ... → v`
3. Define `potential v = XOR sum of edge colors along the path`
4. **Well-definedness**: The `parity_sum_cycle_zero` axiom guarantees path-independence

### Why This is Blocked

Missing infrastructure in three areas:

#### 1. Connectivity
**Need**: Proof that bridgeless finite graphs are connected

**Current situation**: We have `bridgeless` hypothesis but no lemma proving connectivity
```lean
bridgeless : ∀ e, e ∈ edges → ¬IsBridge adj e
```

**What's needed**:
```lean
lemma bridgeless_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj]
    (edges : Finset E)
    (bridgeless : ∀ e, e ∈ edges → ¬IsBridge adj e)
    (cubic : ∀ v, (univ.filter (adj v)).card = 3) :
    ∀ u v, ∃ path : List V, path.Chain' adj ∧ path.head? = some u ∧ path.getLast? = some v
```

Mathlib likely has infrastructure for this via `SimpleGraph.Connected`, but adapting it to our `V → V → Prop` adjacency relation needs work.

#### 2. Path-Finding Machinery

**Need**: Constructive way to obtain paths between vertices

**Options**:
- **Classical choice**: Use `Classical.choose` on the connectivity proof
- **Explicit BFS**: Construct spanning tree via breadth-first search
- **Mathlib's `SimpleGraph.Walk`**: Adapt existing path infrastructure

**Current attempt pattern**:
```lean
by_cases h : Nonempty V
case pos =>
  obtain ⟨v₀⟩ := h
  use fun v =>
    if v = v₀ then (false, false)
    else
      let path := Classical.choose (connectivity_proof v₀ v)
      xor_sum_along_path path edge_coloring
```

#### 3. Invoking `parity_sum_cycle_zero`

**The axiom** (line 226-230):
```lean
axiom parity_sum_cycle_zero
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (incident : V → Finset E)
    (edge_coloring : EdgeColoring E)
    (cycle : List V)
    (hcycle : cycle.Chain' (fun u v => ∃ e, e ∈ incident u ∧ e ∈ incident v))
    (hclosed : cycle.head? = cycle.getLast?) :
    (cycle.zipWith (·) cycle.tail!).foldl
      (fun acc (u, v) =>
        let e := Classical.choose (shared_edge_exists u v)
        acc + EdgeColor.toBits (edge_coloring.color e))
      (false, false) = (false, false)
```

**Challenge**: To prove path-independence, need to:
1. Take two paths from `v₀` to `v`
2. Form a cycle by concatenating path1 with path2.reverse
3. Apply `parity_sum_cycle_zero` to show XOR sum is zero
4. Conclude that path1 and path2 give same potential value

## Concrete Task for GPT-5 Pro

### Primary Goal
Complete the sorry at **line 437** in `FourColor/Tait.lean` by constructing the potential function.

### Suggested Approach

**Step 1**: Prove or find connectivity
- Search Mathlib for bridgeless → connected lemmas
- Adapt to our `adj : V → V → Prop` setting
- May need to convert to `SimpleGraph` temporarily

**Step 2**: Get base vertex
- Prove `Nonempty V` from cubic property (cubic graphs must have vertices)
- Or use `by_cases h : Nonempty V` with classical reasoning

**Step 3**: Define potential via Classical.choose
```lean
use fun v =>
  if h : v = v₀ then (false, false)
  else
    let path := Classical.choose (connectivity_proof v₀ v)
    compute_xor_sum path edge_coloring incident
```

**Step 4**: Prove adjacency property
For adjacent `u, v` sharing edge `e`, show:
```lean
potential v = potential u + EdgeColor.toBits (edge_coloring.color e)
```
This requires:
- Extracting paths to both `u` and `v`
- Using path-independence (parity axiom)
- Case analysis on whether paths share edges

### Key Lemmas to Search For

In Mathlib (may need adaptation):
- `SimpleGraph.Connected.exists_walk` - connectivity to paths
- `SimpleGraph.Walk` - path infrastructure
- Bridge/cut-edge theorems
- Graph connectivity from local properties

### Hints from Local Knowledge Base

File: `how-to-lean.md` contains patterns for:
- Using `ReflTransGen` for transitive closure
- Classical reasoning patterns
- Working with inductive types
- Symmetric relations

### Build Status

The file currently **compiles successfully** with these 2 sorries:
```bash
$ lake build FourColor.Tait
# Builds with warnings about sorries but no errors
```

## What Success Looks Like

When complete:
1. Line 437 sorry replaced with actual construction
2. Line 493 sorry filled by composing `tait_forward` and `tait_reverse`
3. Full build succeeds: `lake build FourColor.Tait`
4. Proof is constructive (or uses minimal classical choice)

## Additional Context

### F₂² = Bool × Bool Encoding
- `(false, false)` = identity element
- Addition = componentwise XOR
- `EdgeColor` and `VertexColor` both map to F₂²
- All four colors are distinct in F₂²

### Cubic Graph Property
```lean
cubic : ∀ v, (univ.filter (adj v)).card = 3
```
Every vertex has exactly 3 neighbors.

### Bridgeless Property
```lean
bridgeless : ∀ e, e ∈ edges → ¬IsBridge adj e
```
No edge disconnects the graph when removed.

## Questions to Consider

1. Can we adapt `SimpleGraph.Connected` to our `Prop`-valued adjacency?
2. Is there a cleaner way than Classical.choose for path extraction?
3. Can we leverage existing Mathlib infrastructure for XOR sums over paths?
4. Should we define helper functions for path XOR computation?

## Files to Reference

- **Main file**: `FourColor/Tait.lean`
- **Rotation system**: `FourColor/Geometry/RotationSystem.lean` (has graph infrastructure)
- **Local knowledge**: `how-to-lean.md`
- **Previous progress docs**: `PROGRESS_2025-11-06.md`, `TAIT_CORRECTION_2025-11-06.md`

---

**Bottom Line**: The mathematical approach is sound. We need to bridge the gap between our axioms (especially `parity_sum_cycle_zero`) and Lean's type system by finding or proving graph connectivity, then using classical choice to extract paths and compute XOR sums.

Good luck! 🎯
