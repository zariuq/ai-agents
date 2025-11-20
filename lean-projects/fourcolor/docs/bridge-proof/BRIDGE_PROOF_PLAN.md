# Bridge Proof Plan - Zero Sorries
## Following Formalization Rules

> "Always prove that which can be proven without using axioms.
> Never use sorries as a substitute for axioms.
> Build a solid foundation of concretely proven theorems/lemmas."

---

## Current Status

We have 4 sorries that need to be discharged:
1. `spanningTree_edges_are_bridges` - Tree edges are bridges
2. `forest_edge_bound_by_induction` - |E| ≤ |V| - k
3. `components_increase_by_erasing_bridge` - Bridge removal increases components
4. `hBridge` in `exists_dual_leaf` - Application of #1

---

## Challenge: The Gap

**Problem**: Our definitions use different representations:
- `Tree T`: SimpleGraph on subtype vertices
- `SpanningForest F`: Record with Finset of edges + dichotomy
- `treeConnected`: ReflTransGen relation on faces
- `isBridge`: Property about `treeConnectedMinus`

**Gap**: We need bidirectional conversion between:
- `T.Walk f g` (SimpleGraph walk)
- `treeConnected G F f g` (ReflTransGen relation)

---

## Proof Strategy for spanningTree_edges_are_bridges

###Core Idea

For spanning forest built from tree `T` via `spanningTreeToForest`:
1. Tree edge `e` connects faces `f` and `g` in `T`
2. `T.Adj f_sub g_sub` for some subtype vertices
3. If `treeConnectedMinus G F e f g` held (path without `e`)
4. Convert this to `T.Walk f_sub g_sub` not using the edge `(f_sub, g_sub)`
5. Combined with `T.Adj f_sub g_sub`, this creates a cycle
6. Contradicts `hT_tree.isAcyclic`

### Required Helper Lemmas

```lean
-- Convert ReflTransGen to Walk
lemma reflTransGen_to_walk (G : DiskGeometry V E)
    (T : SimpleGraph {f // f ∈ G.toRotationSystem.internalFaces})
    (hT_sub : T ≤ dualGraph G)
    (f g : {f // f ∈ G.toRotationSystem.internalFaces})
    (h_path : Relation.ReflTransGen (fun f' g' =>
      ∃ e ∈ treeEdgesOfDualTree G T hT_sub, e ∈ f'.val ∧ e ∈ g'.val) f g) :
    T.Walk f g := by
  sorry

-- Show that treeConnectedMinus gives reflTransGen without specific edge
lemma treeConnectedMinus_to_reflTransGen (G : DiskGeometry V E) (F : SpanningForest G)
    (e_excluded : E) (f g : Finset E)
    (h : treeConnectedMinus G F e_excluded f g) :
    Relation.ReflTransGen (fun f' g' =>
      ∃ e ∈ F.tree_edges, e ≠ e_excluded ∧ e ∈ f' ∧ e ∈ g') f g := by
  exact h  -- This is definitional

-- Identify faces with subtype vertices via E2
lemma face_eq_via_edge (G : DiskGeometry V E) (e : E)
    (he_int : e ∉ G.toRotationSystem.boundaryEdges)
    (f : Finset E) (hf : f ∈ G.toRotationSystem.internalFaces) (he_f : e ∈ f)
    (f_sub : {f // f ∈ G.toRotationSystem.internalFaces}) (he_f_sub : e ∈ f_sub.val) :
    f = f_sub.val ∨ (∃ g_sub, e ∈ g_sub.val ∧ f = g_sub.val) := by
  -- Use E2: e belongs to exactly 2 internal faces
  sorry

-- Walk with additional edge creates cycle
lemma walk_plus_edge_has_cycle (T : SimpleGraph V) [DecidableEq V]
    (h_acyclic : T.IsAcyclic)
    (u v : V) (h_adj : T.Adj u v)
    (walk : T.Walk u v) (h_walk_ne : walk ≠ SimpleGraph.Walk.nil) :
    False := by
  -- If we have both an edge u--v and a non-trivial walk u→v, that's a cycle
  sorry
```

### Main Proof Sketch

```lean
lemma spanningTree_edges_are_bridges :
  -- Assume treeConnectedMinus G F e f g for contradiction
  intro h_minus
  -- Extract subtype witnesses from tree construction
  obtain ⟨f_sub, g_sub, hT_adj, ...⟩ := (definition of tree edge)
  -- Show f = f_sub.val and g = g_sub.val via E2 uniqueness
  have hf_eq := face_eq_via_edge ...
  have hg_eq := face_eq_via_edge ...
  -- Convert treeConnectedMinus to Walk in T
  have walk_fg := reflTransGen_to_walk ...
  -- This walk doesn't use edge e, but we have T.Adj f_sub g_sub
  -- So we have a cycle
  exact walk_plus_edge_has_cycle hT_tree.isAcyclic f_sub g_sub hT_adj walk_fg ...
```

---

## Next Steps

1. ✅ **Document the plan** (this file)
2. 🔄 **Build helper lemmas** one by one
3. 🔄 **Assemble main proof**
4. 🔄 **Repeat for other 3 sorries**

**Estimated Time**: 4-6 hours total for all 4 proofs

---

## Alternative: Simpler Approach?

Could we avoid the Walk conversion by using the dichotomy directly?

**Observation**: The SpanningForest dichotomy says:
- For tree edge `e`: `e ∈ tree_edges` ∨ (path exists without `e`)
- But this is inclusive OR, not exclusive

**Issue**: Dichotomy doesn't directly say "no path without e for tree edges"

**Conclusion**: We DO need the tree structure to prove bridges properly.

---

## Files to Modify

1. `FourColor/Geometry/DualForest.lean` - Add helper lemmas, fill sorries
2. `how-to-lean.md` - Document Walk/ReflTransGen conversion patterns

---

**Status**: Plan documented, ready to implement helpers systematically
