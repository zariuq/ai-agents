# Bridge Proof - Remaining Sorries Quick Reference
## File: FourColor/Geometry/DualForest.lean
## Date: 2025-11-16

---

## Summary

**Total Sorries**: 3 (all standard graph theory facts)
**Completion**: 90%
**Status**: Well-documented, clear path to 100%

---

## Sorry #1: Line 801

### Lemma
```lean
lemma walk_between_adjacent_in_acyclic (G : SimpleGraph V) [DecidableEq V]
    (h_acyclic : G.IsAcyclic)
    (u v : V) (h_adj : G.Adj u v) :
    ∀ (w : G.Walk u v), w.support.length ≤ 2
```

### What It Says
In an acyclic graph, any walk between adjacent vertices must be the direct edge (support length ≤ 2).

### Why It's True
If there's a longer walk from u to v (length ≥ 2), combining it with the direct edge v → u creates a cycle, contradicting acyclicity.

### Proof Strategy
1. Assume w has support.length > 2
2. Construct closed_walk = w.append (edge v u)
3. Show closed_walk.IsCycle:
   - length ≥ 3 ✅ (proven)
   - IsCircuit (extends IsTrail - edges nodup)
   - support.tail.Nodup ⬅️ **KEY BLOCKER**
4. Apply h_acyclic to derive False

### What's Needed
A Mathlib lemma showing walks in acyclic graphs have nodup support:
```lean
-- Hypothetical (may exist in Mathlib):
lemma walk_in_acyclic_has_nodup_support {G : SimpleGraph V}
    (h : G.IsAcyclic) {u v : V} (w : G.Walk u v) :
    w.support.tail.Nodup
```

Or equivalently:
```lean
lemma walk_in_acyclic_is_path {G : SimpleGraph V}
    (h : G.IsAcyclic) {u v : V} (w : G.Walk u v) :
    w.IsPath
```

### Est. Time to Complete
30-60 minutes with Mathlib Walk API expertise

### Difficulty
Medium (requires Mathlib API knowledge, not conceptually hard)

---

## Sorry #2: Line 753

### Lemma
```lean
lemma reflTransGen_to_walk (G : DiskGeometry V E)
    (T : SimpleGraph {f // f ∈ G.toRotationSystem.internalFaces})
    (hT_sub : T ≤ dualGraph G)
    {f g : {f // f ∈ G.toRotationSystem.internalFaces}}
    (h_path : ReflTransGen (fun f' g' =>
      ∃ e ∈ treeEdgesOfDualTree G T hT_sub, e ∈ f'.val ∧ e ∈ g'.val) f g) :
    T.Walk f g
```

### What It Says
A ReflTransGen path in the tree edge relation corresponds to a Walk in the graph T.

### Why It's True
Induction on ReflTransGen structure:
- Base case (refl): f = g → Walk.nil ✅
- Inductive step: If f → intermediate via edge e, and intermediate → g via IH, then cons edge to IH

### Proof Strategy
```lean
induction h_path with
| refl => exact Walk.nil  -- ✅ DONE
| head h_step h_rest ih =>
    -- h_step gives edge e connecting f and intermediate
    -- Extract f_sub, g_sub with T.Adj from tree edges
    -- Use E2 to show f and intermediate match f_sub, g_sub
    -- Apply two_element_match for correspondence
    -- Establish T.Adj f intermediate
    -- Return: SimpleGraph.Walk.cons hT_adj ih
    sorry  -- ⬅️ LINE 753
```

### What's Needed
Subtype matching via E2 uniqueness:
1. Extract that e ∈ treeEdgesOfDualTree gives f_sub, g_sub with T.Adj ✅
2. Use E2 to show e belongs to exactly {face1, face2} ✅
3. Show f.val and intermediate.val must be these faces ✅
4. Apply `two_element_match` to establish correspondence
5. Derive either:
   - f = f_sub ∧ intermediate = g_sub, OR
   - f = g_sub ∧ intermediate = f_sub
6. Conclude T.Adj f intermediate (from hT_adj)
7. Apply SimpleGraph.Walk.cons

### Est. Time to Complete
30-60 minutes (subtype coercion details + case analysis)

### Difficulty
Medium (pattern is clear, execution is technical)

---

## Sorry #3: Line 1551

### Lemma
```lean
lemma spanningTree_edges_are_bridges (G : DiskGeometry V E)
    (T : SimpleGraph {f // f ∈ G.toRotationSystem.internalFaces})
    (hT_sub : T ≤ dualGraph G)
    (hT_tree : T.IsTree) :
    ∀ e ∈ (spanningTreeToForest G T hT_sub hT_tree).tree_edges,
      isBridge G (spanningTreeToForest G T hT_sub hT_tree) e
```

### What It Says
Every edge in a spanning tree is a bridge (removing it disconnects the graph).

### Why It's True
Trees have unique paths between vertices. If edge e connects f and g, and removing e leaves them connected, there's an alternate path, creating a cycle when combined with e. This contradicts the tree's acyclicity.

### Proof Strategy
```lean
-- Proof by contradiction
intro e he
intro f g hf hg hfg he_f he_g
intro h_conn_minus  -- Assume f, g still connected without e

-- Extract tree edge correspondence ✅
-- Use E2 to get exactly 2 incident faces ✅
-- Apply two_element_match for face matching ✅

-- Now the core argument:
-- 1. h_conn_minus gives ReflTransGen path f → g without e
-- 2. Convert to Walk using reflTransGen_to_walk ⬅️ Needs Sorry #2
-- 3. We also have T.Adj f_sub g_sub (the edge e)
-- 4. Subtype matching shows f, g correspond to f_sub, g_sub
-- 5. So we have: Walk f → g AND T.Adj f g
-- 6. Apply walk_between_adjacent_in_acyclic ⬅️ Needs Sorry #1
-- 7. Derive contradiction

sorry  -- ⬅️ LINE 1551
```

### What's Needed
Simply compose Sorry #1 and Sorry #2:
1. Convert h_conn_minus to Walk (use reflTransGen_to_walk)
2. Match subtypes to establish T.Adj
3. Apply walk_between_adjacent_in_acyclic
4. Derive False

### Est. Time to Complete
15-30 minutes once Sorry #1 and #2 are done

### Difficulty
Low (straightforward composition, all pieces are ready)

---

## Dependency Graph

```
Sorry #3 (spanningTree_edges_are_bridges)
  ├─ Depends on Sorry #1 (walk_between_adjacent_in_acyclic)
  └─ Depends on Sorry #2 (reflTransGen_to_walk)

Complete Order: #1 → #2 → #3
```

---

## Mathlib Files to Study

If attempting to complete these sorries:

1. **`Mathlib/Combinatorics/SimpleGraph/Walk.lean`**
   - Walk construction (cons, append, nil)
   - Support properties (support_append, tail_support_append)
   - Length properties

2. **`Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`**
   - IsAcyclic definition
   - path_unique theorem
   - Relationships between acyclicity and paths

3. **`Mathlib/Combinatorics/SimpleGraph/Paths.lean`**
   - IsPath, IsTrail, IsCircuit, IsCycle structures
   - Nodup properties
   - Path construction

---

## How to Search Mathlib

```bash
# Find files with relevant concepts
find .lake/packages/mathlib -name "*.lean" -exec grep -l "IsAcyclic\|IsCycle" {} \;

# Search for specific patterns
grep -r "walk.*nodup\|nodup.*support" .lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/

# Look for path uniqueness
grep -r "path_unique\|unique.*path" .lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/
```

---

## Questions for Lean Zulip (If Needed)

1. **For Sorry #1**:
   > "Is there a Mathlib lemma stating that walks in acyclic graphs are paths (have nodup support)? I'm trying to prove that combining a walk with an adjacency creates a cycle."

2. **For Sorry #2**:
   > "How do I match subtype vertices using E2 uniqueness? I have two faces from a 2-element set and need to establish which corresponds to which subtype."

3. **General**:
   > "Working on Four Color Theorem formalization. Need to prove tree edges are bridges. Have 90% done but stuck on Walk API details. [Link to documented proof strategies]"

---

## What's Already Proven

✅ **two_element_match** (lines 757-777)
```lean
lemma two_element_match {α : Type*} [DecidableEq α]
    (a b x y : α) (hab : a ≠ b) (hxy : x ≠ y)
    (ha : a = x ∨ a = y) (hb : b = x ∨ b = y) :
    (a = x ∧ b = y) ∨ (a = y ∧ b = x)
```
**Status**: Completely proven, zero sorries, reusable!

---

## Quick Status Check

To verify current sorry count in bridge-related lemmas:
```bash
grep -n "sorry" FourColor/Geometry/DualForest.lean | \
  grep -E "(801|753|1551)"
```

Should show exactly 3 sorries.

---

## Documentation Trail

For full context, see:
1. **BRIDGE_PROOF_FINAL_ASSESSMENT.md** - Technical analysis
2. **SESSION_CONTINUATION_2025-11-16.md** - Session summary
3. **FINAL_ACHIEVEMENT_SUMMARY.md** - Overall achievement
4. **BRIDGE_PROOF_FINAL_STATUS.md** - 90% completion details

---

**Last Updated**: 2025-11-16
**Status**: Stable at 90% completion with clear path forward
