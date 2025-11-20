# Bridge Proof Progress - Session 2025-11-16
## Goal: Prove spanningTree_edges_are_bridges without sorry

---

## Current Status: 70% Complete

### What's Been Built ✅

1. **Helper Lemma: two_element_match** (lines 740-762)
   - Proves that two distinct pairs from a 2-element set match up to symmetry
   - Fully proven, no sorries
   - Essential for identifying subtype vertices with faces via E2

2. **Main Proof Structure** (lines 1415-1505)
   - Set up contradiction: assume `treeConnectedMinus` holds
   - Extracted tree edge correspondence via `treeEdgesOfDualTree`
   - Used E2 to get the two faces containing edge `e`
   - Applied `two_element_match` to establish correspondence
   - Case split into 4 cases (reduces to 2 by symmetry)

3. **reflTransGen_to_walk skeleton** (lines 700-738)
   - Started building the reverse direction of `walk_to_reflTransGen`
   - Induction structure in place
   - Needs completion for final sorry discharge

---

## What Remains (4 sorries)

### In span

ningTree_edges_are_bridges:

1. **Line 1494**: Main case - f = f_sub.val, g = g_sub.val
   - Need to: Convert `h_conn_minus` to Walk using `reflTransGen_to_walk`
   - Then: Show Walk + T.Adj creates cycle
   - Use: `hT_tree.isAcyclic` for contradiction

2. **Lines 1497, 1502**: Symmetric cases - swapped assignment
   - Similar to case 1 but with T.Adj symmetry

3. **Line 1505**: Duplicate of case 1
   - Same proof as line 1494

### In reflTransGen_to_walk:

4. **Line 738**: Establish T.Adj and cons onto walk
   - Need to match faces with subtype vertices
   - Then use SimpleGraph.Walk.cons

---

## Key Insight

The proof has circular dependency:
- `spanningTree_edges_are_bridges` needs `reflTransGen_to_walk`
- `reflTransGen_to_walk` needs similar face-matching logic

**Resolution**: Complete `reflTransGen_to_walk` first, then use it in main proof.

---

## Next Steps

### Step 1: Complete reflTransGen_to_walk (30-60 min)

```lean
-- At line 738, need to show T.Adj f intermediate
-- We have: f_sub, g_sub with T.Adj f_sub g_sub and edge e connecting them
-- We have: f.val and intermediate.val contain e
-- By E2 + two_element_match: f = f_sub (or g_sub), intermediate = g_sub (or f_sub)
-- Therefore: T.Adj f intermediate (possibly after subtype coercion)
-- Then: SimpleGraph.Walk.cons hT_adj_matched ih
```

### Step 2: Use reflTransGen_to_walk in main proof (15-30 min)

```lean
-- At line 1494:
-- We have h_conn_minus : treeConnectedMinus G F e f g
-- This is ReflTransGen with e excluded
-- Convert to subtype witnesses:
let f_as_sub : {f // f ∈ ...} := ⟨f, hf⟩
let g_as_sub : {f // f ∈ ...} := ⟨g, hg⟩
-- Use reflTransGen_to_walk (with e excluded relation)
have walk_fg : T.Walk f_as_sub g_as_sub := ...
-- We also have T.Adj f_sub g_sub
-- Show f_as_sub = f_sub, g_as_sub = g_sub via hf1, hg2
-- Then walk_fg + T.Adj creates cycle
-- Contradiction with hT_tree.isAcyclic
```

### Step 3: Handle symmetric cases (15 min)

Use `T.Adj.symm` for swapped cases.

### Step 4: Test build (5 min)

`lake build FourColor.Geometry.DualForest`

---

## Estimated Time to Complete

- reflTransGen_to_walk: 30-60 min
- Main proof cases: 30-45 min
- Testing: 5-10 min

**Total**: 1-2 hours for full zero-sorry proof

---

## Blocker: Cycle Detection

Need a lemma stating: Walk + Adj edge = cycle (in acyclic graph = contradiction)

**Option A**: Use Mathlib's cycle detection
**Option B**: Prove directly:
```lean
lemma walk_plus_adj_contradicts_acyclic
    (T : SimpleGraph V) (h_acyclic : T.IsAcyclic)
    (u v : V) (h_adj : T.Adj u v)
    (walk : T.Walk u v) (h_nontrivial : walk.length > 0) :
    False := by
  -- walk.append (edge u v) creates a cycle
  -- But h_acyclic says no cycles
  sorry
```

This is the final piece needed.

---

## Current File State

- DualForest.lean: ~3100 lines
- New helpers added: ~50 lines
- Main proof: ~90 lines (with sorries)
- Net: Proof structure 70% complete

---

## Recommendation

Continue with completing `reflTransGen_to_walk`, then discharge all 4 sorries.

Alternatively: Accept this partial progress (good proof structure, clear remaining work documented) and move to other Section 4 lemmas, returning later.

---

**Progress**: Solid foundational work, clear path to completion identified! 🎯
