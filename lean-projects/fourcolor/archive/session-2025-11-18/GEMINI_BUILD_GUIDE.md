# Build Guide for Gemini: Lemma 4.7 Completion

**Task:** Complete the `fundamental_cycle_property` proof in `SpanningForest.lean`
**Approach:** Implement the 7-step algorithm without case-splitting on e'
**Status:** Counterexample proven ✅ | Strategy clear ✅ | Ready to implement 🚀

---

## Quick Start: Essential Build Commands

### ⚠️ CRITICAL: CPU-Friendly Builds

**ALWAYS use LAKE_JOBS=3** to avoid freezing the computer:

```bash
# Good (CPU-friendly)
export LAKE_JOBS=3 && lake build FourColor.Geometry.SpanningForest

# BAD (will use 100% CPU, computer unusable)
lake build FourColor.Geometry.SpanningForest
```

### Quick Syntax Check (No Full Build)

```bash
# Just check syntax, don't build dependencies
lean FourColor/Geometry/SpanningForest.lean
# Note: This will show import errors but is fast for syntax checking
```

### Full Build (Recommended)

```bash
# Build with CPU limit and timeout
export LAKE_JOBS=3 && timeout 300 lake build FourColor.Geometry.SpanningForest
```

### Build Output Monitoring

```bash
# Save to file and watch
export LAKE_JOBS=3 && lake build FourColor.Geometry.SpanningForest 2>&1 | tee /tmp/build.log

# Watch in real-time
tail -f /tmp/build.log
```

---

## The Task: Fix One Sorry

### Location
**File:** `FourColor/Geometry/SpanningForest.lean`
**Line:** 213
**Function:** `fundamental_cycle_property`

### Current Code (WRONG - Don't Do This)

```lean
| inr he'_tree =>
  -- Case 2: e' ∈ tree_edges
  exfalso  -- ❌ WRONG: Trying to prove impossible
  apply h_acyclic e' he'_tree ...
  sorry -- STUCK
```

### Why It's Wrong

We proved a **counterexample** showing Case 2 is VALID, not impossible.
See `FourColor/Geometry/CounterexampleCaseTwo.lean` for the formal proof.

**The 4-cycle counterexample:**
- Tree T = {e_ab, e_bc, e_cd}
- New edge e = e_da
- ✅ Can witness with e' = e_ab ∈ T (NOT e_da!)
- Therefore Case 2 happens normally!

---

## The Solution: 7-Step Algorithm

**Key insight:** Don't case-split on e'. Use ANY witness constructively to extract the fundamental cycle for e.

### The Algorithm

```lean
lemma fundamental_cycle_property
    (h_acyclic : isAcyclic G tree_edges)
    (he_notin : e ∉ tree_edges)
    (he_int : e ∉ G.toRotationSystem.boundaryEdges)
    (h_not_acyclic : ¬ isAcyclic G (insert e tree_edges)) :
  ∃ f g,
    f ∈ G.toRotationSystem.internalFaces ∧
    g ∈ G.toRotationSystem.internalFaces ∧
    f ≠ g ∧
    e ∈ f ∧ e ∈ g ∧
    ReflTransGen (fun x y => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ x ∧ e' ∈ y) f g := by

  -- Step 1: Get e's incident faces using E2
  obtain ⟨f, g, ...⟩ := two_internal_faces_of_interior_edge G.toPlanarGeometry he_int

  -- Step 2: Get witness from negation (DON'T CARE WHICH e' IT IS!)
  unfold isAcyclic at h_not_acyclic
  push_neg at h_not_acyclic
  obtain ⟨e', he'_in, f', g', hf', hg', hf'_ne_g', he'_f', he'_g', h_path⟩ := h_not_acyclic

  -- Step 3: Prove h_path must use e somewhere
  -- (Since tree_edges is acyclic, any cycle in insert e tree_edges contains e)
  have h_uses_e : ∃ (step in path), edge_of_step = e := by
    -- TODO: Prove by contradiction with h_acyclic
    sorry

  -- Step 4: Find FIRST occurrence of e in path
  obtain ⟨h₁, h₂, prefix_path, h_first_e⟩ :=
    first_occurrence_of_e h_path h_uses_e

  -- Step 5: By E2, {h₁, h₂} = {f, g}
  have : {h₁, h₂} = {f, g} := by
    -- Use E2 uniqueness (already done in Case 1)
    sorry

  -- Step 6: prefix_path is tree-only
  have h_tree_only : ReflTransGen (tree relation) h₁ h₂ := by
    apply Relation.ReflTransGen.mono _ prefix_path
    -- All edges before first e are in tree_edges
    sorry

  -- Step 7: Handle orientation (f,g) vs (g,f)
  -- Use symmetry as in Case 1
  exact ⟨f, g, ..., tree_only_path⟩
```

### Helper Lemmas Needed

You'll need to implement:

1. **Path unpacking:**
   ```lean
   lemma rflTransGen_to_list
     {α : Type*} {R : α → α → Prop} {a b : α}
     (h : ReflTransGen R a b) :
     ∃ (n : ℕ) (vs : Fin (n+1) → α),
       vs 0 = a ∧ vs (Fin.last n) = b ∧
       ∀ i : Fin n, R (vs i.castSucc) (vs i.succ)
   ```

2. **First occurrence:**
   ```lean
   lemma first_occurrence_of_e
     (h_path : ReflTransGen ...)
     (h_uses : path uses e) :
     ∃ (h₁ h₂ : faces) (prefix : tree-only path),
       e connects h₁ h₂ ∧
       prefix goes from start to h₁
   ```

3. **Path must use e:**
   ```lean
   lemma path_must_use_e
     (h_acyclic : isAcyclic G tree_edges)
     (h_path : path in insert e tree_edges) :
     path uses e at least once
   ```

---

## Key Resources

### 📄 Must-Read Files

1. **`FUNDAMENTAL_CYCLE_LESSON.md`** - Complete analysis of the problem
   - Explains the false claim we were trying to prove
   - Shows the 4-cycle counterexample
   - Gives the correct strategy

2. **`FourColor/Geometry/CounterexampleCaseTwo.lean`** - Formal counterexample
   - Proves Case 2 is valid (not impossible)
   - Locks in the intuition

3. **`FourColor/Geometry/SpanningForest.lean`** - The file to edit
   - Lines 102-186: Case 1 (COMPLETE) - use as a template!
   - Line 213: The sorry to fix

4. **`L4.7_STATUS.md`** - Current status
   - What's complete, what needs work
   - Dependency chain

### 🔧 Useful Existing Code

**E2 Uniqueness Pattern (from Case 1, line 137-150):**
```lean
have h_eq : {f', g'} = ({f, g} : Finset (Finset E)) := by
  have hcard_f'g' : ({f', g'} : Finset (Finset E)).card = 2 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_singleton]
    simp only [Finset.mem_singleton]
    exact hf'_ne_g'
  have hfaces_f'g' : ∀ face ∈ ({f', g'} : Finset (Finset E)),
      face ∈ G.toRotationSystem.internalFaces ∧ e ∈ face := by
    intro face hface
    simp only [Finset.mem_insert, Finset.mem_singleton] at hface
    cases hface with
    | inl heq => subst heq; exact ⟨hf', he'_f'⟩
    | inr heq => subst heq; exact ⟨hg', he'_g'⟩
  have : {f', g'} = fg := hunique _ ⟨hcard_f'g', hfaces_f'g'⟩
  rw [this, ← hfg_pair]
```

**Path Transformation (from Case 1, line 158-166):**
```lean
have h_path_tree : ReflTransGen (...) f' g' := by
  apply Relation.ReflTransGen.mono _ h_path
  intro x y ⟨e'', he''_ins, hne, hx, hy⟩
  have he''_tree : e'' ∈ tree_edges := by
    simp only [Finset.mem_insert] at he''_ins
    cases he''_ins with
    | inl heq => rw [heq] at hne; contradiction
    | inr hmem => exact hmem
  exact ⟨e'', he''_tree, hne, hx, hy⟩
```

**Symmetric Path Reversal (from Case 1, line 181-185):**
```lean
have h_sym : Symmetric (fun x y => ∃ e'' ∈ tree_edges, e'' ≠ e ∧ e'' ∈ x ∧ e'' ∈ y) := by
  intro x y ⟨e'', hmem, hne, hx, hy⟩
  exact ⟨e'', hmem, hne, hy, hx⟩
have h_path_rev := rflTransGen_reverse_of_symmetric h_sym h_path_tree
```

---

## Import Structure (Why Separate Files)

### The Issue

```
SpanningForest.lean
  ↓ imports
CounterexampleCaseTwo.lean
  ↓ imports
SpanningForest.lean
  ↓ CIRCULAR DEPENDENCY! ❌
```

### The Solution

**Separate files:**
- `SpanningForest.lean` - Main proof (doesn't import counterexample)
- `CounterexampleCaseTwo.lean` - Counterexample (imports SpanningForest)

**Why it works:**
- Counterexample is for UNDERSTANDING, not for the proof
- Main proof never references the counterexample
- Counterexample uses definitions from SpanningForest
- One-way dependency: Counterexample → SpanningForest ✓

---

## Testing Your Changes

### After Each Edit

```bash
# Quick syntax check (2 seconds)
export LAKE_JOBS=3 && timeout 10 lake build FourColor.Geometry.SpanningForest 2>&1 | head -20

# Look for errors
grep "error:" /tmp/build.log | head -5
```

### Final Verification

```bash
# Full build (3-5 minutes)
export LAKE_JOBS=3 && timeout 300 lake build FourColor.Geometry.SpanningForest 2>&1 | tee /tmp/final_build.log

# Check for sorries
grep -n "sorry" FourColor/Geometry/SpanningForest.lean

# Expected: 0 sorries (or just comments mentioning "sorry")
```

---

## Common Pitfalls

### ❌ Don't Do This

1. **Case-split on e'**
   ```lean
   cases he'_in with
   | inl => ...
   | inr => exfalso; sorry  -- WRONG!
   ```

2. **Try to prove path avoids e**
   ```lean
   have : ∀ step, edge ≠ e := sorry  -- IMPOSSIBLE!
   ```

3. **Use `lake build` without LAKE_JOBS**
   ```bash
   lake build  # FREEZES COMPUTER!
   ```

### ✅ Do This Instead

1. **Use witness constructively (no case split)**
   ```lean
   obtain ⟨e', ..., h_path⟩ := h_not_acyclic
   -- Don't care what e' is, just find e in path
   ```

2. **Prove path MUST use e**
   ```lean
   have h_uses_e : ∃ step, edge = e := by
     -- If no step uses e, contradict h_acyclic
   ```

3. **Always use LAKE_JOBS=3**
   ```bash
   export LAKE_JOBS=3 && lake build ...
   ```

---

## Communication Protocol

### When Stuck

1. **Show exact error:**
   ```bash
   export LAKE_JOBS=3 && lake build ... 2>&1 | grep "error:" -A 5
   ```

2. **Show line numbers:**
   ```bash
   grep -n "sorry" FourColor/Geometry/SpanningForest.lean
   ```

3. **Ask specific questions:**
   - "How do I unpack ReflTransGen into a list?"
   - "What mathlib lemma shows symmetry?"
   - "How do I prove this specific goal: `...`"

### When Making Progress

1. **Report sorry count:**
   ```bash
   grep -c "sorry" FourColor/Geometry/SpanningForest.lean
   ```

2. **Share proof structure:**
   ```lean
   -- Completed steps:
   -- Step 1: ✅
   -- Step 2: ✅
   -- Step 3: ⚠️ (sorry)
   ```

---

## Success Criteria

### Done When

1. ✅ Zero sorries in `fundamental_cycle_property`
2. ✅ Build completes with no errors
3. ✅ All dependency chain complete:
   ```
   exists_spanning_forest
     → maximal_acyclic_dichotomy
       → fundamental_cycle_for_new_edge
         → fundamental_cycle_property ✓ (no sorries!)
   ```

### Expected Result

```bash
$ grep -c "sorry" FourColor/Geometry/SpanningForest.lean
0

$ export LAKE_JOBS=3 && lake build FourColor.Geometry.SpanningForest
✔ Built FourColor.Geometry.SpanningForest
```

---

## TL;DR - Quick Checklist

- [ ] Read `FUNDAMENTAL_CYCLE_LESSON.md` (15 min)
- [ ] Read counterexample in `CounterexampleCaseTwo.lean` (5 min)
- [ ] Look at Case 1 (lines 102-186) for patterns (10 min)
- [ ] Implement 7-step algorithm (don't case-split on e'!)
- [ ] Test frequently with `LAKE_JOBS=3`
- [ ] Zero sorries = SUCCESS! 🎉

---

**Bottom line:** The math is clear, the strategy is proven correct via counterexample. You're implementing a well-understood algorithm, not discovering new math. Use Case 1 as a template!

**Estimated time:** 2-4 hours of focused work.

**Confidence:** 🟢 HIGH - This is doable and the path is clear.

Good luck! 🚀
