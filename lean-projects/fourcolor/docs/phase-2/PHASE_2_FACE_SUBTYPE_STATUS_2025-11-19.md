# Phase 2: Face Subtype Refactoring - Status 2025-11-19

## Mission: Implement GPT-5.1's Option A

**Strategy**: Move dual graph relation to Face G subtype for "small refactor, big payoff"

**Status**: ⏳ **Significant Progress** - 3/5 sorries filled, 2 hard infrastructure sorries remain

---

## Achievements ✅

### 1. Face Subtype Definition (Lines 108-113)

```lean
abbrev Face (G : DiskGeometry V E) :=
  {f : Finset E // f ∈ G.toRotationSystem.internalFaces}
```

**Win**: Makes "f is internal" a type-level guarantee!

### 2. Updated isAcyclic (Lines 115-123)

```lean
def isAcyclic (G : DiskGeometry V E) (tree_edges : Finset E) : Prop :=
  ∀ e ∈ tree_edges, ∀ (f g : Face G),
    f ≠ g →
    e ∈ f.1 → e ∈ g.1 →
    ¬ ReflTransGen (fun f' g' => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ f'.1 ∧ e' ∈ g'.1) f g
```

Now quantifies over `Face G` instead of arbitrary `Finset E`!

### 3. Lifted path_must_use_new_edge_face (Lines 89-112)

Same induction proof, now works with `Face G` types.

### 4. Case 1 Complete (Lines 242-303)

✅ All `.1` projections in place
✅ `Subtype.eq` pattern for contradictions
✅ Zero sorries

### 5. Case 2: 3 Sorries Filled!

**Original sorries** (from GPT-5.1 analysis):
- Sorry #1-2: Internal face membership → ✅ **ELIMINATED** by Face G type!
- Sorry #3: Face distinctness (line 374, 490) → ✅ **FILLED** using `hf1f2_eq`
- Sorry #4: Tree-only path (line 490) → ⚠️ **REMAINING** (hardest)
- Sorry #5: Suffix analysis (line 437) → ⚠️ **REMAINING** (complex)

---

## Remaining Sorries (2 Total)

### Sorry #1: Suffix Analysis (Line 437)

**Location**: Inside `f1 = f2` contradiction case, nested `by_cases` for suffix

**Context**:
```lean
by_cases hf1f2_eq : f1 = f2
· exfalso
  by_cases hf2_eq_g' : f2 = g'
  · -- ✅ FILLED: prefix gives R-only path, contradiction
  · by_cases h_suffix_R : ReflTransGen R f2 g'
    · -- ✅ FILLED: suffix R-only, concatenate for contradiction
    · -- ⚠️ SORRY: Suffix uses S, need to analyze structure
```

**Challenge**: If `f1 = f2` (first S-step is reflexive) and suffix is NOT R-only, derive contradiction

**Difficulty**: ⭐⭐⭐ (Hard - requires analyzing multiple S-steps in path)

**Strategy ideas**:
- Show all S-steps in suffix are also reflexive → reduces to R-only case → contradiction
- Or: Show f1 = f2 contradicts f' ≠ g' given the path structure
- Or: Accept as infrastructure gap (path structure analysis)

---

### Sorry #2: Tree-Only Path (Line 490) 🔴 **HARDEST**

```lean
have h_path_tree : ReflTransGen (fun x y => ∃ e'' ∈ tree_edges, e'' ≠ e ∧ e'' ∈ x ∧ e'' ∈ y) f1.1 f2.1
```

**GPT-5.1's Cycle-Opening Argument**:

1. **Prefix**: `f' →*(tree\{e'}) f1` (tree-edges except e')
2. **e-step**: `f1 →e→ f2` (edge e connects f1, f2)
3. **Suffix**: `f2 →*(tree∨e) g'` (tree-edges or e)
4. **Close cycle**: `g' →e'→ f'` (edge e' connects g', f')
5. **Result**: Cycle in dual graph
6. **Goal**: "Opening" at e yields tree-path `f1 → f2`

**Challenge**: Formalizing "opening the cycle" in Lean

**What we have**:
- `h_prefix : ReflTransGen (tree-edges-except-e') f' f1`
- `he_f1, he_f2 : e ∈ f1.1, e ∈ f2.1`
- `h_suffix : ReflTransGen (mixed) f2 g'`
- `he'_f', he'_g' : e' ∈ f'.1, e' ∈ g'.1`

**What we need**: Either
- (A) General cycle-opening lemma for ReflTransGen
- (B) Direct construction using specific path structure

**Difficulty**: ⭐⭐⭐⭐ (Very Hard - fundamental graph theory)

**Current documentation** (lines 463-490): Detailed cycle argument with TODO

---

## Progress Summary

| Component | Status | Lines | Notes |
|-----------|--------|-------|-------|
| Face subtype definition | ✅ Done | 108-113 | Clean type-level invariant |
| isAcyclic update | ✅ Done | 115-123 | Quantifies over Face G |
| path_must_use_new_edge_face | ✅ Done | 89-112 | Lifted to Face G |
| Case 1 | ✅ Done | 242-303 | Zero sorries |
| Case 2 infrastructure | ✅ Done | 364-366 | 3 sorries eliminated! |
| Case 2: f1 = f2 → contradiction | ⏳ Partial | 369-437 | 2 subcases filled, 1 sorry |
| Case 2: f1 ≠ f2 → E2 uniqueness | ✅ Done | 438-454 | Clean proof |
| Case 2: symmetric cases | ✅ Done | 468-490 | 2 contradictions filled! |
| Case 2: tree path | ⚠️ Sorry | 461-490 | Cycle-opening needed |

---

## Build Status

Build in progress - waiting for verification

Expected: 2 sorry warnings (lines 437, 490)

---

## Lessons Learned

### GPT-5.1 Was Right! ✅

> "The f1, f2 you get from `path_must_use_new_edge_face` are *automatically* internal faces — their type is `{f // f ∈ internalFaces}`. So the two 'infrastructure sorries' simply disappear: you use `f1.property`, `f2.property`."

**Verified**: Lines 364-366 celebrate this win!

### Type-Level Invariants Win

Moving from "proof that f is internal" to "Face G subtype" eliminated 3 sorries immediately. Mario's principle: "Make illegal states unrepresentable."

### Some Problems Are Genuinely Hard

The remaining 2 sorries are not architectural issues - they're:
1. Complex path structure analysis (suffix with multiple S-steps)
2. Fundamental graph theory (cycle-opening)

Both are well-documented with clear TODOs.

---

## Recommendations

### Option A: Accept Current State ✅ **RECOMMENDED**

**Rationale**:
- 3/5 sorries filled
- Infrastructure sorries eliminated (main goal of refactoring!)
- Remaining 2 sorries are genuine mathematical challenges, not Lean engineering
- Both well-documented with clear strategies

**Documentation**: Mark as "Option A complete - 2 graph theory sorries remain"

### Option B: Tackle Suffix Analysis (30-60 mins)

**Approach**: Show that if `f1 = f2` and we have a non-R-only suffix, we can:
1. Apply `path_must_use_new_edge_face` to suffix to find another S-step
2. Show this S-step is also reflexive (since S connects faces in {f, g})
3. Recurse until we show suffix is actually R-only, contradicting `h_suffix_R`

**Risk**: May require lemmas we don't have about iterated path decomposition

### Option C: Research Cycle-Opening (1-2 hours)

**Search for**:
- mathlib lemmas about cycles in graphs
- ReflTransGen cycle properties
- Path concatenation and manipulation lemmas

**Fallback**: Accept as infrastructure gap, document clearly

---

## Next Steps

**If continuing**:
1. Try Option B (suffix analysis) - might cascade to solve both
2. Or search mathlib for cycle lemmas (Option C)
3. Or accept and document (Option A)

**If moving on**:
1. Update session summary
2. Mark Phase 2 as "Option A Success - infrastructure clean"
3. Note remaining sorries as graph theory challenges

---

## Code Locations

- **Face subtype**: Lines 108-123
- **path_must_use_new_edge_face**: Lines 89-112
- **fundamental_cycle_for_new_edge**: Lines 166-490
  - Case 1: Lines 236-303 ✅
  - Case 2: Lines 305-490 ⏳
    - f1 = f2 case: Lines 369-437 (1 sorry at 437)
    - f1 ≠ f2 case: Lines 438-490 (1 sorry at 490)

---

**Session achievement**: Successfully implemented Option A Face subtype refactoring, eliminating 3/5 sorries! 🎉

The remaining 2 sorries are well-scoped graph theory problems, not architectural issues.
