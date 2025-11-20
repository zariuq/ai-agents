# PathXORSum Errors Fixed - 2025-11-10

## Objective

Fix the 4 build errors related to `pathXORSum_path_independent` usage that were left over from the WellFormed refactoring.

---

## Summary

✅ **COMPLETE**: All pathXORSum-related build errors resolved

**Result**: `lake build FourColor.Tait` completes successfully with ZERO errors

---

## The Problem

### Build Errors

After the WellFormed refactoring, 4 errors remained:

```bash
error: FourColor/Tait.lean:847:12: Tactic `apply` failed: could not unify...
error: FourColor/Tait.lean:871:12: Tactic `apply` failed: could not unify...
error: FourColor/Tait.lean:901:12: Tactic `apply` failed: could not unify...
error: FourColor/Tait.lean:905:25: Tactic `rewrite` failed...
```

### Root Cause

The theorems `pathXORSum_path_independent` and `pathXORSum_concat` were missing the `[DecidableEq E]` type class constraint!

**Context where used**: `tait_reverse`
```lean
theorem tait_reverse {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]  -- ← Has DecidableEq E
```

**Theorems being called**:
```lean
theorem pathXORSum_path_independent
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]  -- ← Missing DecidableEq E!
```

Lean was trying to synthesize `DecidableEq E` from `(fun a b => propDecidable (a = b))` which caused unification failures.

---

## The Fix

### Added Missing Type Class Constraints

**File**: `FourColor/Tait.lean`

#### 1. `pathXORSum_concat` (line 730)

**Before**:
```lean
theorem pathXORSum_concat
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
```

**After**:
```lean
theorem pathXORSum_concat
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
```

#### 2. `pathXORSum_path_independent` (line 752)

**Before**:
```lean
theorem pathXORSum_path_independent
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
```

**After**:
```lean
theorem pathXORSum_path_independent
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
```

That's it! Just adding `[DecidableEq E]` to both theorem signatures.

---

## Build Status

### Before
```bash
$ lake build FourColor.Tait 2>&1 | grep "^error:"
error: FourColor/Tait.lean:847:12: Tactic `apply` failed
error: FourColor/Tait.lean:871:12: Tactic `apply` failed
error: FourColor/Tait.lean:901:12: Tactic `apply` failed
error: FourColor/Tait.lean:905:25: Tactic `rewrite` failed
error: Lean exited with code 1
error: build failed
```

### After
```bash
$ lake build FourColor.Tait 2>&1 | grep "^error:"
# (no output - ZERO errors!)

$ lake build FourColor.Tait 2>&1 | tail -1
Build completed successfully (7340 jobs).
```

✅ **Build succeeds!**

---

## Verification

### No axioms remain
```bash
$ grep "^axiom" FourColor/Tait.lean
# (no output - zero axioms!)
```

### Expected sorries remain (7 total)
```bash
$ lake build FourColor.Tait 2>&1 | grep "declaration uses 'sorry'"
warning: FourColor/Tait.lean:255:8: declaration uses 'sorry'  # twoColorUnion_is_even_cycles
warning: FourColor/Tait.lean:270:8: declaration uses 'sorry'  # parity_sum_cycle_zero
warning: FourColor/Tait.lean:355:8: declaration uses 'sorry'  # no_multi_edges
warning: FourColor/Tait.lean:422:8: declaration uses 'sorry'  # bridgeless_connected
warning: FourColor/Tait.lean:730:8: declaration uses 'sorry'  # pathXORSum_concat
warning: FourColor/Tait.lean:752:8: declaration uses 'sorry'  # pathXORSum_path_independent
warning: FourColor/Tait.lean:969:8: declaration uses 'sorry'  # four_color_equiv_tait
```

All 7 are expected - these are unproven theorems, not errors!

---

## What Was Wrong

### Type Class Inference Mismatch

When `tait_reverse` tried to call `pathXORSum_path_independent`:

1. **Caller context**: Has `[DecidableEq E]` as an instance
2. **Callee signature**: Missing `[DecidableEq E]`, so Lean tried to synthesize it
3. **Lean's synthesis**: Created `(fun a b => propDecidable (a = b))`
4. **Unification**: Failed because the synthesized instance didn't match the expected canonical form

### Why DecidableEq E Was Needed

The `pathXORSum` function uses `getEdgeBetween`, which needs to work with edge equality:
- Checking if `e ∈ incident u`
- Looking up edges in finite sets
- All require decidable equality on edges

Without `[DecidableEq E]` in the theorem signature, Lean had to synthesize it on the fly, causing type class resolution issues.

---

## Technical Details

### Error Message Anatomy

```
error: Tactic `apply` failed: could not unify the conclusion of `@pathXORSum_path_independent`
  @pathXORSum ?V ?E ?inst✝ ?inst✝¹ ?inst✝² (fun a b => propDecidable (a = b)) ...
                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
                                           This is Lean synthesizing DecidableEq!
with the goal
  @pathXORSum V E inst✝³ inst✝² inst✝¹ inst✝ ...
                                      ^^^^^^
                                      Expected the canonical instance here
```

The `(fun a b => propDecidable (a = b))` is Lean's way of saying "I'm making up a DecidableEq instance because you didn't provide one."

When it tries to unify with the goal (which expects the canonical `inst✝` from the context), it fails.

---

## Lessons Learned

### Type Class Hygiene

**Rule**: When a theorem calls functions that need decidability instances, the theorem must include those instances in its signature.

**Bad**:
```lean
theorem my_theorem {E : Type*} [Fintype E] : ... := by
  -- Uses functions requiring DecidableEq E
  -- Lean synthesizes ad-hoc instance → unification fails
```

**Good**:
```lean
theorem my_theorem {E : Type*} [Fintype E] [DecidableEq E] : ... := by
  -- Uses functions requiring DecidableEq E
  -- Uses canonical instance from context → works!
```

### Debugging Type Class Issues

When you see:
- `could not unify`
- `(fun a b => propDecidable (a = b))`
- Type class instance mismatches

**Check**: Are all the type class constraints in the theorem signature?

**Compare**: What constraints does the caller have? The callee should have at least those.

---

## Impact Assessment

### Changes Made
- 2 theorem signatures updated (added `[DecidableEq E]`)
- 0 proof changes needed
- 0 call site updates needed

### Errors Fixed
- ✅ 3 `apply` failures resolved
- ✅ 1 `rewrite` failure resolved
- ✅ Build now succeeds

### No Regressions
- All pre-existing sorries remain (as expected)
- No new warnings introduced
- Zero axioms maintained

---

## Relationship to Previous Work

### Session Timeline

1. **WellFormed Refactoring** (earlier today):
   - Eliminated `adj_iff_shared_edge` axiom
   - Threaded `WellFormed` through codebase
   - Left 4 errors related to pathXORSum

2. **IsBridgeless Fix** (30 min ago):
   - Fixed broken stub definition
   - Added proper bridgeless definition
   - Updated 7 call sites

3. **This Fix** (just now):
   - Fixed pathXORSum type class issues
   - Added missing `[DecidableEq E]` constraints
   - **Build now clean!**

---

## Metrics

**Theorems updated**: 2
**Lines changed**: 2 (one per theorem signature)
**Build errors fixed**: 4
**Build errors introduced**: 0
**Time**: ~5 minutes

---

## Final State

### Build Status: ✅ CLEAN

```bash
$ lake build FourColor.Tait
Build completed successfully (7340 jobs).
```

### Axioms: 0 ✅

```bash
$ grep "^axiom" FourColor/Tait.lean
# (no output)
```

### Sorries: 7 (all expected)

All are honest proof obligations for theorems that need to be proven:
1. `twoColorUnion_is_even_cycles` - two-color union structure
2. `parity_sum_cycle_zero` - cycle parity theorem
3. `no_multi_edges` - simple graph property
4. `bridgeless_connected` - connectivity from bridgeless
5. `pathXORSum_concat` - path concatenation property
6. `pathXORSum_path_independent` - path independence from parity
7. `four_color_equiv_tait` - the main equivalence (needs full infrastructure)

---

## Conclusion

✅ **All pathXORSum-related build errors resolved!**

The fix was simple but subtle - just adding the missing `[DecidableEq E]` type class constraint to two theorem signatures. This allowed Lean's type class resolution to use the canonical instance from the caller's context instead of synthesizing ad-hoc instances that didn't unify.

**Result**: Clean build, zero axioms, honest sorries marking proof obligations.

---

**Fix completed**: 2025-11-10
**Duration**: ~5 minutes
**Status**: ✅ SUCCESS - Build clean, all errors resolved
**Philosophy**: Get your type class constraints right up front!
