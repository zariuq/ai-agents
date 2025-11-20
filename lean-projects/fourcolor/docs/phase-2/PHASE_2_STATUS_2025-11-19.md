# Phase 2 Status: SpanningForest.lean - 2025-11-19

## Mission
Complete SpanningForest.lean: eliminate all sorries

## Current Status

**Total sorries**: 2 (down from original 3-4)

### Sorry #1: `path_must_use_new_edge` (line 59)
**Status**: ⚠️ Induction pattern issue
**Problem**: ReflTransGen induction with intermediate variable naming
**Attempts**:
- Tried `@tail _ _ z _` pattern → too many variables error
- Tried `rename_i c` → type mismatch (R b✝ c vs R c b)
- Tried default pattern `| tail hab hbc ih` → unknown identifier errors

**TODO**: Either:
(a) Find correct Lean 4 induction pattern for ReflTransGen with explicit intermediate node
(b) Use mathlib helper lemma if available
(c) Accept as documented sorry for now

### Sorry #2: `fundamental_cycle_property` Case 2 (line 259, previously 244)
**Status**: ✅ Proof exists, ⚠️ Termination checker blocks it
**Problem**: Recursive call not recognized as terminating by Lean
**Solution found**: Complete proof exists in `fundamental_cycle_for_new_edge` (lines 360-434)

**Why it works**:
- Case 2 recursively calls `fundamental_cycle_property` with different witness
- Recursive call forces Case 1 (e_witness → e), avoiding infinite recursion
- E2 uniqueness + 4 symmetric subcases complete the proof

**Why Lean rejects it**:
- Termination not structurally obvious (witness edge parameter changes)
- Would need well-founded recursion proof

**TODO**: Either:
(a) Add termination proof using well-founded recursion
(b) Refactor to inline `fundamental_cycle_for_new_edge`'s proof directly
(c) Accept as documented sorry (references complete proof in line 380)

### Archived: `first_occurrence_of_e` (line 127)
**Status**: ✅ Archived in comment block
**Reason**: Fundamentally broken lemma (path condition excludes the edge being searched for)

## Progress Made

✅ **Case 1 complete** (`fundamental_cycle_property`, lines 183-242)
- Clean proof using E2 uniqueness
- Path transformation to tree_edges only
- All 4 symmetric subcases handled

✅ **Complete reference proof exists** (`fundamental_cycle_for_new_edge`, lines 301-434)
- Shows both cases are provable
- Case 2 implemented successfully (but can't be copied due to termination)

✅ **Clean code invariants maintained**:
- Zero errors (sorries documented, not blocking)
- All used lemmas proven or documented
- Architecture: isAcyclic → fundamental_cycle_property → exists_maximal_acyclic → SpanningForest

## Build Status

```bash
export LAKE_JOBS=3 && lake build FourColor.Geometry.SpanningForest
```

**Result**:
- 2 sorry warnings (expected)
- 0 errors
- Rest of file compiles successfully

## Recommendations

### Option A: Accept Current State
- Document the 2 sorries as "implementation details"
- Both have clear proof strategies
- Focus energy on downstream theorems

### Option B: Pair Program with Expert
- Get help with ReflTransGen induction patterns
- Learn Lean 4 termination proof techniques
- 1-2 hour session could eliminate both sorries

### Option C: Use path_must_use_new_edge differently
- Check if the lemma is actually needed
- Maybe the proof can be restructured to avoid it

## Files Modified

- `FourColor/Geometry/SpanningForest.lean`:
  - Attempted `path_must_use_new_edge` induction (reverted to sorry)
  - Filled `fundamental_cycle_property` Case 2 (blocked by termination, reverted to documented sorry)
  - Archived `first_occurrence_of_e` as commented-out broken code

## Next Steps

**If continuing Phase 2**:
1. Research Lean 4 ReflTransGen induction patterns in mathlib
2. Check for `head_induction_on` or similar helper lemmas
3. Try `cases` instead of `induction` for the ReflTransGen proof

**If moving to Phase 3**:
- Accept 2 documented sorries
- Proceed to next module in cleanup plan
- Return to these with fresh perspective or expert help

---

**Session time**: ~2 hours
**Net progress**: 3-4 sorries → 2 well-documented sorries + 1 archived
**Key learning**: Lean 4 termination checker is strict; recursive proofs need explicit well-founded measures
