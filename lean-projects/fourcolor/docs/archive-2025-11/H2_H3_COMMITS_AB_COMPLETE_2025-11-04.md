# H2→H3 Wiring: Commits A & B Complete! 🎉

**Date**: 2025-11-04
**Session**: H2→H3 Integration (following Oruži's guidance)
**Achievement**: Completed 2 of 4 local H3 sorries

---

## Status Summary

### ✅ Commit A: `support₁_add_toggles_singleton` (COMPLETE)

**Location**: `FourColor/Geometry/Disk.lean:452-481`
**Purpose**: Z₂ singleton toggle lemma for support₁
**Status**: Fully proven, 0 sorries

**Implementation**: Pure Z₂ case-split proof
- Case e = e₀: Use `zmod2_ne_zero_iff_eq_one` to show y toggles
- Case e ≠ e₀: y contributes 0, so x is unchanged
- Result: `support₁ (x + y) = (support₁ x \ {e₀}) ∪ ({e₀} \ support₁ x)`

**Key technical detail**: Had to work around `fin_cases` unavailability by using explicit Z₂ dichotomy with `zmod2_ne_zero_iff_eq_one`.

### ✅ Commit B: Boundary Case Fix (COMPLETE)

**Location**: `FourColor/Geometry/Disk.lean:628-653`
**Purpose**: Show toggleSum is zero on boundary edges
**Status**: Fully proven, 0 sorries

**Implementation**: Internal faces disjoint from boundary
- Use `internal_face_disjoint_boundary` to show e ∉ f for all f ∈ S₀
- Pointwise zero → sum is zero
- Contradiction with h : (toggleSum e).fst ≠ 0

**Key property used**: `internal_face_disjoint_boundary` (already in RotationSystem)

---

## What Was Accomplished

### Commit A Technical Details

**Line count**: ~29 lines
**Dependencies**: Only `zmod2_ne_zero_iff_eq_one` (already in file)
**Proof structure**:
```lean
by_cases h : e = e₀
· -- At e₀: fst toggles in Z₂
  have hy_eq_1 : (y e).fst = 1
  have toggle_iff : (x e).fst + 1 ≠ 0 ↔ (x e).fst = 0
  have z2_iff : (x e).fst = 0 ↔ ¬(x e).fst = 1
  simp [support₁, toggle_iff, z2_iff]
· -- Off e₀: fst is unchanged
  have h0 : (y e).fst = 0
  simp [support₁, h0, h]
```

**Tricky part**: After `subst h`, the variable `e₀` disappears, so we use `e` instead throughout the proof.

### Commit B Technical Details

**Line count**: ~25 lines
**Dependencies**: `internal_face_disjoint_boundary` (RotationSystem)
**Proof structure**:
```lean
have hzero : (toggleSum G (1,0) S₀ e).fst = 0 := by
  -- every internal face avoids boundary edges
  have hpoint : ∀ f ∈ S₀, e ∉ f := ...
  -- pointwise zero
  have : ∀ f ∈ S₀, (faceBoundaryChain (1,0) f e).fst = 0 := by
    intro f hf
    have he_not_in_f := hpoint f hf
    by_cases he' : e ∈ f
    · exfalso; exact he_not_in_f he'
    · simp [he']
  -- sum of zeros is zero
  apply Finset.sum_eq_zero
-- contradiction
exact absurd hzero h
```

**Tricky part**: The `by_cases` needed explicit `exfalso` in the positive case since we know e ∉ f.

---

## Impact

### H3 Non-Support-Aware Descent (Almost Complete)

With Commits A and B, the lemma `aggregated_toggle_strict_descent_at_prescribed_cut` (line 616) is **99% complete**. Only needs:
- H2 to provide `S₀` with `cutEdges G S₀ = {e0}`
- Then it's fully automatic!

The proof flow:
1. ✅ toggleSum flips only e0 (boundary case now proven)
2. ✅ support₁_add_toggles_singleton applies
3. ✅ Strict cardinality drop by 1

### H3₁ Support-Aware Descent

Similar status: needs H2-support to provide `S₀` with `cutEdges₁ G x S₀ = {e0}`.

---

## Next Steps

### Commit C: H2-Support Implementation (In Progress)

**Skeleton provided by Oruži** (Section 4 of guidance doc)
**Location**: Line 547 (fill the sorry)
**Needs**: 3 small local lemmas (~5-10 lines each)

1. `hS₀_touch`: Induction on `ReflTransGen` showing faces touch support
2. `huniq_e0`: e0 has exactly one incident face in S₀
3. `hno_other_support_cuts`: Other support edges aren't cuts

**Construction approach**: Component-after-delete restricted to support edges
- Use `adjOnSupportExcept x e0` (already defined!)
- Build `S₀` as `ReflTransGen` closure from seed face
- Prove `cutEdges₁ G x S₀ = {e0}`

### Commit D: H3₁ Wiring

Once C is complete:
- Get `S₀` with `cutEdges₁ = {e0}`
- Apply `toggleSum_supported_on_cuts₁_10` (already proven)
- Use `support₁_add_toggles_singleton` (Commit A)
- Conclude strict descent

**Expected**: ~20 lines of straightforward composition

---

## Build Status

**File**: `FourColor/Geometry/Disk.lean`
**Total lines**: 967
**Sorries remaining**: ~5 (including H2-support, H3₁, mirror lemmas)
**Build status**: ✅ Success (only linter warnings)

---

## Technical Lessons Learned

### Z₂ Reasoning in Lean 4

- `fin_cases` tactic not available (or named differently)
- Use explicit `by_cases` with `zmod2_ne_zero_iff_eq_one`
- Need to prove `x = 0 ↔ ¬x = 1` explicitly for Z₂

### Variable Substitution

- After `subst h`, the substituted variable disappears
- Must use the remaining variable consistently
- Named intermediate lemmas help (e.g., `hy_eq_1` instead of reusing `hy1`)

### Finset Membership Proofs

- `exfalso` + direct contradiction clearer than complex `simp` chains
- Break down nested `by_cases` for readability
- Use `have` to name intermediate facts

---

## Methodology Notes

Following **Oružové Carneiro philosophy**:
- ✅ Drop-in proofs from Oruži worked with minor tactical adjustments
- ✅ Used explicit case analysis instead of fragile `simp` magic
- ✅ Named intermediate lemmas for clarity
- ✅ No clever tricks, just straightforward logic

**No parity arguments, no fragile case analysis - just clear, direct proofs!**

---

## Next Session Goals

1. ⏭️ **Commit C**: Implement H2-support (fill 3 small local lemmas)
2. ⏭️ **Commit D**: Wire H3₁ (straightforward composition)
3. ⏭️ Optional: Port v3 purification layer for robustness
4. ⏭️ CI sanity pass

---

## Summary

**What we completed**:
- ✅ Commit A: `support₁_add_toggles_singleton` (~29 lines)
- ✅ Commit B: Boundary case fix (~25 lines)
- Total: ~54 lines of solid Z₂ and graph theory proofs

**What's left**:
- Commit C: H2-support (~80-100 lines, skeleton provided)
- Commit D: H3₁ wiring (~20 lines, composition)
- Total remaining: ~100-120 lines

**Status**: 🟢 On track! H2→H3 pipeline almost wired!

---

## Credit

**Guidance**: Oruži (GPT-5 Pro)
**Implementation**: Claude Code (Robo Mario)
**Philosophy**: Oružové Carneiro (use fundamental properties, not clever tricks)
