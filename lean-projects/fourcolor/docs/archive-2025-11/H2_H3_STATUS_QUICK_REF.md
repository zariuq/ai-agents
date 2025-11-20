# H2→H3 Wiring: Quick Reference

**Last Updated**: 2025-11-04
**Build Status**: ✅ COMPILES with documented sorries

---

## Overall Status

| Component | Status | Lines | Sorries |
|-----------|--------|-------|---------|
| Commit A: `support₁_add_toggles_singleton` | ✅ COMPLETE | 29 | 0 |
| Commit B: Boundary case fix | ✅ COMPLETE | 25 | 0 |
| Commit C: H2-support skeleton | ⏳ IN PROGRESS | 145 | 3 |
| Commit D: H3₁ wiring | ⏭️ READY | — | 1 |

---

## File Locations

### Main Implementation
`FourColor/Geometry/Disk.lean`

### Documentation
- `docs/H2_H3_WIRING_PLAN_2025-11-04.md` - Oruži's guidance
- `docs/H2_H3_COMMITS_AB_COMPLETE_2025-11-04.md` - Commits A & B details
- `docs/COMMIT_C_PROGRESS_2025-11-04.md` - Commit C progress
- `docs/SESSION_2025-11-04_H2_H3_WIRING.md` - Full session summary

---

## Sorries to Fill

### Sorry 1: Line 619 (hS₀_touch tail case)
**Difficulty**: ⭐⭐ (pattern matching technical issue)
**Estimated**: 3-5 lines
**Strategy**: Extract witness edge from `adjOnSupportExcept` existential

### Sorry 2: Line 636 (huniq_e0)
**Difficulty**: ⭐⭐⭐ (requires NoDigons)
**Estimated**: 40-50 lines
**Strategy**: Cardinality + reachability contradiction

### Sorry 3: Line 642 (hno_other_support_cuts)
**Difficulty**: ⭐⭐ (straightforward R-adjacency)
**Estimated**: 15-20 lines
**Strategy**: Show both incident faces reachable via R

### Sorry 4: Line 678 (Commit D)
**Difficulty**: ⭐ (composition, after C complete)
**Estimated**: 20 lines
**Strategy**: Wire H2-support → cut-parity → descent

---

## Build Commands

```bash
# Build main file
lake build FourColor.Geometry.Disk

# Check for errors only
lake build FourColor.Geometry.Disk 2>&1 | grep -E "(error:|warning:.*sorry)"

# Full project build
lake build
```

---

## Key Definitions

### H2-Support Construction (Line 562)
```lean
lemma exists_leaf_subtree_with_prescribed_cut₁
    {x : E → Color} (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    {e0 : E} (he0_supp : e0 ∈ support₁ x)
    (he0_int : e0 ∉ G.toRotationSystem.boundaryEdges) :
    ∃ (S₀ : Finset (Finset E)), S₀.Nonempty ∧
      S₀ ⊆ facesTouching₁ G x ∧
      cutEdges₁ G x S₀ = {e0}
```

### adjOnSupportExcept
```lean
def adjOnSupportExcept (x : E → Color) (e0 : E) (f g : Finset E) : Prop :=
  f ∈ G.toRotationSystem.internalFaces ∧
  g ∈ G.toRotationSystem.internalFaces ∧
  (∃ e, e ≠ e0 ∧ e ∈ support₁ x ∧ e ∈ f ∧ e ∈ g)
```

---

## Next Steps

**Primary**: Commit D (H3₁ wiring) - line 678

**Optional**: Fill Sorries 1-3 in Commit C

**After D**: Lock descent pipeline, Tait finishing move

---

## Quick Links

**Previous Complete Work**:
- NoDigons proof: `docs/NODIGONS_COMPLETE_2025-11-04.md`
- Meridian parity: `docs/MERIDIAN_PARITY_COMPLETE_2025-11-04.md`

**Related Sessions**:
- H2 component-after-delete (previous session)
- Meridian layer implementation (previous session)
