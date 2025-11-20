# Commit C Progress Report: H2-Support Implementation

**Date**: 2025-11-04
**Status**: IN PROGRESS - Skeleton complete, 4 sorries remaining

---

## Summary

Commit C (H2-support implementation) has made significant progress. The skeleton from Oruži's guidance is fully in place and compiling. Four sorries remain to be filled, three of which are the originally planned local lemmas.

---

## Current Status

### File: `FourColor/Geometry/Disk.lean`

**Lemma**: `exists_leaf_subtree_with_prescribed_cut₁` (lines 562-706)

**Purpose**: Component-after-delete construction using support-restricted reachability

**Build status**: ✅ **COMPILES** with 4 sorries

---

## Sorries Remaining

### Sorry 1: ReflTransGen.tail destructuring (line 619)

**Location**: Inside `hS₀_touch` proof, inductive case of ReflTransGen

**Issue**: Pattern matching for `adjOnSupportExcept` structure

**Definition**:
```lean
def adjOnSupportExcept (x : E → Color) (e0 : E) (f g : Finset E) : Prop :=
  f ∈ G.toRotationSystem.internalFaces ∧
  g ∈ G.toRotationSystem.internalFaces ∧
  (∃ e, e ≠ e0 ∧ e ∈ support₁ x ∧ e ∈ f ∧ e ∈ g)
```

**Attempted approaches**:
1. `let ⟨...⟩ := h_step` → Invalid ⟨...⟩ notation error (ReflTransGen has multiple constructors)
2. `obtain ⟨...⟩ := h_step` → Identifiers not in scope
3. `rcases h_step with ⟨...⟩` → Identifiers not in scope
4. `unfold adjOnSupportExcept` before rcases → Same issue
5. `have := h_step.2.2` → Invalid projection (Prop, not structure)

**Root cause**: In the `tail` case of ReflTransGen induction, `h_step` has type `R prev_face current_face` where `R = adjOnSupportExcept G x e0`. The pattern matching needs to destructure the 3-level conjunction structure `A ∧ B ∧ (∃ e, ...)` but Lean 4 is not binding the variables correctly.

**Next steps to try**:
- Use explicit `And.intro` / `And.left` / `And.right` to manually destructure
- Check if there's an `R.choose` API for the existential
- Simplify to just `sorry` and move on (current status)

### Sorry 2: huniq_e0 uniqueness proof (line 636)

**Goal**: Prove e0 has exactly one incident face in S₀ (namely f₀)

**Proof strategy**:
1. f is reachable from f₀ via R-steps (since f ∈ S₀)
2. There are only 2 faces containing e0: f₀ and g₀ (from `incident_faces_of_interior_edge`)
3. If f ≠ f₀, then f = g₀
4. But g₀ is NOT reachable from f₀ via R (since R excludes e0)
5. Contradiction ⇒ f = f₀

**Dependencies needed**:
- NoDigons property (to show g₀ unreachable)
- Cardinality reasoning for `facesIncidence e0`

**Status**: Skeleton documented, needs ~40-50 lines of careful cardinality/reachability reasoning

### Sorry 3: hno_other_support_cuts (line 642)

**Goal**: For any support edge e ≠ e0, prove ¬(∃! f, f ∈ S₀ ∧ e ∈ f)

**Proof strategy**:
1. Let e be a support edge with e ≠ e0
2. Get its two incident faces f_e and g_e from `incident_faces_of_interior_edge`
3. If one is in S₀, show R-adjacency via e means the other is too
4. Therefore e has 0 or 2 incident faces in S₀, never exactly 1

**Dependencies needed**:
- `incident_faces_of_interior_edge` (already available)
- R-adjacency property

**Status**: Clear proof strategy, needs ~15-20 lines

### Sorry 4: aggregated_toggle_strict_descent_at_prescribed_cut₁ (line 678)

**This is Commit D, not Commit C!**

**Goal**: Wire H2-support into H3₁ descent

**Dependencies**: Sorries 1-3 must be completed first

**Proof strategy**:
1. Get S₀ from H2-support with `cutEdges₁ G x S₀ = {e0}`
2. Apply `toggleSum_supported_on_cuts₁_10` (already proven)
3. Use `support₁_add_toggles_singleton` (Commit A, complete)
4. Conclude strict descent

**Status**: Straightforward composition once Commit C is done

---

## Technical Challenges Encountered

### Pattern Matching in Induction

The `tail` case of `ReflTransGen` induction provides `h_step : R a b`, but Lean 4's pattern matching for nested conjunctions + existentials is not working as expected. Multiple approaches tried, all failed.

**Workaround**: Temporarily using `sorry` to unblock other work.

### Variable Scoping with `subst`

After `subst hf_is_g₀` where `hf_is_g₀ : f = g₀`, Lean replaces all `g₀` with `f`, not the other way around. This causes `g₀` to disappear from scope.

**Solution**: Use `rw [hf_is_g₀] at hreach` instead of `subst`.

### Finset Cardinality Lemmas

`Finset.eq_of_subset_of_card_le` expects specific argument structure that wasn't matching. Attempted to use `ext` with manual case analysis but got complex.

**Workaround**: Simplified to `sorry` with documented proof strategy.

---

## Code Statistics

**Lines written**: ~145 lines (including comments and structure)
**Lines of skeleton from Oruži**: ~80 lines
**Additional infrastructure**: ~65 lines of proof attempts

**Current state**:
- ✅ Component-after-delete structure complete
- ✅ ReflTransGen R definition correct
- ✅ S₀ construction correct
- ✅ hS₀_nonempty proven
- ⏳ hS₀_touch: base case done, tail case has sorry
- ⏳ huniq_e0: strategy documented, needs implementation
- ⏳ hno_other_support_cuts: strategy documented, needs implementation
- ✅ cutEdges₁ = {e0} packaging complete (uses above lemmas)

---

## Next Steps

### Option A: Push forward with sorries
1. Document the current state clearly
2. Move to Commit D (H3₁ wiring) with sorries in place
3. Complete the full H2→H3 pipeline with axioms
4. Return to fill sorries later

### Option B: Complete Commit C now
1. Solve Sorry 1 with explicit conjunction destructuring
2. Implement Sorry 2 using NoDigons
3. Implement Sorry 3 with R-adjacency
4. Then proceed to Commit D

**Recommendation**: Option A for now - get the full pipeline wired, then return to fill technical details. The proof strategies are clear and documented.

---

## Alignment with Oruži's Guidance

Following Oruži's 5-step plan:

1. ✅ **Step 1**: Finish two local H3 sorries (Commits A & B) - COMPLETE
2. ⏳ **Step 2**: Implement H2-support (Commit C) - IN PROGRESS (skeleton done, 3 local sorries remain)
3. ⏭️ **Step 3**: Wire H3₁ to H2 (Commit D) - NEXT
4. ⏭️ **Step 4**: (Optional) Port v3 purification layer
5. ⏭️ **Step 5**: CI sanity pass

---

## Conclusion

Commit C has substantial progress:
- ✅ Skeleton implementation matches Oruži's guidance exactly
- ✅ File compiles with documented sorries
- ✅ Proof strategies for remaining work are clear
- ⏳ Three technical lemmas need completion (Sorries 1-3)

The H2-support construction is **architecturally complete** and ready to be used by Commit D, even with sorries in place.

**Ready to proceed to Commit D (H3₁ wiring)!**

---

## Credit

**Guidance**: Oruži (GPT-5 Pro)
**Implementation**: Claude Code (Robo Mario)
**Philosophy**: Oružové Carneiro (use fundamental properties, document clearly when blocked)
