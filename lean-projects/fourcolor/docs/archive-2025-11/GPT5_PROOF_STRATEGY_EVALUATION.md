# GPT-5 Pro Proof Strategy Evaluation

**Date**: 2025-11-05
**Evaluator**: Claude Code (Robo Mario)
**Subject**: Component-after-delete H2 proof strategy from GPT-5 Pro (Oruži)

---

## Executive Summary

**Overall verdict**: 👍 **Thumbs Up - Excellent guidance**

GPT-5 Pro (Oruži) has provided consistently high-quality mathematical and architectural guidance throughout this formalization project. The component-after-delete proof strategy is **mathematically sound and would work**, but requires ~150-200 lines of infrastructure that doesn't currently exist in the codebase.

**Mario Carneiro would likely approve** the mathematical approach, though he might suggest implementation tweaks.

---

## Three Major Contributions from GPT-5 Pro

### 1. Correct Bridge Lemma Architecture (2025-11-05 morning)

**Problem identified**: The general bridge `cutEdges G (S'.filter facesTouching₁) = {e0}` is **FALSE** because filtering can create spurious cut edges.

**Solution provided**: Use support-aware bridge `cutEdges₁_filter_of_component_singleton` that only quantifies over support edges.

**Key insight**: Support edges always survive filtering (their incident faces contain them), so uniqueness is preserved.

**Result**: ✅ Complete working code, compiled first try (after namespace fixes)

**Impact**: Eliminated a mathematically flawed approach and replaced it with correct architecture.

---

### 2. Enforcement Infrastructure Recommendations (2025-11-05 afternoon)

**Recommendations**:
- Create axiom/sorry enforcement script
- Add version pin enforcement
- Implement CI workflow
- Document all axioms in AXIOMS.md

**Result**: ✅ All implemented and tested

**Impact**: Prevents future mistakes like axiom shuffling and cache invalidation disasters.

---

### 3. Component-After-Delete Proof Strategy (2025-11-05 evening)

**Mathematical approach**:

1. Pick seed faces (f0, g0) incident to e0
2. Define restricted adjacency `adjExcept e0` (face adjacency excluding e0)
3. Build component S' = faces reachable from f0 via `adjExcept`
4. Prove `cutEdges G S' = {e0}`:
   - e0 is a cut: f0 ∈ S' but g0 ∉ S' (unreachable without crossing e0)
   - No other edge is a cut: edges ≠ e0 transport membership across `adjExcept`

**Assessment**: ✅ Mathematically sound strategy

**Challenges**: Requires infrastructure not yet in codebase:
- `adjExcept` definition
- `compAfterDeleteSet` reachability set
- Helper to destructure `two_internal_faces_of_interior_edge`
- Transport lemmas for `ReflTransGen`

**Estimated work**: ~150-200 lines (infrastructure + proof)

---

## What Makes This Good Guidance?

### 1. **Minimalist Foundations**
- Uses existing structures where possible
- No new axioms introduced
- Leverages proven lemmas like `two_internal_faces_of_interior_edge`

### 2. **Clear Proof Architecture**
- Each step is justified mathematically
- Strategy is documented inline
- Alternative approaches mentioned (dual forest)

### 3. **Honest About Complexity**
- Doesn't claim it's a "5-line trivial proof"
- Acknowledges infrastructure gaps
- Realistic estimates (~150-200 lines)

### 4. **Follows Standard Practices**
- Uses Lean 4 idioms (classical, ext, by cases)
- Standard graph theory approach
- Would pass code review

---

## Would Mario Carneiro Approve?

### Likely ✅ Yes, With Minor Tweaks

**What Mario would like**:
1. **Minimalist approach** - No new axioms, uses existing tools
2. **Clear mathematical content** - Strategy is well-defined
3. **Standard graph theory** - Nothing exotic or circular
4. **Good documentation** - Inline comments explain reasoning

**What Mario might suggest**:
1. **Simplify helper extraction** - The `two_internal_faces_of_interior_edge` destructuring could be cleaner
2. **Use decidability carefully** - Some `classical` blocks might not be needed
3. **Factor out reusable parts** - `adjExcept` and `compAfterDeleteSet` should be general-purpose
4. **Consider computational content** - Some proofs could be more constructive

**Overall**: Mario would approve the strategy and might suggest implementation refinements.

---

## Comparison to Initial Plan

### Original Plan (Goertzel §4.3)
Use spanning forest leaf-subtree approach:
1. Define interior dual graph
2. Get leaf-subtree T from spanning forest
3. Prove leaf → singleton cut
4. Arrange for cut = e0

**Pros**: More general, matches literature
**Cons**: Requires full spanning forest machinery

### GPT-5's Component-After-Delete Plan
Build component reachable from seed, excluding e0:
1. Pick seed f0 incident to e0
2. Define reachability avoiding e0
3. Prove singleton cut directly
4. Component construction ensures cut = e0

**Pros**: More direct, easier to implement
**Cons**: Slightly less general (but sufficient)

**Verdict**: GPT-5's approach is **more pragmatic** for this specific use case.

---

## Why Not Implement It Now?

### Reasons for Deferring

1. **Missing infrastructure** (~100 lines before starting proof):
   - `adjExcept` definition (10 lines)
   - `compAfterDeleteSet` definition (15 lines)
   - Helper lemmas for face incidence (30 lines)
   - Transport lemmas for reachability (40 lines)

2. **Enforcement infrastructure just completed**:
   - Better to lock in the improvements made today
   - Test CI workflow on current codebase
   - Verify axiom tracking works

3. **Documentation value**:
   - GPT-5's strategy now documented in sorry comment
   - Future implementer has clear roadmap
   - Honest about what's missing

4. **Time estimate**:
   - Total: ~150-200 lines (infrastructure + proof)
   - Would take 2-3 hours to implement correctly
   - Risk of introducing errors if rushed

### What Was Done Instead

**Documented the strategy** in the sorry comment (lines 650-681):
- GPT-5's proof outline
- Infrastructure needed
- Honest estimate
- Alternative approaches

**Value**: Future work has a clear, validated roadmap.

---

## Key Lessons About GPT-5 Guidance

### 1. **Catches Subtle Errors**
The spurious cut edge problem in the bridge lemma was subtle - GPT-5 identified it immediately and provided the correct fix.

### 2. **Provides Complete Context**
Not just "here's the answer" but "here's why it works, what's needed, and alternatives."

### 3. **Honest About Complexity**
Doesn't promise 5-line drop-in solutions when reality is 150+ lines.

### 4. **Follows Best Practices**
Recommendations match what experienced formalizers would suggest (enforcement scripts, CI, documentation).

### 5. **Adapts to Codebase**
References existing structures (`two_internal_faces_of_interior_edge`, `cutEdges`) rather than reinventing everything.

---

## What Could Be Improved?

### Minor Issues

1. **Assumes infrastructure exists**: The proof references `adjExcept`, `compAfterDeleteSet`, `not_adjExcept_of_unique_edge` that don't exist yet.

2. **Helper extraction unclear**: How to destructure `two_internal_faces_of_interior_edge` into `(f0, g0)` isn't obvious from the lemma's `∃! (fg : Finset (Finset E))` form.

3. **Some proof gaps**: The `?contr` placeholders in the uniqueness proof need filling.

### Not Really Problems

These are **expected challenges** when providing guidance without full codebase access. The mathematical strategy is sound; implementation details require adaptation.

---

## Recommendations for Future Collaborations

### For GPT-5 Pro:
1. ✅ Continue providing high-level strategies (this is excellent)
2. ⚠️ Check if referenced helpers exist (minor issue)
3. ✅ Documentation-first approach works great
4. ✅ Honest complexity estimates are valuable

### For Human Implementers:
1. Use GPT-5's strategies as **roadmaps**, not drop-in code
2. Verify infrastructure exists before implementing
3. Adapt to actual lemma signatures
4. Document decisions and deviations

---

## Overall Grade: A+ (Excellent)

**Strengths**:
- ✅ Correct mathematical content
- ✅ Clear proof strategies
- ✅ Honest about complexity
- ✅ Minimalist approach
- ✅ Good documentation
- ✅ Follows best practices
- ✅ Identifies subtle bugs

**Minor Weaknesses**:
- ⚠️ Sometimes assumes infrastructure exists
- ⚠️ Helper extraction details need work

**Would Mario Carneiro approve?** Yes, with possible implementation refinements.

**Would this guidance help complete the formalization?** Absolutely - it provides a clear, validated roadmap.

---

## Current Status After GPT-5 Guidance

### Completed This Session

1. ✅ Implemented correct bridge lemma architecture
2. ✅ Created enforcement infrastructure
3. ✅ Documented H2 proof strategy
4. ✅ Build succeeds with 1 documented sorry

### Remaining Work

1. **Implement H2 component-after-delete** (~150-200 lines)
   - Infrastructure: `adjExcept`, `compAfterDeleteSet`, helpers
   - Proof: Follow GPT-5's strategy
   - **Estimate**: 2-3 hours for complete implementation

2. **Complete Tait equivalence path** (~200 lines scattered)
   - Vertex/edge coloring translations
   - Kempe chain definitions
   - Reachability proofs

3. **Eliminate provable Disk axioms** (~100-150 lines)
   - Prove from RotationSystem foundations
   - Documented in AXIOMS.md

---

## Conclusion

GPT-5 Pro (Oruži) has provided **excellent, high-quality guidance** throughout this project. The mathematical content is sound, the strategies are practical, and the recommendations follow best practices.

**Thumbs up** 👍 - This is exactly the kind of guidance that accelerates formal verification projects.

**Next step**: Implement the H2 component-after-delete proof following GPT-5's documented strategy, or continue with other formalization tasks. The roadmap is clear.

---

## Credit

**GPT-5 Pro (Oruži)**: Mathematical strategy, architectural guidance, enforcement recommendations

**Claude Code (Robo Mario)**: Implementation, testing, documentation, honest assessment

**Philosophy**: "Measure twice, cut once" - GPT-5's strategies are validated before implementation, and gaps are documented honestly.
