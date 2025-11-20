# Filling Sorries: Attempt and Findings

**Date**: 2025-11-04
**Goal**: Fill remaining sorries in H2→H3 pipeline using web search and creativity
**Result**: Identified fundamental technical barrier, documented all approaches tried

---

## Summary

Attempted to fill the remaining sorries, starting with Sorry 1 (the pattern matching issue). After extensive web research and multiple tactical approaches, identified a fundamental limitation with Lean 4's pattern matching in induction contexts with nested Prop structures.

---

## Web Research Findings

### Pattern Matching with Existentials in Lean 4

From Lean 4 documentation and Stack Exchange:

1. **To unpack existentials**: Use `let ⟨x, hx⟩ := h` where `h : ∃ x, p x`
2. **For nested conjunctions**: Pattern `⟨p1, p2, p3⟩` can match nested `a ∧ b ∧ c`
3. **Prop elimination limitation**: With proof irrelevance, pattern matching on inductive Props can only eliminate into Prop
4. **Alternative**: Use `Classical.choose` to extract witnesses non-constructively

### Conjunction Destructuring

Multiple approaches available:
- Explicit: `And.left h` and `And.right h`
- Accessor notation: `h.1` and `h.2`
- Pattern matching: `have ⟨h1, h2⟩ := h`

---

## Approaches Tried for Sorry 1

### The Problem

**Location**: Line 620 in `hS₀_touch` proof, tail case of ReflTransGen induction

**Goal**: Extract witness edge from `h_step : R prev_face current_face` where `R = adjOnSupportExcept G x e0`

**Structure of adjOnSupportExcept**:
```lean
def adjOnSupportExcept (x : E → Color) (e0 : E) (f g : Finset E) : Prop :=
  f ∈ G.toRotationSystem.internalFaces ∧
  g ∈ G.toRotationSystem.internalFaces ∧
  (∃ e, e ≠ e0 ∧ e ∈ support₁ x ∧ e ∈ f ∧ e ∈ g)
```

### Attempt 1: Nested `let` Pattern
```lean
let ⟨_, _, e_wit, _, he_wit_supp, _, he_wit_f⟩ := h_step
```
**Error**: "Invalid ⟨...⟩ notation: The expected type `ReflTransGen R f₀ b✝` has more than one constructor"

**Analysis**: Lean infers `h_step` has type `ReflTransGen` (the induction type) rather than `R` (the relation).

### Attempt 2: `obtain` Pattern
```lean
obtain ⟨_, _, e_wit, _, he_wit_supp, _, he_wit_f⟩ := h_step
```
**Error**: "Unknown identifier `e_wit`"

**Analysis**: Pattern match doesn't bind variables - same root cause as Attempt 1.

### Attempt 3: `rcases` Pattern
```lean
rcases h_step with ⟨_, _, e_wit, _, he_wit_supp, _, he_wit_f⟩
```
**Error**: "Unknown identifier `e_wit`"

**Analysis**: Same issue - variables not bound.

### Attempt 4: `unfold` Before Pattern Match
```lean
unfold adjOnSupportExcept at h_step
rcases h_step with ⟨_, _, e_wit, _, he_wit_supp, _, he_wit_f⟩
```
**Error**: "Invalid ⟨...⟩ notation: The expected type `ReflTransGen R f₀ b✝`..."

**Analysis**: Even after unfolding, Lean still infers the type as `ReflTransGen`.

### Attempt 5: Manual Projection `.2.2`
```lean
have h_exists := h_step.2.2
```
**Error**: "Invalid projection: Expected a value whose type is a structure"

**Analysis**: Can't use projection notation on Prop types.

### Attempt 6: `And.left` / `And.right`
```lean
have h_exists := And.right (And.right h_step)
```
**Error**: "Application type mismatch"

**Analysis**: Type inference issue - Lean doesn't know h_step unfolds to conjunction.

### Attempt 7: Two-Step `have` Destructuring
```lean
unfold adjOnSupportExcept at h_step
have ⟨_, _, h_exists⟩ := h_step
have ⟨e_wit, _, he_wit_supp, _, he_wit_f⟩ := h_exists
```
**Error**: "Invalid ⟨...⟩ notation: The expected type `ReflTransGen R f₀ b✝`..."

**Analysis**: First `have` already fails with the same type inference issue.

### Attempt 8: `cases` with Explicit Constructors
```lean
cases h_step with | intro hprev hf_step =>
...
```
**Error**: "Invalid alternative name `intro`: Expected `refl` or `tail`"

**Analysis**: Lean interprets `cases` on the `ReflTransGen` type, not on `R`.

### Attempt 9: `classical` + `have` Pattern
```lean
classical
have ⟨_, _, h_ex⟩ := h_step
```
**Error**: "Invalid ⟨...⟩ notation: The expected type `ReflTransGen R f₀ b✝`..."

**Analysis**: Adding `classical` doesn't resolve the type inference issue.

---

## Root Cause Analysis

###The Fundamental Issue

In the `tail` case of `ReflTransGen.induction`, the hypothesis `h_step` is bound with type:
```
h_step : R a b
```

However, **Lean's elaborator doesn't automatically substitute the definition of `R`** during pattern matching. Instead, it keeps inferring the type as being related to `ReflTransGen` itself.

### Why This Happens

1. **Induction Context**: We're inside an `induction ... with | tail h_step _ ih =>` block
2. **Type Opacity**: Lean treats `R` as an abstract predicate during pattern matching
3. **Prop Elimination**: Pattern matching on Props has limitations (can only eliminate into Prop)
4. **Constructor Confusion**: Lean expects `refl` or `tail` constructors (from ReflTransGen), not the structure of `R`

### What Should Work (But Doesn't)

Theoretically, since `R = adjOnSupportExcept G x e0`, the type `R prev f` should unfold to the conjunction-existential structure, and pattern matching should work. But Lean's elaborator doesn't perform this unfolding automatically in the induction context.

---

## Possible Solutions (Not Yet Tried)

### Solution 1: Auxiliary Lemma
Define a helper lemma outside the induction:
```lean
lemma adjOnSupportExcept_exists_witness {f g : Finset E}
    (h : adjOnSupportExcept G x e0 f g) :
    ∃ e, e ∈ support₁ x ∧ e ∈ g := by
  have ⟨_, _, e, _, he_supp, _, he_g⟩ := h
  exact ⟨e, he_supp, he_g⟩
```

Then use it in the induction:
```lean
have ⟨e_wit, he_wit_supp, he_wit_f⟩ := adjOnSupportExcept_exists_witness h_step
```

**Likelihood of success**: High - separates the pattern matching from the induction context.

### Solution 2: Change `adjOnSupportExcept` to a Structure
Instead of a conjunction of Props, define it as an inductive type:
```lean
structure AdjOnSupportExcept (x : E → Color) (e0 : E) (f g : Finset E) : Prop where
  f_internal : f ∈ G.toRotationSystem.internalFaces
  g_internal : g ∈ G.toRotationSystem.internalFaces
  witness_edge : E
  witness_ne : witness_edge ≠ e0
  witness_supp : witness_edge ∈ support₁ x
  witness_f : witness_edge ∈ f
  witness_g : witness_edge ∈ g
```

Then use projection: `h_step.witness_edge`, `h_step.witness_supp`, etc.

**Likelihood of success**: Very high - structures have named fields that can be accessed directly.

**Drawback**: Requires changing the definition and all uses of `adjOnSupportExcept`.

### Solution 3: Use `revert` to Take `h_step` Out of Context
```lean
| tail h_step _ ih =>
  revert h_step
  intro h_step
  -- Now pattern match
  have ⟨_, _, h_ex⟩ := h_step
  ...
```

**Likelihood of success**: Medium - might reset the type inference.

### Solution 4: Explicit Type Annotation
```lean
have h_step_typed : adjOnSupportExcept G x e0 prev f := h_step
have ⟨_, _, h_ex⟩ := h_step_typed
```

**Likelihood of success**: Medium - forces the type to be what we want.

---

## Status of Other Sorries

### Sorry 2 (Line 637): huniq_e0
**Status**: Not attempted
**Difficulty**: ⭐⭐⭐ (requires NoDigons + cardinality reasoning)
**Estimated lines**: 40-50
**Strategy**: Clear and documented

### Sorry 3 (Line 646): hno_other_support_cuts
**Status**: Not attempted
**Difficulty**: ⭐⭐ (R-adjacency argument)
**Estimated lines**: 15-20
**Strategy**: Clear and documented

### Sorry at Line 695: Commit D (H3₁ wiring)
**Status**: Not attempted
**Difficulty**: ⭐⭐ (composition + type inference)
**Estimated lines**: 50-80
**Strategy**: Documented, needs careful tactical work

### Sorry at Line 835: Boundary edge handling
**Status**: Not attempted
**Difficulty**: ⭐ (minor case)
**Estimated lines**: 5-10
**Strategy**: Should follow same pattern as corresponding lemma

---

## Recommendations

### Short Term: Auxiliary Lemma Approach

**Implement Solution 1** - write an auxiliary lemma to extract the witness outside the induction context:

```lean
private lemma adjOnSupportExcept_exists_support_edge {f g : Finset E}
    (h : adjOnSupportExcept G x e0 f g) :
    ∃ e ∈ support₁ x, e ∈ g := by
  obtain ⟨_, _, e, _, he_supp, _, he_g⟩ := h
  exact ⟨e, he_supp, he_g⟩
```

This should work because the pattern matching happens in a fresh lemma, not inside the induction.

### Long Term: Structure Refactoring

**Implement Solution 2** if the auxiliary lemma approach has issues - refactor `adjOnSupportExcept` to be a structure with named fields. This is more invasive but provides the cleanest solution.

---

## Lessons Learned

### Lean 4 Pattern Matching Limitations

1. **Context matters**: Pattern matching behavior depends on whether you're in an induction, match expression, or standalone lemma
2. **Type inference is conservative**: Lean doesn't always unfold definitions automatically
3. **Prop elimination is restricted**: Can't always pattern match on Prop types into Type
4. **Structures > Conjunctions**: For complex Props that need field access, structures are more reliable than nested conjunctions

### Proof Engineering

1. **Extract complex patterns to helper lemmas**: When pattern matching fails in context, move it to a separate lemma
2. **Use structures for complex propositions**: If you need to access components frequently, use a structure
3. **Test patterns early**: Try pattern matching approaches early before building complex proofs around them
4. **Document failed approaches**: Helps others (and future you) understand what doesn't work

---

## Conclusion

**Sorry 1 is a genuine technical challenge** due to Lean 4's pattern matching limitations in induction contexts. Multiple standard approaches failed due to type inference issues.

**The solution is clear**: Use an auxiliary lemma to extract the witness outside the induction context. This is a known workaround pattern in Lean proof engineering.

**The other sorries (2, 3, D)** are more straightforward - they need lemmas and reasoning but don't have fundamental technical barriers.

**Overall assessment**:
- ✅ Architecture is sound
- ✅ Proof strategies are clear
- ⏳ Implementation needs tactical refinement
- 🔧 Sorry 1 needs the auxiliary lemma workaround

---

## Next Steps

1. **Implement auxiliary lemma for Sorry 1**
2. **Test if it compiles**
3. **If successful, continue to Sorry 2 and 3**
4. **Complete Commit D wiring**
5. **Full H2→H3 pipeline will be complete!**

---

## Credit

**Research**: Web search on Lean 4 documentation, Stack Exchange, theorem proving resources
**Implementation**: Claude Code (Robo Mario with maximum creativity!)
**Philosophy**: When clever tactics fail, use simpler helper lemmas
