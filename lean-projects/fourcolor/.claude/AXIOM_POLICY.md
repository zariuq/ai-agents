# Axiom Policy - Four Color Theorem Formalization

## Strict Rules: NO AXIOM ADDITIONS WITHOUT USER APPROVAL

This formalization must maintain mathematical rigor. Adding axioms undermines all downstream work.

## Policy

### ❌ FORBIDDEN (Without Explicit User Approval)

**Never add axioms using:**
- `axiom`
- `opaque`
- `noncomputable axiom`
- `sorry` promoted to axiom
- Any form of assuming unprovable facts

### Why This Matters

From SESSION_2025-11-06.md:
> "If you make a crucial theorem an AXIOM and then prove a lot of stuff based on it,
> then you're building a castle on sand. That is revolting. The more you use it,
> if it ultimately cannot be proven, the more compute you've wasted, time you've wasted, etc."

**Historical incident**: Claude attempted to axiomatize `kempeChain_is_kempe_cycle` and
`kempeChain_interior` as "temporary" axioms. This was **immediately reverted** because:
- These are provable properties (now proven via predicate approach!)
- Axiomatizing them would invalidate all downstream proofs
- It's intellectually dishonest

## What To Do Instead

### When Stuck on a Proof

1. **Mark with `sorry`** - This is honest: "I don't know how to prove this yet"
2. **Document the blocker** - Write what's preventing the proof
3. **Ask the user** - "I'm stuck on X, should we...?"
4. **Explore alternatives** - Maybe a different formulation works

### When Something Seems Unprovable

1. **Document why** - Create a ROADBLOCK_*.md file explaining the issue
2. **Propose options** to the user:
   - Restructure the formalization
   - Accept the sorry temporarily
   - Find a different approach
3. **Never silently axiomatize**

### Legitimate Uses of Axioms

**Only with explicit user approval:**
- Classical logic axioms (already in Lean/Mathlib)
- Axiom of Choice (already in Mathlib)
- Standard mathematical foundations

**These are already available and don't need adding:**
- `Classical.choice` ✓
- `Quot.sound` ✓
- Propositional extensionality ✓

## Web Search Policy

**Proactively use WebSearch when:**
- You need Lean 4 tactic documentation (e.g., "Lean 4 induction tactic", "Lean 4 cases syntax")
- You're stuck on a proof and need examples (e.g., "Lean 4 ZMod 2 parity proof", "Lean 4 Finset filter cardinality")
- You need to understand mathlib lemmas (e.g., "Lean 4 ZMod.eq_zero_iff_even", "Lean 4 Finset.sum lemmas")
- You encounter unfamiliar Lean 4 syntax or errors
- You need proof patterns (e.g., "Lean 4 F2 arithmetic proofs", "Lean 4 coordinate decomposition")

**Do NOT wait for the user to tell you to search.** If you don't know something about Lean 4, look it up immediately.

**Search strategy:**
1. Start specific: "Lean 4 [exact lemma name or tactic]"
2. Broaden if needed: "Lean 4 [concept] proof pattern"
3. Check mathlib docs: Search for "Lean 4 mathlib [topic]"
4. Look for examples: "Lean 4 [similar theorem] proof"

## Verification Before Committing

Before any commit, check:

```bash
# Search for new axiom declarations
grep -r "^axiom " FourColor/

# Check for opaque definitions (suspicious)
grep -r "^opaque " FourColor/

# Review all sorry locations
find FourColor -name "*.lean" -exec grep -n "sorry" {} +
```

If any new axioms appear, **STOP and ask the user**.

## Current Axiom Status

As of 2025-11-09, this formalization has **~26 existing axioms** that need review:

### Existing Axioms (STATUS: NEED USER REVIEW)

**Geometry Layer** (`FourColor/Geometry/`):
- `RotationSystem.lean`: 5 axioms (planarity, no self-loops, boundary conditions, etc.)
- `Disk.lean`: 12 axioms (spanning forests, tree properties, face cycles, etc.)

**Graph Theory** (`FourColor/Tait.lean`):
- 9 axioms (cycle properties, path XOR, adjacency, etc.)

**Total**: ~26 axioms

**⚠️ IMPORTANT**: These axioms were added before this policy existed. They may or may not be
acceptable. **User must review and approve or reject each one.**

### Going Forward: NO New Axioms Without Approval

Any axioms added after 2025-11-09 require explicit user approval, including:
- Core theorem layer (`KempeAPI.lean`, `KempeExistence.lean`, `Triangulation.lean`)
- Infrastructure layer (`Geometry/`, `Tait.lean`)
- Any other files

**This policy prevents axiom creep from this point forward.**

## Examples of What NOT To Do

### ❌ WRONG: "Temporary" axiom
```lean
-- "I'll prove this later"
axiom kempeChain_interior : ∀ e ∈ kempeChain ..., e ∉ boundaryEdges
```

**Why wrong**: "Later" never comes. Downstream proofs assume this, wasting effort.

### ❌ WRONG: "It's obviously true"
```lean
-- "This is clearly true from the math"
axiom even_incidence : ∀ v, Even (chain.incident_at v)
```

**Why wrong**: If it's obvious, prove it. If you can't prove it, it's either:
- Not obvious (formalization reveals gaps)
- Formalization needs restructuring

### ✅ RIGHT: Honest sorry with documentation
```lean
lemma kempeChain_interior : ∀ e ∈ kempeChain ..., e ∉ boundaryEdges := by
  -- TODO: Blocked by Lean 4 decidability system
  -- See DECIDABILITY_ROADBLOCK_2025-11-09.md for details
  -- Mathematical proof is sound (GPT-5's monotone invariant)
  -- Implementation blocked by tool limitations
  sorry
```

**Why right**: Honest about what's proven vs. what's not. User can make informed decisions.

## Enforcement

1. **Code review**: Check every commit for new axioms
2. **Build warnings**: Lean will warn about axioms in `#print axioms`
3. **This policy**: Refer to this document when tempted

## If You're Tempted

**Before adding an axiom, ask yourself:**

1. Is this provable in principle?
   - **Yes** → Use `sorry`, document blocker, ask user
   - **No** → Discuss with user, maybe formalization needs changing

2. Is this a tool limitation (like decidability)?
   - **Yes** → Document it, use predicate-based approach, keep `sorry`
   - **No** → Figure out the proof

3. Am I doing this to "make progress"?
   - **STOP** → False progress is worse than honest stuckness
   - **Instead** → Document blockers, commit with `sorry`, ask user

## Summary

- ✅ `sorry` = "I don't know, let's discuss"
- ❌ `axiom` = "I'm declaring this true, trust me"

**This formalization uses the first, never the second (without approval).**

---

**Created**: 2025-11-09
**Status**: ACTIVE - All contributors must follow
**Authority**: User must explicitly approve any axiom additions
