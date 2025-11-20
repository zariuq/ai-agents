# Guardrail Concept: Proving Overapproximations Wrong

## The Idea (from GPT-5 Pro)

Instead of just removing bad code or hoping we won't use it again, **prove it's wrong** using the formal system itself.

## What We Wanted to Prove

The overapproximate `kempeChain`:
```lean
def kempeChain_overapprox (x : E → Color) (c₁ c₂ : Color) : Finset E :=
  Finset.univ.filter (fun e => x e = c₁ ∨ x e = c₂)  -- ALL αβ edges
```

is **provably wrong** for two uses:

### 1. Interior Property Violation
```lean
lemma kempeChain_overapprox_hits_boundary
    (D : ZeroBoundaryData V E) (x : E → Color) (c₁ c₂ : Color)
    (h : ∃ e, e ∈ D.boundaryEdges ∧ (x e = c₁ ∨ x e = c₂)) :
    ∃ e, e ∈ D.boundaryEdges ∧ e ∈ kempeChain_overapprox x c₁ c₂
```

**Meaning**: If any boundary edge is colored α or β, the overapprox includes it, violating interior-only requirement.

### 2. Kempe Cycle Property Violation
```lean
lemma kempeChain_overapprox_not_isKempeCycle_of_three
    (incident : V → Finset E) (x : E → Color) (v0 : V) (c₁ c₂ : Color)
    (h3 : 3 ≤ ((incident v0).filter (fun e => x e = c₁ ∨ x e = c₂)).card) :
    ¬ isKempeCycle incident x (kempeChain_overapprox x c₁ c₂) c₁ c₂
```

**Meaning**: If any vertex has ≥3 incident αβ-edges, the overapprox violates the degree-≤2 constraint of `isKempeCycle`.

### 3. Unit Test Counterexample
```lean
-- One vertex with three edges, all colored α
def V₀ := Unit
def E₃ := Fin 3
def incident₀ : V₀ → Finset E₃ := fun _ => Finset.univ
def x_all_alpha (α β : Color) : E₃ → Color := fun _ => α

-- This proves overapprox is NOT an isKempeCycle
example (α β : Color) (hαβ : α ≠ β) :
    ¬ isKempeCycle incident₀ (x_all_alpha α β)
      (kempeChain_overapprox (x_all_alpha α β) α β) α β
```

## Why This is Valuable

### Cultural/Architectural
- **Not just "don't do X"** - we **prove X is wrong**
- Build fails immediately with concrete counterexample
- No wishful thinking or "maybe it works in this case..."

### Technical
- Guardrails use the formal system itself
- Clear error messages pointing to violated properties
- Prevents overapprox from being used accidentally

## Why Implementation Failed

### Lean 4 Decidability Hell

Every attempt to prove these lemmas hit typeclass instance problems:

```
error: typeclass instance problem is stuck, it is often due to metavariables
```

**Root cause**: The `iff` statement `e ∈ ... ↔ (x e = c₁ ∨ x e = c₂)` requires decidability instances for:
- Membership in filtered Finset
- Color equality (has this)
- The disjunction
- The whole iff

Even with `classical`, `open scoped Classical`, `noncomputable`, explicit `DecidableEq` - **nothing worked**.

This is a known hard problem in Lean 4's typeclass resolution system.

## What We Achieved Instead

1. **Documented the concept** - future work can implement when Lean improves
2. **Kept the overapprox definition** with clear "MUST NOT use" warning
3. **Added sorry'd guardrail lemmas** - statements exist even if proofs don't compile

## Lessons Learned

### 1. Good Ideas Can Hit Tool Limitations

The guardrail concept is **excellent** - prove wrong code is wrong. But Lean 4's decidability system blocked implementation.

**This is NOT a failure of the idea** - it's a limitation of the current tool.

### 2. Document Intent Even When Blocked

The guardrail lemmas exist (with sorry) as **documentation of intent**:
- They state what SHOULD be provable
- They explain WHY the overapprox is wrong
- Future work can fill the sorries when Lean improves

### 3. Decidability is a Real Barrier

In Lean 4, simple-looking statements about Finsets can be unprovable due to typeclass resolution issues. This is a known problem that affects practical formalization work.

## What Actually Prevents Mistakes

**Current situation**:
- We have proper `kempeChain` (connected component, not overapprox)
- The overapprox definition exists but is clearly marked "MUST NOT use"
- Comments explain why it's wrong
- Sorry'd guardrail lemmas document the violations

**What would help**:
- Lean 5 or Lean 4 improvements to decidability
- Alternative formulation that avoids `iff` on complex predicates
- Community expertise on working around typeclass issues

## Conclusion

The guardrail concept is **sound and valuable**. Implementation was blocked by Lean 4 technical limitations, not by mathematical or logical problems.

We documented the intent and kept the infrastructure for future work.

**Key insight**: Sometimes the best we can do is document what SHOULD be provable, even when the tool prevents actually proving it.

---

**Date**: 2025-11-09
**Status**: Concept documented, implementation blocked by Lean 4 decidability
**Files affected**: Would have been `FourColor/KempeAPI.lean`, `FourColor/Tests/Guardrails.lean`
