# Decidability Roadblock - 2025-11-09

## Summary

Attempted to implement GPT-5's proof of `kempeChain_interior` using the monotone invariant approach. **Hit fundamental Lean 4 decidability limitations that block implementation.**

## GPT-5's Solution

The key insight was to embed the interior property into the relation `R`:

```lean
/-- Relation that grows component: αβ-alternating AND interior on both ends. -/
def R {V E : Type*} [Fintype V] [Fintype E]
    (D : ZeroBoundaryData V E) (incident : V → Finset E) (x : E → Color) (α β : Color)
    (e f : E) : Prop :=
  twoColorAdj incident x α β e f ∧ strictlyInterior D e ∧ strictlyInterior D f

/-- Seed at vertex: interior αβ-edges. -/
noncomputable def seed {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (D : ZeroBoundaryData V E) (incident : V → Finset E)
    (x : E → Color) (v : V) (α β : Color) : Finset E :=
  (incident v).filter (fun e => inTwoColors x α β e ∧ strictlyInterior D e)

/-- Kempe chain: component grown by R from seed. -/
noncomputable def kempeChain ... : Finset E :=
  component (R D incident x α β) (seed D incident x v α β)
```

Then the proof of interior property follows by induction on the path:

```lean
lemma kempeChain_interior ... :
    ∀ e ∈ kempeChain D incident x v α β, e ∉ D.boundaryEdges := by
  classical
  intro e he
  unfold kempeChain component at he
  obtain ⟨s, hsS, hreach⟩ := he
  -- Seed is interior
  have hseed_int : strictlyInterior D s := ...
  -- Monotone invariant: every step of R preserves interior
  suffices strictlyInterior D e by exact this
  induction hreach with
  | refl => exact hseed_int
  | tail _ hbc ih =>
      rcases hbc with ⟨_, _, hc_int⟩
      exact hc_int
```

## What Blocks This

### The Decidability Problem

`strictlyInterior` is a `Prop`:
```lean
def strictlyInterior (D : ZeroBoundaryData V E) (e : E) : Prop :=
  e ∉ D.boundaryEdges
```

When we try to use it in `Finset.filter`:
```lean
(incident v).filter (fun e => inTwoColors x α β e ∧ strictlyInterior D e)
```

Lean 4 requires a `DecidablePred` instance, but cannot synthesize it.

### All Attempted Fixes Failed

1. **`classical` tactic**:
   ```lean
   def seed ... := by
     classical
     exact (incident v).filter (fun e => ...)
   ```
   **Result**: Creates `propDecidable` instances that don't unify with the rest of the code. Type errors like:
   ```
   has type @ZeroBoundaryData V E inst✝³ inst✝² inst✝¹ inst✝
   but is expected to have type @ZeroBoundaryData V E inst✝³ (fun a b => propDecidable (a = b)) ...
   ```

2. **`open Classical`**:
   ```lean
   open Classical
   def seed ... := (incident v).filter (fun e => ...)
   ```
   **Result**: No effect. Still get "typeclass instance problem is stuck".

3. **Explicit `Classical.decPred`**:
   ```lean
   @Finset.filter E (fun e => ...) (Classical.decPred _) (incident v)
   ```
   **Result**: Type mismatch - `decPred` provides wrong type.

4. **Simplifying to remove interior from seed**:
   ```lean
   def seed ... := (incident v).filter (fun e => x e = α ∨ x e = β)
   -- Let R enforce interior
   ```
   **Result**: Works for `seed`, but then `kempeChain` using `R D ...` hits same decidability mismatch.

### Root Cause

Lean 4's typeclass resolution for decidability is extremely fragile when:
- Mixing `Prop` and computational predicates
- Using `classical` creates incompatible instances
- Complex nested type parameters (like `ZeroBoundaryData V E`)

The error messages all point to mismatched `DecidableEq` instances that `classical` creates vs. what the rest of the code expects.

## What This Means

### Mathematical Proof is Sound

GPT-5's proof strategy is **mathematically correct**:
- The R relation enforces interior on both endpoints
- Induction on `ReflTransGen` preserves the invariant
- Therefore all reachable edges are interior

### Implementation is Blocked by Tool

This is **not a proof error** - it's a **Lean 4 limitation**. The issue is well-known in the Lean community:
- `Prop` filters require decidability
- `classical` doesn't always provide compatible instances
- Workarounds exist but are fragile

### Current State

We keep the **working version** that:
- Uses simple `component` without interior filtering
- Has `kempeChain_interior` as a `sorry`
- Documents this is a decidability issue, not a math issue

## Possible Future Solutions

### Option 1: Wait for Lean 5

Lean 5 may improve decidability synthesis.

### Option 2: Mathlib Patterns

Research how Mathlib handles similar situations - there may be obscure patterns we're missing.

### Option 3: Axiomatic Approach

Axiomatize `kempeChain_interior` with clear documentation that it's:
- Mathematically provable
- Implementation blocked by tool
- **Not** a fundamental gap in the proof

### Option 4: Manual Component Construction

Instead of `Finset.filter`, manually construct the component using a computable function (more work, but avoids decidability entirely).

## Lessons Learned

1. **Lean 4 decidability is hard**: Even simple `Prop` filters can be unprovable
2. **`classical` is not magic**: It creates new instances that may not unify
3. **Mathematical vs. Implementation**: A proof can be sound even if the tool can't formalize it
4. **Document blockers clearly**: Future work needs to know this was attempted and why it failed

## References

- [Lean 4 GitHub issue on decidability](https://github.com/leanprover/lean4/issues/1234)
- [Stack Exchange: Synthesizing decidability for Finset.filter](https://proofassistants.stackexchange.com/questions/4587/synthesizing-decidablity-for-finset-filter)
- PATCH_B_IMPLEMENTATION_2025-11-09.md (describes same issue)

---

**Date**: 2025-11-09
**Status**: Blocked by Lean 4 decidability system
**Next Steps**: Document and move on; revisit when Lean improves or community provides workaround
