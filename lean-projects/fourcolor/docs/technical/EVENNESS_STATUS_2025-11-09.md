# Evenness Proof Status - 2025-11-09 (End of Session)

## Goal
Prove that Kempe chains have even incidence at every vertex, eliminating the last sorry in `kempeFix_preserves_zero`.

## What Was Accomplished ✅

### 1. Infrastructure Built
Created the full lemma structure following GPT-5 Pro's guidance:
- `even_alphaBeta_incident` (L1 - F₂ parity)
- `alphaBeta_incident_are_interior` (helper)
- `KempePred_equiv_on_alphaBeta_at` (L2 - local pairing)
- `kempePred_even_at` (main assembly)

### 2. Partial Proofs Completed ✅
- **Filter equivalence**: PROVEN (KempePred includes color check)
- **`alphaBeta_incident_are_interior`**: PROVEN (boundary edges are zero, contradiction)

### 3. Web Search Integration ✅
- Used WebSearch to find ZMod 2 parity lemmas
- Found `ZMod.eq_zero_iff_even`: `(n : ZMod 2) = 0 ↔ Even n`
- Updated `.claude/AXIOM_POLICY.md` with Web Search Policy

## What Remains Unproven ❌

### Critical Blocker: F₂² Parity Argument

**Lemma**: `even_alphaBeta_incident`
```lean
lemma even_alphaBeta_incident
    (D : ZeroBoundaryData V E) (x : E → Color) (α β : Color)
    (hx : InZero D x) :
    ∀ w : V, Even ((D.incident w).filter (fun e => x e = α ∨ x e = β)).card
```

**Mathematical claim**: From `∑ e ∈ incident w, x e = (0, 0)` in F₂² = (ZMod 2) × (ZMod 2), the cardinality of edges colored α or β is even.

**Status**: Has `sorry` (line 320)

**Why it's hard**:
- Requires decomposing the sum by color partitions
- Need to analyze coordinates in (ZMod 2) × (ZMod 2) separately
- Must connect cardinalities to ZMod 2 values using `ZMod.eq_zero_iff_even`
- Requires deep understanding of F₂² arithmetic patterns

**What was tried**:
- Studied `swap_preserves_vertex_sum` (assumes evenness, doesn't prove it)
- Found ZMod 2 parity lemmas in mathlib
- Attempted direct proof structure but got stuck on coordinate analysis

### Dependent Blockers

**Lemma**: `KempePred_equiv_on_alphaBeta_at` (line 370)
- Local pairing: two αβ-edges at same vertex are reachable in line graph
- **Status**: Has `admit`
- **Dependency**: None directly, but needed for final assembly

**Lemma**: `kempePred_even_at` (line 400)
- Main assembly: combines L1 + L2 via case analysis
- **Status**: Has `sorry`
- **Dependency**: Blocked by `even_alphaBeta_incident`

**Nonzero color properties** (lines 549-550)
- Show c₁ ≠ (0,0) and c₂ ≠ (0,0) from bad vertex + InZero
- **Status**: Has `admit`
- **Complexity**: Moderate (unfold definitions, use contradiction)

## Current Sorry/Admit Count

**In KempeAPI.lean**:
- 1 sorry in `even_alphaBeta_incident` (F₂ parity)
- 1 admit in `KempePred_equiv_on_alphaBeta_at` (local pairing)
- 1 sorry in `kempePred_even_at` (assembly)
- 2 admits for nonzero colors

**Total: 5 unproven statements**

## Build Status

✅ **Compiles successfully** (all sorries/admits are properly placed)

```bash
$ lake build FourColor.KempeAPI
Build completed successfully (7342 jobs).
```

## Honest Assessment

### What Went Well
1. ✅ Understood the problem and GPT-5's strategy
2. ✅ Built correct lemma structure
3. ✅ Proved 2 lemmas completely (filter equivalence, interior helper)
4. ✅ Learned to use WebSearch for Lean 4 research
5. ✅ Maintained zero-tolerance policy (no axioms, honest about gaps)

### What Didn't Work
1. ❌ Could not complete F₂² parity proof
2. ❌ Underestimated difficulty of ZMod 2 coordinate analysis
3. ❌ Need deeper Lean 4 expertise for modular arithmetic proofs

### Why This Is Hard

This is **not** a simple proof. The F₂² parity argument requires:
- Understanding how to partition a sum by color classes
- Converting between Finset cardinalities and ZMod 2 values
- Manipulating equations in (ZMod 2) × (ZMod 2) coordinates
- Using `ZMod.eq_zero_iff_even` in the right places

**This is advanced Lean 4 formalization** requiring expertise beyond my current capability.

## Next Steps (Options)

### Option 1: Expert Help
- Post to Lean Zulip with specific F₂² parity question
- Ask Mario Carneiro or mathlib4 contributors
- This is a well-scoped, interesting mathematical question

### Option 2: Simplify The Problem
- Look for alternative characterization of evenness
- Find existing mathlib lemmas that might apply
- Consider if there's a combinatorial argument instead of algebraic

### Option 3: Accept Current State
- Document the 5 unproven statements clearly
- Move to other sorries in the codebase
- Return to evenness proof when more Lean 4 expertise is gained

### Option 4: Study More Examples
- Find similar F₂ parity proofs in mathlib4
- Study how others handle sum decomposition by partition
- Learn ZMod 2 arithmetic patterns from existing code

## Key Lemmas Needed (For Future Reference)

```lean
-- Mathlib lemmas that might help:
ZMod.eq_zero_iff_even : (n : ZMod 2) = 0 ↔ Even n
Finset.sum_partition : -- (look for this)
Finset.card_sum : -- (look for this)
nsmul_eq_zero_iff : -- in ZMod context

-- Pattern to learn:
-- How to show: (∑ e in S, f e : ZMod 2) = 0 → Even S.card
```

## Conclusion

**We made real progress** (2 lemmas proven, infrastructure built, learned WebSearch), but **hit a genuine blocker** (F₂² parity proof beyond current capability).

**This is NOT a failure** - it's hitting the boundary of expertise and being honest about it. The mathematical approach is sound (GPT-5 verified), but the Lean 4 implementation requires skills we need to develop.

**Recommendation**: Seek expert help on the F₂² parity proof specifically. This is a well-defined, interesting problem that the Lean community can help with.

---

**Session Date**: 2025-11-09 (Evening)
**Status**: Partial progress, honest blockers documented
**Build**: ✅ Compiles
**Policy**: ✅ Zero-tolerance maintained (no axioms, honest about unproven statements)
