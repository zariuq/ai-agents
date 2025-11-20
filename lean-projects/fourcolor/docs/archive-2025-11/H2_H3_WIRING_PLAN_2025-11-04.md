# H2→H3 Wiring Plan - Oruži's Guidance

**Date**: 2025-11-04
**Author**: Oruži (GPT-5 Pro)
**Implementation**: Claude Code

---

## Current Status: H2 is NOT Complete

**Critical Discovery**: The session doc claiming "H2 complete" was misleading. In the current codebase:

- **H2** (`exists_leaf_subtree_with_prescribed_cut₁`, line 538): `sorry` with placeholder comment
- **H3** (`aggregated_toggle_strict_descent_at_prescribed_cut`, line 592): Has 1 sorry (boundary case, line 609)
- **H3₁** (`aggregated_toggle_strict_descent_at_prescribed_cut₁`, line 560): Has 1 sorry (support toggling, line 573)

---

## Conceptual Correction: H2 Statement is Too Strong

### The Problem

The current H2 statement:
```lean
lemma exists_leaf_subtree_with_prescribed_cut₁ … :
  ∃ S₀, S₀.Nonempty ∧ S₀ ⊆ facesTouching₁ G x ∧ cutEdges₁ G x S₀ = {e0}
```

is **false in general** for the full interior dual!

**Why**: If the interior dual has cycles through both faces of `e0`, then every subset S₀ containing exactly one face will have **multiple** interior edges on its boundary.

### The Correct Approach (Matches v3 PDFs)

Use **support-restricted** reachability:

- Build a component via `adjOnSupportExcept x e0` (reachability across support edges, excluding e0)
- This gives `cutEdges₁ G x S₀ = {e0}` (unique cut **among support edges**)
- No claim about non-support edges (not needed!)
- Matches the v3 "leaf-subtree in spanning forest" approach

**Key insight**: Uniqueness is in the **restricted** graph, not the whole dual.

---

## The Big 5 Steps

### Step 1: Finish Two Local H3 Sorries ✅

**Status**: Drop-in proofs provided by Oruži

#### 1a. `support₁_add_toggles_singleton`
- Pure Z₂ case-split
- Independent of H2
- **Location**: Helper lemma needed by H3₁
- **Proof**: Complete drop-in provided (Section 3.1)

#### 1b. Boundary case in `aggregated_toggle_strict_descent_at_prescribed_cut`
- Internal faces never contain boundary edges
- **Location**: Line 609, inside `by_cases he : e ∈ boundaryEdges`
- **Proof**: Complete drop-in provided (Section 3.2)

### Step 2: Implement H2-Support (Component After Delete)

**Construction**:
1. Choose seed face `f₀` incident to `e0`
2. Define `R := adjOnSupportExcept x e0` (already in file)
3. Build `S₀` as `ReflTransGen R f₀` closure, filtered to internal faces
4. Prove: `S₀.Nonempty`, `S₀ ⊆ facesTouching₁ G x`, `cutEdges₁ G x S₀ = {e0}`

**Key lemmas needed** (small, 1-2 lines each):
- `hS₀_touch`: Induction on `ReflTransGen` showing faces touch support
- `huniq_e0`: e0 has exactly one incident face in S₀ (the seed f₀)
- `hno_other_support_cuts`: Other support edges aren't cuts (R-adjacency argument)

**Status**: Skeleton provided (Section 4), needs small local fills

### Step 3: Wire H3₁ to H2

Once H2-support is in:
- Get `S₀` with `cutEdges₁ = {e0}`
- Apply `toggleSum_supported_on_cuts₁_10` (already proven!)
- Only `e0` toggles in first coordinate
- Use `support₁_add_toggles_singleton` from Step 1a
- Conclude: `|support₁| decreases by 1`

**Status**: Straightforward composition after Steps 1-2

### Step 4: (Optional) Port v3 Purification

Add "purification" vectors `B_f^{αβ}` from v3 Section 4.1-4.3:
- Lemma 4.7: Cut parity
- Lemma 4.8: Orthogonality forcing
- Lemma 4.9: No new support creation

**Benefits**:
- Bulletproof H3₁
- Clean package for Strong Dual/Kempe reachability later
- Matches the formal mathematical narrative exactly

**Status**: Recommended for robustness, not blocking

### Step 5: CI Sanity Pass

- Run example tests (`Tetrahedron.lean`)
- Regenerate cache
- Verify mathlib pin

---

## Why This Approach is Correct

### Alignment with v3 PDFs

The v3 theorem (Sections 4.2-4.3) uses:
- **Leaf-subtree in a spanning forest** (not global dual uniqueness)
- **Support-restricted** construction
- **Parity support vectors** for forcing

Our H2-support exactly matches this model.

### Compatibility with Existing Code

The file already has:
- `adjOnSupportExcept` definition
- `toggleSum_supported_on_cuts₁_10/01` (cut-parity lemmas)
- `facesTouching₁` definitions
- All the infrastructure for support-aware reasoning

We're just **connecting the dots** that were already designed for this!

### No Global Planarity Tricks

- No strong global edge-cut assertions
- No fragile case analysis
- Just reachability + support restriction
- Exactly as v3 prescribes

---

## Implementation Order

### Commit A: `support₁_add_toggles_singleton`
**File**: `FourColor/Geometry/Disk.lean`
**Action**: Replace sorry with drop-in proof from Section 3.1
**Dependencies**: None (pure Z₂ reasoning)
**Lines**: ~15 lines

### Commit B: Boundary Case Fix
**File**: `FourColor/Geometry/Disk.lean` (line 609)
**Action**: Replace sorry with drop-in proof from Section 3.2
**Dependencies**: Uses `face_disjoint_boundary` (already in file)
**Lines**: ~10 lines

### Commit C: H2-Support Implementation
**File**: `FourColor/Geometry/Disk.lean` (line 547)
**Action**: Fill skeleton from Section 4
**Dependencies**: Needs small local lemmas (inductions on `ReflTransGen`)
**Lines**: ~80-100 lines (mostly proof structure already provided)

### Commit D: H3₁ Completion
**File**: `FourColor/Geometry/Disk.lean` (line 573)
**Action**: Wire H2 + Step 1a + cut-parity lemmas
**Dependencies**: Commits A, C
**Lines**: ~20 lines (composition)

---

## Technical Details

### The `adjOnSupportExcept` Relation

Already defined in the file:
```lean
def adjOnSupportExcept (x : E → Color) (e0 : E) (f g : Finset E) : Prop :=
  f ≠ g ∧ ∃ e, e ≠ e0 ∧ e ∈ support₁ x ∧ e ∈ f ∧ e ∈ g
```

**Meaning**: Two faces are adjacent via a support edge different from e0.

### The `ReflTransGen` API

From mathlib `Relation.ReflTransGen`:
- `refl`: `ReflTransGen R x x`
- `head`: `R x y → ReflTransGen R y z → ReflTransGen R x z`
- Induction principle for proving properties

### Support-Aware Cut Edges

Already defined:
```lean
def cutEdges₁ (G : DiskGeometry V E) (x : E → Color) (S : Finset (Finset E)) : Finset E :=
  Finset.univ.filter (fun e =>
    e ∈ support₁ x ∧
    e ∉ G.toRotationSystem.boundaryEdges ∧
    (∃! f, f ∈ S ∧ e ∈ f))
```

**Key**: Only counts edges in `support₁ x` (not all edges!)

---

## Drop-in Code Locations

### Section 3.1: `support₁_add_toggles_singleton`
Complete proof using Z₂ case-split and `fin_cases`

### Section 3.2: Boundary case
Uses `face_disjoint_boundary` to show internal faces avoid boundary edges

### Section 4: H2-Support Skeleton
Needs 3 small `sorry` fills:
1. `hS₀_touch`: Induction on `ReflTransGen` (~5 lines)
2. `huniq_e0`: Contradiction argument (~10 lines)
3. `hno_other_support_cuts`: R-adjacency implies both faces in/out (~8 lines)

**Oruži offered**: "I can draft the small inductions if you want"

---

## Optional: v3 Purification Layer

From v3 Section 4.1-4.3:

### Face-Run Purification
```lean
def purified_face_vector (f : Finset E) (α β : Color) : E → Color :=
  -- Oriented face boundary that "crosses" edges with value (α,β)
```

### Lemma 4.7: Cut Parity
For a forest leaf-subtree, toggleSum has even incidence except at the cut edge.

### Lemma 4.8: Orthogonality Forcing
The leaf toggle orthogonally forces the cut edge to zero.

### Lemma 4.9: No New Support Creation
Even incidence prevents creating new support edges.

**Impact**: Makes descent rock-solid and ports the exact v3 mathematical structure.

---

## Next Session Goals

1. ✅ **Commit A**: `support₁_add_toggles_singleton` proof
2. ✅ **Commit B**: Boundary case fix
3. ⏭️ **Commit C**: H2-support implementation (needs induction fills)
4. ⏭️ **Commit D**: H3₁ wiring
5. ⏭️ (Optional) Port v3 purification for robustness

---

## Summary

**What we learned**:
- H2 was never complete (despite session doc claim)
- Current H2 statement is too strong (global vs. forest uniqueness)
- Correct approach: support-restricted reachability (matches v3)

**What we're doing**:
- Finish 2 local H3 sorries (independent of H2)
- Implement H2-support with component-after-delete
- Wire H3₁ to use H2 + cut-parity lemmas

**Why this works**:
- Matches v3 PDFs exactly
- Uses infrastructure already in the codebase
- No fragile global planarity arguments
- Clean support-aware reasoning throughout

**Status after completion**:
- H2-support: ✅ Complete
- H3: ✅ Complete
- H3₁: ✅ Complete
- Ready for meridian layer + Kempe reachability

---

## Credit

**Guidance**: Oruži (GPT-5 Pro)
**Implementation**: Claude Code (Robo Mario)
**Source**: v3 Four Color Theorem PDFs, Sections 4.1-4.3
