# GPT-5 Pro Guidance on Axioms vs Definitions

## Core Principle

**"Don't use axioms for things that are really just definitions."**

## The Pattern

When you see:
```lean
axiom Foo_spec : ∀ …, Foo … ↔ (explicit property)
```

Replace with:
```lean
def Foo (…params…) : Prop := (explicit property)

@[simp] lemma Foo_iff : Foo … ↔ (explicit property) := Iff.rfl
```

Then prove properties as lemmas:
```lean
lemma Foo_symm : Foo a b → Foo b a := by ...
```

---

## Analysis of Tait.lean Axioms

### ✅ `adj_symm` - CORRECTLY ELIMINATED
**Was**: `axiom adj_symm`
**Now**: `lemma adj_symm` proved from `adj_iff_shared_edge`

**Status**: DONE - this follows the pattern

---

### ⚠️ `adj_iff_shared_edge` - KEEP AS AXIOM (for now)
**Current**:
```lean
axiom adj_iff_shared_edge
    (incident : V → Finset E) (adj : V → V → Prop) (u v : V) :
    adj u v ↔ (∃ e, e ∈ incident u ∧ e ∈ incident v ∧ u ≠ v)
```

**Why keep it**:
- `adj` is a PARAMETER, not something we define
- This axiom constrains what `adj` relations are acceptable
- It's saying "we only work with adj relations that match this characterization"

**Alternative approach** (if we controlled the graph structure):
```lean
structure CubicGraph (V E : Type*) where
  incident : V → Finset E
  -- Define adj based on shared edges
  adj (u v : V) : Prop := ∃ e, e ∈ incident u ∧ e ∈ incident v ∧ u ≠ v

-- Then adj_iff_shared_edge becomes Iff.rfl
```

**TODO**: Check if we can refactor to have a concrete `CubicGraph` structure

---

### ✅ `pathXORSum` - CORRECTLY MADE INTO DEF
**Was**: `axiom pathXORSum : ... → Bool × Bool`
**Now**: `noncomputable def pathXORSum : ... → Bool × Bool := ...`

**Status**: DONE - definition compiles

---

### ⚠️ `pathXORSum_single_edge` - PROPERTY PROOF BLOCKED
**Current**: `axiom` → changed to `lemma` but has `sorry`

**Blocker**: Need to prove `getEdgeBetween` returns the edge `e` passed in
**Root cause**: `adj_iff_shared_edge` only guarantees ∃, not ∃!

**Solution needed**:
1. Either add uniqueness to `adj_iff_shared_edge`:
   ```lean
   adj u v ↔ (∃! e, e ∈ incident u ∧ e ∈ incident v ∧ u ≠ v)
   ```

2. Or prove it from cubic graph properties (degree 3 implies uniqueness)

3. Or add as lemma:
   ```lean
   lemma adj_unique_edge (cubic : IsCubic incident) (hadj : adj u v) :
     ∃! e, e ∈ incident u ∧ e ∈ incident v
   ```

---

### ⚠️ `pathXORSum_concat` - PROPERTY PROOF TODO
**Status**: Still axiom, should be provable from recursive definition

**Strategy**: Induction on path structure, use:
- Base: concat with empty path
- Step: `pathXORSum (u :: v :: rest) = edge_color(u,v) + pathXORSum (v :: rest)`

---

### ⚠️ `pathXORSum_path_independent` - DEEP THEOREM
**Status**: Still axiom

**This is NOT definitional** - it's a real theorem requiring:
- Cycle parity (XOR sum around cycle = (0,0))
- Path difference forms a cycle
- Therefore two paths between same endpoints have same XOR sum

**Decision**: May be OK to keep as axiom OR requires proving cycle parity first

---

## Application to pathXORSum

**What we did RIGHT**:
1. ✅ Made `pathXORSum` a `def` not an axiom
2. ✅ Defined Bool × Bool XOR operation
3. ✅ Implemented recursive structure

**What's BLOCKED**:
- Property proofs need either:
  - Uniqueness of shared edge (∃! not just ∃)
  - OR proof that `Classical.choose` gives the "right" edge (same color)

**Recommendation**:
1. Add `adj_unique_edge` lemma (provable from cubic property)
2. Prove `getEdgeBetween_spec`: returns an edge satisfying the adj predicate
3. Then complete property proofs

---

## Summary

| Axiom | Should be | Status | Action |
|-------|-----------|--------|--------|
| `adj_symm` | lemma | ✅ DONE | Proved from adj_iff_shared_edge |
| `adj_iff_shared_edge` | axiom OK | ⚠️ KEEP | Parameter constraint, not definition |
| `pathXORSum` | def | ✅ DONE | Implemented recursively |
| `pathXORSum_single_edge` | lemma | ⚠️ BLOCKED | Need uniqueness of edge |
| `pathXORSum_concat` | lemma | ❌ TODO | Prove by induction |
| `pathXORSum_path_independent` | axiom/theorem | ❌ DEEP | Requires cycle parity |

**Next priority**: Add `adj_unique_edge` lemma to unblock pathXORSum properties

---

**Created**: 2025-11-10
**Source**: GPT-5 Pro advice on axiom vs definition pattern
**Application**: Four Color Theorem formalization
