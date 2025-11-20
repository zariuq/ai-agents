# Axiom Audit - 2025-11-10

## Objective

Systematically review all axioms in `FourColor/Tait.lean` to determine:
1. Which are genuine mathematical facts (OK as axioms)
2. Which should be definitions (following GPT-5 guidance)
3. Which can be proven from existing infrastructure

---

## Current Axioms in Tait.lean

### 1. `twoColorUnion_is_even_cycles` (line 240)
**Type**: Mathematical theorem placeholder
**Status**: ✅ OK as axiom (for now)
**Reason**: Returns `True` - this is a placeholder for a genuine mathematical theorem about two-color unions forming even cycles. Will need real implementation later.
**Action**: None (intentional placeholder)

---

### 2. `parity_sum_cycle_zero` (line 254)
**Type**: Mathematical theorem
**Status**: ✅ OK as axiom
**Reason**: This states that XOR sum around any cycle is (0,0). This is REAL mathematical content requiring proof from F₂ parity theory. Not a definition.
**Action**: None (genuine axiom)

---

### 3. `adj_iff_shared_edge` (line 303)
**Type**: Parameter constraint
**Status**: ⚠️ Questionable - consider refactoring
**Reason**: This constrains the parametric `adj` relation to match shared-edge semantics. With `primalAdj` now available as a canonical definition, this axiom is mainly for backward compatibility.
**Recommendation**:
- Keep for now (backward compatibility)
- Consider refactoring code to use `primalAdj` directly
- Eventually could eliminate this in favor of `primalAdj`
**Action**: Document as "compatibility axiom" for parametric `adj`

---

### 4. `no_multi_edges` (line 331)
**Type**: Foundational graph assumption
**Status**: ⚠️ SHOULD BE DERIVED from `WellFormed.no_parallel`
**Reason**: This states that two vertices share at most one edge (simple graph property). The `WellFormed` structure already has `no_parallel` field that provides this.
**Issue**: Current formalization doesn't have `WellFormed` available in contexts where `no_multi_edges` is used.
**Recommendation**:
- **Option A**: Refactor to pass `WellFormed` structure through the code
- **Option B**: Keep as axiom but document that it's derivable from `WellFormed`
- **Option C**: Prove it from graph structure assumptions
**Action**: Add documentation noting derivability from `WellFormed.no_parallel`

---

### 5. `bridgeless_connected` (line 395)
**Type**: Graph theory theorem
**Status**: ✅ OK as axiom
**Reason**: This is a genuine theorem in graph theory: bridgeless finite graphs are connected. It's not a definition but a proven fact that would require significant graph theory infrastructure to prove.
**Action**: None (genuine axiom representing real mathematical content)

---

### 6. `pathXORSum_concat` (line 692)
**Type**: Compositional property
**Status**: ⚠️ PROVABLE but technically complex
**Reason**: This states that path XOR distributes over concatenation. It IS provable from the recursive definition of `pathXORSum` through structural induction, but the proof requires careful handling of `List.Chain'` proofs.
**Current status**: Documented as provable, kept as axiom for pragmatic reasons
**Action**: Already documented with justification

---

### 7. `pathXORSum_path_independent` (line 711)
**Type**: Deep mathematical theorem
**Status**: ✅ OK as axiom
**Reason**: This requires proving cycle parity (XOR sum around cycle = 0), which depends on `parity_sum_cycle_zero`. This is real mathematical content, not definitional.
**Action**: None (genuine axiom)

---

## Summary

| Axiom | Classification | Should Change? | Action |
|-------|---------------|----------------|---------|
| `twoColorUnion_is_even_cycles` | Placeholder | No | Intentional placeholder |
| `parity_sum_cycle_zero` | Mathematical theorem | No | Genuine axiom |
| `adj_iff_shared_edge` | Parameter constraint | Maybe | Consider refactoring to use `primalAdj` |
| `no_multi_edges` | Foundational assumption | Yes | Should derive from `WellFormed` or prove |
| `bridgeless_connected` | Graph theorem | No | Genuine axiom |
| `pathXORSum_concat` | Provable property | No | Pragmatically kept as axiom (documented) |
| `pathXORSum_path_independent` | Mathematical theorem | No | Genuine axiom |

---

## Priority Recommendations

### HIGH PRIORITY: Refactor `no_multi_edges`

**Current State**: Added as axiom to prove `adj_unique_edge`

**Problem**: The formalization already has `WellFormed.no_parallel` which provides this property. We're duplicating assumptions.

**Solutions** (in order of preference):

1. **Best**: Refactor code to thread `WellFormed` structure through
   - Update `ThreeEdgeColoring` to include `WellFormed` constraint
   - Update `adj_unique_edge` to take `WellFormed` parameter
   - Prove `no_multi_edges` as lemma from `WellFormed.no_parallel`
   - **Impact**: Cleaner architecture, no redundant axioms
   - **Effort**: 2-3 hours of refactoring

2. **Good**: Prove `no_multi_edges` from existing structure
   - Search for existing assumptions about edge structure
   - May be implicit in `Endpoints.distinct` or incident relation
   - **Impact**: Eliminate 1 axiom
   - **Effort**: 1-2 hours

3. **Acceptable**: Document clearly that `no_multi_edges` is derivable
   - Add comment linking to `WellFormed.no_parallel`
   - Note this is a "simplifying axiom" that could be eliminated
   - **Impact**: Honest documentation
   - **Effort**: 5 minutes

### MEDIUM PRIORITY: Consider `adj_iff_shared_edge` refactoring

**Current State**: Axiom constraining parametric `adj` relations

**Now that we have**: `primalAdj` as canonical definition

**Opportunity**: Gradually migrate code to use `primalAdj` directly instead of parametric `adj`

**Benefits**:
- No axiom needed for `primalAdj` (it's a definition)
- Properties proven, not assumed
- Clearer semantics

**Effort**: 3-4 hours of refactoring throughout codebase

---

## GPT-5 Pattern Applied

Following "don't use axioms to pin down what a definition should be":

✅ **Correctly applied**:
- `primalAdj` is a definition, not an axiom
- Properties of `primalAdj` are proven lemmas
- Clear separation between definitions and theorems

⚠️ **Room for improvement**:
- `no_multi_edges` should be derived, not axiomatized
- `adj_iff_shared_edge` could be eliminated in favor of `primalAdj`

---

## Comparison: Before vs After This Session

### Before
- `adj_symm`: axiom
- `adj_unique_edge`: axiom
- No `primalAdj` definition
- 7 axioms total

### After
- `adj_symm`: ✅ proven lemma (3 lines)
- `adj_unique_edge`: ✅ proven lemma (from `no_multi_edges`)
- `primalAdj`: ✅ definition with 3 proven properties
- `no_multi_edges`: axiom (should be derived)
- 7 axioms total (but 2 are now proven, 1 new axiom added)

**Net**:
- Eliminated 2 axioms by proving them
- Added 1 axiom (`no_multi_edges`) which should be derived
- Added 1 definition (`primalAdj`) with proven properties

---

## Next Steps

1. **Immediate**: Document `no_multi_edges` as derivable from `WellFormed` (5 min)
2. **Short-term**: Investigate proving `no_multi_edges` from existing structure (1-2 hrs)
3. **Medium-term**: Consider refactoring to use `WellFormed` throughout (2-3 hrs)
4. **Long-term**: Migrate from parametric `adj` to `primalAdj` where possible (3-4 hrs)

---

**Audit completed**: 2025-11-10
**Auditor**: Following GPT-5 Pro "definitions not axioms" guidance
**Result**: 1-2 axioms identified as candidates for elimination through refactoring

