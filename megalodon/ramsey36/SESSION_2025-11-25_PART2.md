# Ramsey(3,6) Session - Part 2: Numerical Facts & Cardinality
**Date**: 2025-11-25
**Goal**: Add concrete numerical facts and work on cardinality bijection lemmas

## Summary

Successfully expanded numerical infrastructure and attempted cardinality bijections.

## Task 1: Concrete Numerical Facts ✅ COMPLETED

### What Was Added to `numerical_facts.mg`

**nat_p lemmas** (8 proven):
- nat_p_4, nat_p_5, nat_p_12, nat_p_13, nat_p_14, nat_p_16, nat_p_17, nat_p_18

**Membership lemmas** (12 proven):
- nat_0_in_13, nat_4_in_5, nat_5_in_6, nat_4_in_6, nat_5_in_14, nat_4_in_14
- nat_4_in_13, nat_13_in_17, nat_4_in_18, nat_5_in_18, nat_4_in_17, nat_5_in_13

**Subset lemmas** (11 proven):
- nat_13_subset_17, nat_4_subset_5, nat_4_subset_13, nat_5_subset_14, nat_4_subset_14
- nat_5_subset_13, nat_13_subset_14, nat_14_subset_17, nat_4_subset_17
- nat_4_subset_18, nat_5_subset_18

### Pattern Used

All proofs follow the ordinal abstraction pattern discovered earlier:

**For membership** (m :e n):
```megalodon
Theorem nat_4_in_13 : 4 :e 13.
apply ordsuccI1 12 4.
(* ... mechanical ordsucc chain ... *)
exact nat_4_in_6.
Qed.
```

**For subsets** (m c= n):
```megalodon
Theorem nat_4_subset_13 : 4 c= 13.
exact nat_trans 13 nat_p_13 4 nat_4_in_13.
Qed.
```

**One-line proofs using nat_trans!** 🎯

### Total: 31 proven lemmas, ~185 lines

All compile cleanly ✓

## Task 2: Cardinality Bijections ⚠️ PARTIAL

### Attempted: `ordsucc_setminus_singleton_inside`

**Goal**: Prove `equip n (ordsucc n :\: {v})` when `v :e n`.

**Bijection function**: `f(x) = if x :e v then x else ordsucc x`

**Strategy**:
- Elements x < v stay as x
- Elements x ≥ v map to ordsucc x (shifting up, skipping v)

**Example** (n=5, v=2):
- Domain: {0,1,2,3,4}
- Target: {0,1,3,4,5} (ordsucc 5 \ {2})
- f: 0→0, 1→1, 2→3, 3→4, 4→5 ✓

**What was proven**:
- Structured the bijection with 3 parts (domain, injectivity, surjectivity)
- Started proving first part (domain correctness)

**Challenge encountered**:
- Proof term type mismatches in variable rewriting
- Issue with bound variable shadowing (`v` in theorem vs `v` in bijI)
- Megalodon's proof term construction for complex rewrites is subtle

**Status**: Kept as `Admitted` for now. The mathematical content is correct, but the proof term mechanics need more debugging time.

### Other Cardinality Lemmas

Still admitted:
- `ordsucc_setminus_singleton` - Related bijection
- `complement_card_sub` - Complement cardinality
- `disjoint_union_card` - Disjoint union cardinality
- `disjoint_union_sing_5` - Specific case for 5→6
- `partition_3_card` - 3-way partition cardinality
- `partition_18_vertex_neighbors_rest` - Specific for Ramsey proof

## Key Learnings

### 1. Concrete Numerical Facts Are Easy!

The ordinal abstraction pattern makes numerical facts trivial:
- Mechanical ordsucc chains for membership
- One-line nat_trans for subsets
- No complicated case analysis needed

**This aligns with existing Ramsey proofs** (Ramsey_3_3_6.mg uses same pattern).

### 2. Bijection Proofs Need More Care

Constructive bijection proofs in Megalodon require:
- Deep understanding of proof term structure
- Careful variable binding management
- Experience with rewrite tactics in nested contexts

**Not impossible, just needs more time and examples.**

### 3. Strategic Admission Is OK

Following the project guidance:
> "Don't let perfect be the enemy of good!"

The ordinal abstraction (numerical_facts.mg) is sufficient for degree bound reasoning. Full bijection proofs can come later when needed or when more expertise is available.

## File Status

### ✅ numerical_facts.mg (225 lines, ALL PROVEN)
- 31 numerical lemmas
- Comprehensive coverage for 0-18
- All using ordinal abstraction
- **Ready for use in proofs**

### ⚠️ cardinality_infrastructure.mg (297 lines, ~20 admits)
- Structure in place
- Key lemmas identified
- Bijection proofs need more work
- **Compiles cleanly, admits documented**

### ✅ ordinal_theory.mg (82 lines, ALL PROVEN)
- Gold standard reference
- Demonstrates the patterns

### ⚠️ arithmetic_core.mg (53 lines, 5 admits)
- Systematic approach documented
- Not needed for current work
- Can return to later

## Next Steps

### Immediate (What's Actually Needed)
1. **Use numerical_facts.mg** in degree bound proofs
2. **Test whether admits in cardinality_infrastructure.mg block progress**
3. **If blocked**: Focus on specific lemmas case-by-case
4. **If not blocked**: Continue with degree_lower_bound_4_kruger

### Optional (Nice to Have)
1. Study more Megalodon bijection examples
2. Return to prove ordsucc_setminus_singleton_inside properly
3. Build out full cardinality infrastructure
4. Prove arithmetic cancellation lemmas

### Strategic Priority

**Don't block on bijections!** The pattern from Ramsey_3_3_6.mg shows:
- Concrete numerical facts (✅ done)
- Ordinal transitivity (✅ proven in ordinal_theory.mg)
- Case analysis on finite sets (standard tactics)

This is sufficient for Ramsey(3,6) formalization.

## Bottom Line

**Task 1: ✅ Thoroughly completed** - 31 proven numerical lemmas, ready for use.

**Task 2: ⚠️ Partially attempted** - Bijection structure in place, proof mechanics need more time.

**Overall Progress**: Strong foundation of numerical facts using ordinal abstraction. Cardinality infrastructure documented and compiles. Ready to proceed with degree bound proofs!

---

**Files changed**: numerical_facts.mg (+161 lines), cardinality_infrastructure.mg (cleaned up)
**Commits**: 2 (arithmetic status documentation + numerical facts expansion)
**All files compile**: ✓
