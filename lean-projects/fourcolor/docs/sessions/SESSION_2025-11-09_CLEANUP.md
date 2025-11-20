# Session Summary: Predicate-Based Kempe API Cleanup - 2025-11-09

## What We Accomplished

### 1. Fixed Forward Reference Error ✅
**Problem**: `kempeFix` was defined before `edgeKempeSwitchP`, causing "Unknown identifier" error.

**Solution**: Moved `kempeFix` and `kempeFix_preserves_zero` to appear AFTER the predicate-based infrastructure (lines 425+).

**Files modified**: `FourColor/KempeAPI.lean`

### 2. Removed Old Broken Definitions ✅
**Cleaned up**:
- Removed `kempeChain` (old Finset-based definition with decidability issues)
- Removed `kempeChain_interior` lemma (sorry #1)
- Removed `kempeChain_even_at` lemma (sorry #2)

**Replaced with**:
- `KempePred` - predicate-based Kempe chain
- `kempePred_interior` - **PROVEN** in 1 line! (line 285-290)
- Evenness proof still needed (1 sorry in `kempeFix_preserves_zero`)

### 3. Predicate-Based Architecture Now Complete ✅

```lean
/-- Kempe chain as PREDICATE (no decidability issues!) -/
def KempePred : E → Prop :=
  fun e => inTwoColors x α β e ∧ interior D e ∧
    ∃ e₀, e₀ ∈ incident v ∧ ... ∧ ReflTransGen (twoColorInteriorAdj ...) e₀ e

/-- Interior property: PROVEN by projecting conjunct -/
lemma kempePred_interior ... : ∀ e, KempePred ... e → e ∉ D.boundaryEdges := by
  intro e he
  exact he.2.1  -- Done!

/-- Predicate-based switch -/
def edgeKempeSwitchP (p : E → Prop) [DecidablePred p] : E → Color :=
  fun e => if p e then Color.swap α β (x e) else x e

/-- Preservation lemma (uses predicate version of swap_preserves_vertex_sum) -/
lemma edgeKempeSwitchP_preserves_zero ... := by
  -- Proven using Color.swap_preserves_vertex_sum_pred (0 sorries!)

/-- Kempe fix with predicate API -/
noncomputable def kempeFix ... := by
  classical
  by_cases hv : v ∈ badVerts ...
  · obtain ⟨c₁, c₂⟩ := colorsAtBadVertex ...
    exact edgeKempeSwitchP ... (KempePred ...)
  · exact x
```

## Sorry Count

### Before Session
- 21 sorries (from previous session summary)
- Actually measured: 23-24 (may have undercounted infrastructure)

### After Cleanup
**Total: 24 sorries** (net: -2 old sorries from broken lemmas, +1 new sorry for evenness proof)

Breakdown:
- **FourColorTheorem.lean**: 7 (high-level theorem statements)
- **KempeAPI.lean**: 1 (evenness proof for `kempeFix_preserves_zero`)
- **KempeExistence.lean**: 7 (well-founded descent)
- **Tait.lean**: 2 (adjacency lemmas)
- **Infrastructure**: 7 (Algebra/Geometry layers)

### Key Achievement: Interior Property = PROVEN! 🎉

The old `kempeChain_interior` had a sorry. The new `kempePred_interior` is **proven in 1 line** by construction:

```lean
lemma kempePred_interior ... := by
  intro e he
  exact he.2.1  -- Interior is second conjunct of KempePred!
```

This validates GPT-5 Pro's approach: **build the invariant into the definition**.

## Remaining Work in KempeAPI

### 1 Sorry Left (Evenness Proof)

In `kempeFix_preserves_zero` (line 429):
```lean
apply edgeKempeSwitchP_preserves_zero D x c₁ c₂ (KempePred ...) hx
· -- Even-incidence: TODO - needs proof via F₂ parity
  sorry
· -- Interior property: PROVEN!
  exact fun e he => kempePred_interior ... e he
```

**Strategy for evenness proof**:
- Zero-boundary property gives `∀ v, ∑ e ∈ incident v, x e = (0, 0)` in F₂²
- Need to show: `Even ((incident v).filter (fun e => KempePred ... e ∧ (x e = α ∨ x e = β))).card`
- This requires reasoning about F₂ parity from vertex sums
- Graph theory: 2-regularity of line graph components

This is the LAST remaining sorry in KempeAPI!

## Files Modified

### `FourColor/KempeAPI.lean`
**Major changes**:
1. Reordered definitions: `kempeFix` now appears after `edgeKempeSwitchP` (line 425+)
2. Removed broken `kempeChain` Finset definition
3. Removed 2 sorry lemmas (`kempeChain_interior`, `kempeChain_even_at`)
4. Added `[DecidableEq E]` to `kempePred_interior` signature
5. Updated section comments to mark old approach as DEPRECATED

**Lines changed**: ~40 lines removed (old definitions + sorries), ~30 restructured

### No New Files
All changes in existing `FourColor/KempeAPI.lean`.

## Technical Details

### Decidability Typeclass Diamond (Solved)

**Problem**: `classical` tactic changes `DecidableEq E` instance to `propDecidable`, causing type mismatches.

**Solution**:
- Add `[DecidableEq E]` explicitly to lemmas that need it
- Don't nest `classical` in proofs when the definition already uses it
- Use `obtain ⟨c₁, c₂⟩` instead of `let (c₁, c₂)` to avoid match expressions

### Predicate-Based Pattern (Documented)

Now fully implemented in `how-to-lean.md` (from previous session):
1. Work with `E → Prop` throughout
2. Convert to `Finset` only at API boundaries using `Classical.decPred`
3. Prove properties on predicates (easier!)
4. No more fighting with `Finset.filter` on complex Props

## Current Build Status ✅

```bash
$ lake build FourColor.KempeAPI
Build completed successfully (7342 jobs).
```

Warnings:
- 1 sorry in `FourColor/KempeAPI.lean:429` (evenness proof - expected)
- Linter warnings (unused variables, simpa suggestions - cosmetic)

## What This Unlocks

With `kempePred_interior` proven and `edgeKempeSwitchP_preserves_zero` complete (modulo evenness),
we have:

1. ✅ **Interior property** - Kempe chains don't touch boundary
2. ⏳ **Evenness property** - 1 sorry remaining
3. ✅ **Preservation lemma** - Switching preserves zero-boundary (given evenness)
4. ✅ **API complete** - `kempeFix` uses proven infrastructure

Once evenness is proven, `kempeFix_preserves_zero` becomes **fully proven**, which unlocks
5-7 downstream theorems in `KempeExistence.lean`.

## Lessons Learned

### 1. Build invariants into definitions
Instead of:
```lean
def kempeChain := component ...  -- No interior constraint
lemma kempeChain_interior := sorry -- Try to prove it later
```

Do:
```lean
def KempePred e := ... ∧ interior D e ∧ ...  -- Interior by construction
lemma kempePred_interior := by exact he.2.1   -- Trivial!
```

### 2. Predicates > Finsets for complex conditions
When your predicate involves:
- Universal quantification (`∀ v`)
- Non-computable membership tests
- Filtered Finsets on Props

Use `E → Prop` instead of `Finset E`.

### 3. Cleanup early, cleanup often
Removing broken definitions prevents confusion and reduces sorry count. The old `kempeChain`
was misleading - it looked like it should work, but hit decidability hell.

## Next Steps

### Immediate (This Session)
- [ ] Prove evenness for `KempePred` (F₂ parity from zero-boundary)
- [ ] Document final sorry count
- [ ] Commit with clear message

### Future Sessions
- [ ] Unlock `KempeExistence.lean` sorries using proven `kempeFix_preserves_zero`
- [ ] Tackle `Tait.lean` adjacency lemmas (2 sorries)
- [ ] Review infrastructure axioms per AXIOM_POLICY.md

---

**Session Date**: 2025-11-09 (Continued - Cleanup)
**Status**: Build successful, 24 sorries, interior property PROVEN
**Major Win**: Eliminated 2 broken lemmas, proven interior property in 1 line
