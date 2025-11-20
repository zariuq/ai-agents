# F₂ Parity Proof - Concrete Attack Plan

## The Goal (1 Lemma, 1 Sorry)

**File**: `FourColor/KempeAPI.lean`, line 320

```lean
lemma even_alphaBeta_incident
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (D : ZeroBoundaryData V E) (x : E → Color) (α β : Color)
    (hx : InZero D x) :
    ∀ w : V, Even ((D.incident w).filter (fun e => x e = α ∨ x e = β)).card := by
  classical
  intro w
  sorry
```

**Given**: `∑ e ∈ D.incident w, x e = (0, 0)` where `x e : Color = (ZMod 2) × (ZMod 2)`

**Prove**: `Even ((D.incident w).filter (fun e => x e = α ∨ x e = β)).card`

## Concrete Mathlib Lemmas You'll Need

Search for these in mathlib4:

```lean
-- Key conversion lemma (CONFIRMED exists in mathlib)
ZMod.eq_zero_iff_even : (n : ZMod 2) = 0 ↔ Even n

-- Sum manipulation
Finset.sum_partition : -- sum over partition equals sum of sums
Finset.filter_union : -- combine filters
Finset.card_union_of_disjoint : -- if disjoint, card (A ∪ B) = card A + card B

-- Scalar multiplication
nsmul_eq_zero : n • x = 0 → ...  (in ZMod 2 context)

-- Casting between Nat and ZMod 2
Nat.cast_add : (↑(n + m) : ZMod 2) = ↑n + ↑m
```

## Concrete Proof Sketch

### Step 1: Partition the incident edges by color

```lean
-- At vertex w, partition edges by their colors
set S_α := (D.incident w).filter (fun e => x e = α)
set S_β := (D.incident w).filter (fun e => x e = β)
set S_other := (D.incident w).filter (fun e => x e ≠ α ∧ x e ≠ β)

-- Goal set is S_α ∪ S_β
have : (D.incident w).filter (fun e => x e = α ∨ x e = β) = S_α ∪ S_β := by
  ext e; simp; tauto
```

### Step 2: Express the sum in terms of cardinalities

```lean
-- From hx, we have:
have hsum : ∑ e ∈ D.incident w, x e = (0, 0) := hz w

-- Rewrite as sum over color partitions:
have : ∑ e ∈ D.incident w, x e = S_α.card • α + S_β.card • β + (∑ e ∈ S_other, x e) := by
  sorry  -- Use Finset.sum_partition or similar
```

### Step 3: Work in coordinates (ZMod 2) × (ZMod 2)

The key insight: `α = (α.1, α.2)` and `β = (β.1, β.2)` where `.1, .2 : ZMod 2`

```lean
-- Extract first coordinate
have h1 : S_α.card • α.1 + S_β.card • β.1 + (∑ e ∈ S_other, (x e).1) = (0 : ZMod 2) := by
  have := congr_arg Prod.fst hsum
  simp at this
  exact this

-- Extract second coordinate similarly
have h2 : S_α.card • α.2 + S_β.card • β.2 + (∑ e ∈ S_other, (x e).2) = (0 : ZMod 2) := by
  have := congr_arg Prod.snd hsum
  simp at this
  exact this
```

### Step 4: Simplify in ZMod 2

In ZMod 2, we have `n • c = (n % 2) • c`, so:

```lean
-- In ZMod 2: (n : ZMod 2) • c = if Even n then 0 else c
have : S_α.card • α.1 = ((S_α.card : ZMod 2) : ZMod 2) • α.1 := by
  sorry  -- Nat.cast and scalar mult properties
```

### Step 5: Use the key fact

**If** we can show that in the sum equations, the terms force `S_α.card + S_β.card` to be even, then we're done.

The argument (GPT-5's hint): if α, β, and α+β are all distinct and non-zero, then looking at which coordinates are non-zero in each color gives us the constraints.

**THIS IS THE HARD PART** - the case analysis on which colors α, β are.

## Simpler Alternative: Assume α ≠ β, both nonzero

If you add hypotheses:
```lean
lemma even_alphaBeta_incident
    ... (hα : α ≠ (0,0)) (hβ : β ≠ (0,0)) (hαβ : α ≠ β) : ...
```

Then the proof might be easier because you can reason about which coordinates are affected.

## Concrete Next Actions for Opus

1. **Search mathlib4** for:
   - `rg "sum_partition" lake-packages/mathlib`
   - `rg "eq_zero_iff_even" lake-packages/mathlib`
   - `rg "card_union_of_disjoint" lake-packages/mathlib`

2. **Find similar proofs** in mathlib4 where people:
   - Partition a Finset by a property
   - Connect cardinalities to ZMod 2
   - Decompose sums in product types

3. **Start with the simplest case**:
   - Assume α = (1,0), β = (0,1) (the standard basis)
   - Prove it for this special case first
   - Then generalize

4. **Ask on Zulip** with this exact question:
   > "I have `∑ e : E, x e = (0,0)` where `x e : (ZMod 2) × (ZMod 2)`.
   > I want to prove `Even (#{e | x e ∈ {α, β}})` for given colors α, β.
   > What's the right way to decompose this sum by color classes and extract parity?"

## Why This Is Hard But Doable

**Hard**: Requires understanding ZMod 2 arithmetic, Finset sum manipulation, and product type decomposition.

**Doable**: All the pieces exist in mathlib4. It's a matter of finding the right lemmas and chaining them together.

**Estimated time**: 2-4 hours for someone experienced with mathlib4, possibly longer if learning as you go.

## The Payoff

Once this ONE lemma is proven, the rest cascade:
- `KempePred_equiv_on_alphaBeta_at` - ~30 lines (line graph adjacency)
- `kempePred_even_at` - ~40 lines (case analysis with L1 + L2)
- Nonzero properties - ~15 lines each (contradiction)

**Total: ~100-120 lines to complete the entire evenness proof after this blocker.**

---

**Bottom line**: Don't try to invent the wheel. Find the mathlib4 lemmas that do the heavy lifting, and chain them together. The math is sound - it's just a translation problem.
