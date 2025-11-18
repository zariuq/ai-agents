# How to Lean 4 - Local Knowledge Base

## Handling Conditional Expressions in Proofs

### The Problem
When working with `if-then-else` expressions in proofs, tactics like `simpa` and `simp` don't always fully evaluate nested conditionals, especially when you have expressions like:
```lean
if condition1 then value1 else if condition2 then value2 else value3
```

### The Solution: Use `if_pos` and `if_neg` Explicitly

**Key Theorems**:
- **`if_pos (h : c)`**: Rewrites `(if c then t else e)` to `t` given proof `h : c`
- **`if_neg (h : ¬c)`**: Rewrites `(if c then t else e)` to `e` given proof `h : ¬c`
- **`dif_pos` and `dif_neg`**: Similar theorems for dependent if-then-else (`dite`)

### Example Usage

```lean
-- Given: hu₂ : coloring.color u = c₂
-- Goal: Simplify (if coloring.color u = c₁ then c₂ else if coloring.color u = c₂ then c₁ else coloring.color u)

-- Step 1: Prove the first condition is false
have h_u_not_c1 : coloring.color u ≠ c₁ := by
  intro h
  have : c₁ = c₂ := by rw [← h, hu₂]
  sorry -- Need proof that c₁ ≠ c₂

-- Step 2: Apply if_neg to eliminate first branch, then if_pos for second
rw [if_neg h_u_not_c1, if_pos hu₂] at hEq
-- Now the expression simplifies to: c₁
```

### When to Use

**Use `if_pos`/`if_neg` when**:
- You have nested conditionals
- `simpa` or `simp` leaves conditional expressions unsimplified
- You need precise control over which branch is taken

**Prefer `simpa`/`simp` when**:
- Simple, flat conditionals
- Lean can automatically decide the condition

### Related Tactics

- **`split_ifs`**: Splits the goal into cases for each condition (generates multiple goals)
- **`by_cases`**: Manual case split on a proposition

## Proving Inequality of Inductive Constructors

### The Problem
When you have an inductive type like:
```lean
inductive VertexColor
  | red | blue | green | yellow
```

You need to prove that distinct constructors are unequal (e.g., `red ≠ blue`).

### The Solution: Use `nomatch` or Constructor Injectivity

**Method 1: Direct contradiction** (for simple types)
```lean
theorem red_ne_blue : VertexColor.red ≠ VertexColor.blue := by
  intro h
  cases h
```

**Method 2: Using decidable equality**
```lean
-- If the type has DecidableEq instance:
example : c₁ ≠ c₂ := by decide
```

**Method 3: Pattern matching in term mode**
```lean
theorem red_ne_blue : VertexColor.red ≠ VertexColor.blue :=
  fun h => nomatch h
```

### Common Pattern in This Project

When proving `c₁ ≠ c₂` given evidence they should be different:
```lean
have h_not_eq : c₁ ≠ c₂ := by
  intro h
  -- h : c₁ = c₂
  -- Now derive contradiction from context
  cases c₁ <;> cases c₂ <;> try contradiction
  -- Or use context-specific facts
```

## Symmetric Adjacency Relations

### The Problem
Graph adjacency relations may not be explicitly symmetric in the type signature.

### The Solution
Add `Symmetric adj` as a hypothesis when needed:
```lean
theorem graph_property (adj : V → V → Prop) (adj_symm : Symmetric adj) : ... := by
  -- Now can use: adj_symm : ∀ u v, adj u v → adj v u
```

### Using Symmetry
```lean
-- Given hadj : adj u w, need adj w u
have hadj_rev : adj w u := adj_symm hadj
```

## Working with `ReflTransGen` (Transitive Closure)

### Constructor Usage
**Correct pattern** for the `tail` constructor:
```lean
-- ReflTransGen.tail : ReflTransGen R a b → R b c → ReflTransGen R a c
have reach : ReflTransGen.tail path_to_b edge_b_to_c
```

**Not**:
```lean
-- WRONG: Don't use ReflTransGen for the last step
have reach : ReflTransGen.tail path_to_b (ReflTransGen.single edge_b_to_c)
```

The `tail` constructor takes:
1. A path from `a` to `b` (type: `ReflTransGen R a b`)
2. A single step from `b` to `c` (type: `R b c`)
3. Returns a path from `a` to `c`

### Induction on ReflTransGen: Use head_induction_on

**The Problem**: Standard `induction` on `ReflTransGen` struggles with variable naming:
```lean
-- WRONG: Hard to name intermediate variables
induction h_path with
| tail hab hbc ih => -- What is the intermediate node?
  -- Variables a✝, b✝ auto-generated - can't reference them!
```

**The Solution**: Use `Relation.ReflTransGen.head_induction_on` with `rename_i`:

```lean
-- CORRECT: Use head_induction_on helper
induction h_path using Relation.ReflTransGen.head_induction_on with
| refl =>
  -- Base case: a = b
  ...
| head h_step h_rest IH =>
  -- Lean auto-generates: a✝ → c✝ (via h_step), c✝ ~>* b (via h_rest)
  rename_i a' c  -- Name the auto-generated variables
  -- Now: h_step : R a' c,  h_rest : ReflTransGen R c b
  cases h_step with
  | ... => ...
```

**Why This Works**:
- `head_induction_on` works backward from the endpoint (natural for path reasoning)
- `rename_i` captures auto-generated metavariables in order (`a✝`, `c✝` → `a'`, `c`)
- You get clean variable names without fighting the elaborator

**Complete Example** (from SpanningForest.lean):
```lean
lemma path_must_use_new_edge {α : Type*} {R S : α → α → Prop} {a b : α}
    (h_path : ReflTransGen (fun x y => R x y ∨ S x y) a b)
    (h_not_R : ¬ ReflTransGen R a b) :
    ∃ x y, ReflTransGen R a x ∧ S x y ∧ ReflTransGen (fun x y => R x y ∨ S x y) y b := by
  induction h_path using Relation.ReflTransGen.head_induction_on with
  | refl =>
    exfalso
    exact h_not_R .refl
  | head h_step h_rest IH =>
    rename_i a' c
    cases h_step with
    | inl h_R =>
      by_cases h_R_rest : ReflTransGen R c b
      · exfalso; exact h_not_R (.head h_R h_R_rest)
      · obtain ⟨x, y, h_cx, h_Sxy, h_yb⟩ := IH h_R_rest
        exact ⟨x, y, .head h_R h_cx, h_Sxy, h_yb⟩
    | inr h_S =>
      exact ⟨a', c, .refl, h_S, h_rest⟩
```

**Key Tactics**:
- **`rename_i`** - Names anonymous metavariables (`a✝`, `b✝`) in order of appearance
- **`head_induction_on`** - Mathlib helper for backward induction on paths
- **`trans_induction_on`** - Alternative helper for 3-case induction (refl/single/trans)

**Resources**:
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Relation.html
- Search tip: "Lean 4 ReflTransGen induction" finds helper functions

## Common Patterns

### Equality Chain
```lean
-- To prove a ≠ c from a = b and b ≠ c:
have : a ≠ c := ne_of_eq_of_ne hab hbc  -- where hab : a = b, hbc : b ≠ c
```

### Symmetry of Equality
```lean
-- h : a = b, need b = a
have : b = a := h.symm
-- Or use Eq.symm h
```

### Contradiction from Reflexivity
```lean
-- Given h : a ≠ a (impossible), derive any goal
exact absurd rfl h
```

## Let-bindings and Type Unification Issues

**Problem**: When a structure field uses an inline `let` binding, Lean won't unify it with your separate `let` binding, even if syntactically identical.

**Example**:
```lean
structure WellFormed where
  no_parallel : ... →
    (let other := fun e => if v = ends.fst e then ends.snd e else ends.fst e
     ; other e₁ ≠ other e₂)

-- In proof:
let other := fun e => if v = ends.fst e then ends.snd e else ends.fst e
have h := wf.no_parallel he₁ he₂ hne  -- TYPE ERROR!
```

**Solution**: Inline definitions completely, or work directly with the structure's let-binding without introducing your own.

## Threading Invariants Through WellFounded.fix

### The Problem
`WellFounded.fix` expects a step function of type:
```lean
∀ x, (∀ y, y < x → motive y) → motive x
```

But you have an invariant `P x` that you need to maintain through the recursion, and `WellFounded.fix` doesn't support dependent elimination where the step function can take `(x : A) (h : P x)`.

### The Solution: Use Subtype

**Pattern**:
```lean
-- Instead of working on A directly, work on { x : A // P x }
let SubType := { x : A // P x }
let measure : SubType → ℕ := fun ⟨x, _⟩ => measure_on_A x

-- Lift well-foundedness to subtype
have wf_subtype : WellFounded (fun (a b : SubType) => measure a < measure b) := by
  apply InvImage.wf measure wellFounded_lt

-- Step function now has access to invariant
have step : ∀ (xh : SubType),
  (∀ yh : SubType, measure yh < measure xh → ...) → ... := by
  intro ⟨x, hP⟩ IH
  -- Now hP : P x is available!
  ...

-- Apply WellFounded.fix on subtype
have result := WellFounded.fix wf_subtype step ⟨x₀, hP₀⟩
```

### Real Example from Four Color Project

Threading zero-boundary property through well-founded descent:

```lean
-- Want: colorings that are zero-boundary AND have nonempty support
let ZBColorings := { x : E → Color // x ∈ zeroBoundarySet ∧ (supp x).Nonempty }

have step : ∀ (xh : ZBColorings), ... := by
  intro ⟨x, hx, hnz⟩ IH  -- Get both invariants for free!
  -- Can now use hx and hnz in the step
  ...
  -- When making recursive call, must prove invariants hold
  let x' := kempeFix x v
  have hx' : x' ∈ zeroBoundarySet := ...  -- Prove invariant preserved
  have hnz' : (supp x').Nonempty := ...   -- Prove invariant preserved
  exact IH ⟨x', hx', hnz'⟩ hlt
```

### When to Use
- You have an invariant that must hold at every step of recursion
- The invariant is preserved by your recursive step
- Standard `WellFounded.fix` can't access the invariant hypothesis

## ZMod 2 Arithmetic (F₂)

### Decidability is Your Friend

For `ZMod 2`, use decidability to solve goals automatically:

```lean
lemma F2_add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> decide
```

The `fin_cases` tactic generates one goal per constructor (0 and 1), then `decide` solves each computationally.

### Characteristic-2 Identities

Key properties of F₂ (ZMod 2):
- **`a + a = 0`** (everything is its own additive inverse)
- **`2 * a = 0`** (doubling gives zero)
- **Automatic cancellation**: `a + (a + b) = b`

### Proving with Extensionality

For product types like `Color = F₂ × F₂`, use `ext` to reduce to component-wise goals:

```lean
lemma swap_identity (α β : Color) : β = α + (α + β) := by
  ext  -- Split into two goals: β.1 = ... and β.2 = ...
  · show β.1 = α.1 + (α.1 + β.1)
    rw [← add_assoc, F2_add_self, zero_add]
  · show β.2 = α.2 + (α.2 + β.2)
    rw [← add_assoc, F2_add_self, zero_add]
```

### Omega for Natural Number Arithmetic

When you need arithmetic facts about natural numbers:

```lean
have : k + 1 + (k + 1) = k + k + 2 := by omega
```

The `omega` tactic solves linear arithmetic over integers/naturals.

## Pattern: Even Number Induction

When proving something for all even `n`:

```lean
lemma even_property {n : ℕ} (h : Even n) : P n := by
  rcases h with ⟨k, rfl⟩  -- n = 2*k, but written as k + k
  induction k with
  | zero =>
    -- Base case: n = 0
    ...
  | succ k ih =>
    -- Step: given P(2k), prove P(2(k+1)) = P(2k + 2)
    have : k + 1 + (k + 1) = k + k + 2 := by omega
    rw [this]
    -- Use ih : P(2k) and properties of 2
    ...
```

**Key insight**: Lean represents `2*k` as `k + k`, so destructing `Even n` gives `⟨k, rfl⟩` where `n = k + k`.

## Decidability and Finset.filter

### The Problem

When using `Finset.filter` with a predicate, you need decidability for the predicate. Error messages like:

```
error: typeclass instance problem is stuck, it is often due to metavariables
```

often indicate missing decidability instances.

### The Solution: Minimal Type Signatures

**DON'T** use complex type signatures with many type parameters:
```lean
-- WRONG: Too many type parameters confuses typeclass resolution
def myFilter {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (x : E → Color) (c₁ c₂ : Color) : Finset E :=
  Finset.univ.filter (fun e => x e = c₁ ∨ x e = c₂)  -- ERROR!
```

**DO** use minimal type signatures - only what you actually need:
```lean
-- CORRECT: Only include types actually used in the signature
def myFilter {E : Type*} [Fintype E] [DecidableEq E]
    (x : E → Color) (c₁ c₂ : Color) : Finset E :=
  Finset.univ.filter (fun e => x e = c₁ ∨ x e = c₂)  -- Works!
```

### Why This Works

Lean 4 automatically provides decidability for:
- **Equality** on types with `DecidableEq` instance
- **Disjunction** via built-in `instDecidableOr`
- **Conjunction** via built-in `instDecidableAnd`
- **Negation** via built-in `instDecidableNot`

So `x e = c₁ ∨ x e = c₂` is automatically decidable when:
1. `Color` has `DecidableEq` (it does - it's `F₂ × F₂`)
2. The type signature is simple enough for typeclass resolution

### When You Need Custom DecidablePred

For custom predicates that Lean can't auto-synthesize:

```lean
-- Define your predicate
def myPred : MyType → Prop := ...

-- Provide decidability instance
instance : DecidablePred myPred
| constructor1 => Decidable.isTrue (proof_it_holds)
| constructor2 => Decidable.isFalse (proof_it_fails)

-- Now Finset.filter works
def filtered := Finset.univ.filter myPred
```

### Real Example from This Project

**Before (broken)**:
```lean
noncomputable def kempeChain_overapprox
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (x : E → Color) (c₁ c₂ : Color) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => x e = c₁ ∨ x e = c₂)
  -- ERROR: typeclass instance problem stuck
```

**After (works)**:
```lean
def kempeChain_overapprox {E : Type*} [Fintype E] [DecidableEq E]
    (x : E → Color) (c₁ c₂ : Color) : Finset E :=
  Finset.univ.filter (fun e => x e = c₁ ∨ x e = c₂)
  -- Compiles perfectly!
```

### Key Insight

**Simpler type signatures = easier typeclass resolution**

If you only use `E` in your definition, don't include `V` in the signature. Lean's typeclass system works better with minimal signatures.

### Related Pattern: Using Filtered Results

Once you have a filtered Finset, simp lemmas work naturally:

```lean
@[simp] lemma mem_myFilter (e : E) :
    e ∈ myFilter x c₁ c₂ ↔ (x e = c₁ ∨ x e = c₂) := by
  simp [myFilter]  -- Just works!
```

### When Classical Doesn't Help

**Common mistake**: Adding `classical` or `noncomputable` to force decidability.

**Reality**: These don't provide decidability instances - they just allow non-constructive proofs. For `Finset.filter`, you need actual decidability instances.

**Solution**: Fix the type signature, let Lean auto-synthesize instances.

## Predicates vs Finsets: The Nuclear Option

When decidability issues are **completely blocking** your work (complex `Prop` chains, universal quantification, etc.), switch to a **predicate-based architecture**.

### The Problem That Can't Be Fixed

Sometimes `Finset.filter` on a `Prop` predicate is fundamentally blocked:

```lean
-- This will NEVER work if strictlyInterior chains non-computable Props
def strictlyInterior (D : ZeroBoundaryData V E) (e : E) : Prop :=
  ∀ v, e ∈ D.incident v → v ∉ boundaryVerts D

def badDefinition : Finset E :=
  Finset.univ.filter (fun e => strictlyInterior D e)  -- STUCK FOREVER
```

No amount of `classical`, `open Classical`, or `DecidablePred` instances will help.

### The Solution: Predicates All The Way

**Don't compute Finsets - work with predicates (`E → Prop`) directly:**

```lean
-- GOOD: Predicate version (purely logical, no decidability)
def KempePred (D : ZeroBoundaryData V E) (v : V) : E → Prop :=
  fun e =>
    interior D e ∧ inTwoColors x α β e ∧
    ∃ e₀, e₀ ∈ incident v ∧ interior D e₀ ∧
          ReflTransGen (adjacencyRelation ...) e₀ e

-- Finset wrapper ONLY for API compatibility (push to boundaries)
noncomputable def kempeChain (D : ZeroBoundaryData V E) (v : V) : Finset E :=
  @Finset.filter E (KempePred D v) (Classical.decPred _) Finset.univ
```

### Why This Works

1. **Predicates are Props** - no decidability required for logical reasoning
2. **Convert once at boundaries** - use `Classical.decPred _` only when absolutely necessary
3. **Proofs become trivial** - properties that are "by construction" really are:

```lean
lemma pred_interior (e : E) (h : KempePred D v e) : e ∉ D.boundaryEdges :=
  h.1  -- Interior is the FIRST CONJUNCT - one line proof!
```

### Pattern: Predicate-Based API

```lean
-- Step 1: Define relation as Prop
def myRelation (x y : α) : Prop := ...

-- Step 2: Define predicate using ReflTransGen for connectivity
def myPred (seed : α) : α → Prop :=
  fun a => property a ∧ ReflTransGen myRelation seed a

-- Step 3: Noncomputable wrapper ONLY if you need Finset
noncomputable def mySet (seed : α) : Finset α :=
  @Finset.filter α (myPred seed) (Classical.decPred _) Finset.univ

-- Step 4: Prove properties on the PREDICATE (no Finset hassles)
lemma myPred_property (a : α) (h : myPred seed a) : property a :=
  h.1  -- By definition!
```

### When to Use This

**Use predicate-based architecture when:**
- You've tried fixing decidability and failed repeatedly
- The predicate chains multiple non-computable `Prop`s
- You need universal quantification over `Fintype`
- Properties are "by construction" but Lean can't synthesize decidability

**Keep using Finsets when:**
- Predicates are simple (like `x = α ∨ x = β`)
- Type signatures are minimal
- You're not hitting typeclass synthesis issues

### Real Example: Four Color Project

**Before (broken)**:
```lean
-- Trying to filter on strictlyInterior - NEVER WORKS
def kempeChain : Finset E :=
  component.filter (fun e => strictlyInterior D e)  -- ERROR!
```

**After (works perfectly)**:
```lean
-- Predicate includes interior by definition
def KempePred : E → Prop :=
  fun e => interior D e ∧ ... ∧ ReflTransGen ...

-- Interior proof is TRIVIAL
lemma pred_interior : ∀ e, KempePred e → interior D e :=
  fun e h => h.1  -- Just project the conjunct!
```

### Trade-offs

**Pros:**
- Eliminates ALL decidability issues
- Proofs become trivial (properties by definition)
- Clean separation of logic (Prop) and computation (Finset)

**Cons:**
- Noncomputable (but you were already using `noncomputable` everywhere)
- Need to convert at API boundaries
- Slightly more verbose setup

### Key Insight

Lean 4's strict `Prop`/`Bool` separation means you **cannot always compute with Props**. When you hit that wall, **stop trying** - work in the logical world (`Prop`) and only touch the computational world (`Finset`) at boundaries.

This is **not a workaround** - it's the **correct architecture** for complex logical properties!

## Finset Maximum and Optimization

### The Problem: No Finset.argmax

**Common Issue**: You want to find an element of a `Finset` that maximizes some function, but `Finset.argmax` doesn't exist in mathlib!

### Solutions

#### Option 1: Use Finset.max' for Maximum Values (Recommended)

When you need an element with maximum value under some function:

```lean
-- Find a finset with maximum cardinality among candidates
let candidates : Finset (Finset E) := -- some nonempty finite set of finsets

have hNonempty : candidates.Nonempty := -- proof that candidates is nonempty

-- Get the maximum cardinality
let max_card := (candidates.image Finset.card).max'
  (Finset.Nonempty.image hNonempty _)

-- Extract an element achieving this maximum
have : ∃ T ∈ candidates, T.card = max_card := by
  have : max_card ∈ candidates.image Finset.card :=
    Finset.max'_mem _ _
  simp [Finset.mem_image] at this
  exact this

obtain ⟨T, hT_mem, hT_card⟩ := this
```

**Key Functions** (from `Mathlib.Data.Finset.Max`):
- **`Finset.max' (s : Finset α) (H : s.Nonempty) : α`** - Returns the maximum element
- **`Finset.max'_mem : s.max' H ∈ s`** - The maximum is in the set
- **`Finset.le_max' : x ∈ s → x ≤ s.max' H`** - All elements ≤ maximum
- **`Finset.max'_singleton : ({a} : Finset α).max' h = a`**

**Proof Pattern for Maximality**:
```lean
-- Prove that a max-cardinality element is maximal
have h_maximal : ∀ T' ∈ candidates, T'.card ≤ T.card := by
  intro T' hT'
  have : T'.card ∈ candidates.image Finset.card :=
    Finset.mem_image_of_mem _ hT'
  calc T'.card ≤ max_card := Finset.le_max' _ _ this
             _ = T.card := hT_card.symm
```

#### Option 2: Use Finset.sup for Supremum

When you need the supremum of values (works with any semilattice):

```lean
-- Example: maximum element in a finset of naturals
def max_nat (s : Finset ℕ) : ℕ := s.sup id

-- With a function
def max_value (s : Finset α) (f : α → ℕ) : ℕ := s.sup f
```

**Key Properties**:
- `Finset.sup_le : (∀ x ∈ s, f x ≤ b) → s.sup f ≤ b`
- `Finset.le_sup : x ∈ s → f x ≤ s.sup f`

#### Option 3: Induction on Maximum Value

For proving properties by building up sets with maximum values:

```lean
theorem my_property (s : Finset α) : P s := by
  apply Finset.induction_on_max_value (f := some_function)
  · -- Base case: P ∅
    sorry
  · -- Step: if P s and f a ≥ f x for all x ∈ s, then P (insert a s)
    intro a s ha_notin h_max_val hPs
    sorry
```

**Signature**:
```lean
theorem induction_on_max_value [DecidableEq ι] (f : ι → α)
    {p : Finset ι → Prop} (s : Finset ι)
    (h0 : p ∅)
    (step : ∀ a s, a ∉ s → (∀ x ∈ s, f x ≤ f a) → p s → p (insert a s)) :
    p s
```

### Why This Matters

The pattern "find a subset satisfying a property with maximum cardinality" is very common:
- Maximal independent sets
- Maximal acyclic subgraphs
- Maximal cliques
- Optimal colorings

**The key insight**: Maximum-cardinality subsets are automatically maximal!
- If you could add an element and preserve the property, you'd have a larger set
- This contradicts having maximum cardinality
- Therefore, you can't add any more elements → maximal! ✓

### Example: Finding Maximal Acyclic Subsets

```lean
lemma exists_maximal_acyclic :
    ∃ T : Finset E, isAcyclic T ∧ isMaximal T := by
  classical
  let candidates := (Finset.univ : Finset E).powerset.filter isAcyclic

  have hNonempty : candidates.Nonempty := by
    use ∅
    simp [isAcyclic]

  -- Get max cardinality
  let max_card := (candidates.image Finset.card).max'
    (Finset.Nonempty.image hNonempty _)

  -- Extract a candidate with this cardinality
  have : ∃ T ∈ candidates, T.card = max_card := by
    have := Finset.max'_mem _ _
    simp [Finset.mem_image] at this
    exact this

  obtain ⟨T, hT_mem, hT_card⟩ := this

  use T
  constructor
  · -- T is acyclic
    exact (Finset.mem_filter.mp hT_mem).2
  · -- T is maximal: can't add any element and stay acyclic
    intro e he_notin
    by_contra h_still_acyclic
    -- If insert e T is still acyclic, it has larger cardinality
    have : (insert e T).card = T.card + 1 :=
      Finset.card_insert_of_not_mem he_notin
    -- But T has maximum cardinality - contradiction!
    have : insert e T ∈ candidates := by simp [h_still_acyclic]
    have : (insert e T).card ≤ max_card :=
      Finset.le_max' _ _ (Finset.mem_image_of_mem _ ‹_›)
    omega
```

### Common Pitfalls

❌ **Don't**: Try to use `Finset.argmax` (doesn't exist)
❌ **Don't**: Convert to `List` unnecessarily (loses finset structure)
❌ **Don't**: Try to define custom argmax without `classical` mode

✅ **Do**: Use `Finset.max'` with nonemptiness proof
✅ **Do**: Use the maximum cardinality pattern for maximality proofs
✅ **Do**: Use `image` to map your optimization function to a finset of values

### Related Functions

- **`Finset.min'`** - Minimum element of nonempty finset (dual of max')
- **`Finset.inf`** - Infimum in a semilattice (dual of sup)
- **`Finset.image f s`** - Apply function f to all elements
- **`Finset.Nonempty.image`** - Nonemptiness preserved by image

## Type-Level Invariants and Subtypes

### The Architecture Pattern: Make Illegal States Unrepresentable

**Principle** (Mario Carneiro): Instead of carrying around proof obligations, encode invariants in the type system using subtypes.

### Example: Face Subtype Refactoring

**Before** - Proof obligations everywhere:
```lean
def isAcyclic (G : DiskGeometry V E) (tree_edges : Finset E) : Prop :=
  ∀ e ∈ tree_edges, ∀ (f g : Finset E),
    f ∈ G.toRotationSystem.internalFaces →  -- Proof obligation #1
    g ∈ G.toRotationSystem.internalFaces →  -- Proof obligation #2
    f ≠ g →
    e ∈ f → e ∈ g →
    ¬ Relation.ReflTransGen (fun f' g' => ...) f g
```

**After** - Type-level guarantee:
```lean
abbrev Face (G : DiskGeometry V E) :=
  {f : Finset E // f ∈ G.toRotationSystem.internalFaces}

def isAcyclic (G : DiskGeometry V E) (tree_edges : Finset E) : Prop :=
  ∀ e ∈ tree_edges, ∀ (f g : Face G),  -- ✅ Internal membership is AUTOMATIC!
    f ≠ g →
    e ∈ f.1 → e ∈ g.1 →  -- Use .1 to project to underlying Finset E
    ¬ Relation.ReflTransGen (fun f' g' => ∃ e' ∈ tree_edges, e' ≠ e ∧ e' ∈ f'.1 ∧ e' ∈ g'.1) f g
```

### Key Benefits

1. **Proof obligations eliminated**: When you extract `f : Face G`, you get `f.property : f.1 ∈ internalFaces` for free
2. **Less error-prone**: Can't accidentally use a non-internal face
3. **Cleaner proofs**: Focus on the actual logic, not bookkeeping

### Common Subtype Operations

```lean
-- Create a subtype value (need proof!)
have hf : f ∈ G.toRotationSystem.internalFaces := ...
let face : Face G := ⟨f, hf⟩

-- Project to underlying value
face.1  -- or face.val  -- gives the Finset E

-- Get the proof property
face.2  -- or face.property  -- gives proof that face.1 is internal

-- Prove subtype equality using underlying equality
have : face1 = face2 := Subtype.eq (proof_that_face1_val_eq_face2_val)
```

### When to Use Subtypes

✅ **Use subtypes when**:
- You have an invariant that appears in EVERY function/lemma
- Proof obligations clutter the actual mathematical reasoning
- The invariant is "structural" (e.g., membership, boundedness, well-formedness)

❌ **Don't use subtypes when**:
- The property only appears in a few lemmas
- You need to work with both satisfying and non-satisfying values frequently
- The property is complex and changes throughout the proof

## Debugging Typeclass Instance Resolution

### Problem: "typeclass instance problem is stuck, it is often due to metavariables"

This error means Lean can't infer the typeclass instances (like `DecidableEq`, `Membership`, etc.) because it has unresolved metavariables.

### Solution Toolkit

#### 1. Make Implicit Arguments Explicit

**Before** (stuck):
```lean
have h_eq := hunique_e _ ⟨hcard, hprops⟩  -- ❌ What is _?
```

**After** (works):
```lean
have h_eq := hunique_e {f', g'} ⟨hcard, hprops⟩  -- ✅ Explicit set
```

#### 2. Add Type Annotations to Lambdas

**Before** (stuck):
```lean
have h_sym : Symmetric (fun x y => ∃ e'' ∈ tree_edges, e'' ≠ e ∧ e'' ∈ x ∧ e'' ∈ y) := ...
-- ❌ Can't infer Membership E ?m.2289
```

**After** (works):
```lean
have h_sym : Symmetric (fun (x y : Finset E) => ∃ e'' ∈ tree_edges, e'' ≠ e ∧ e'' ∈ x ∧ e'' ∈ y) := ...
-- ✅ Type inference succeeds
```

#### 3. Add Explicit Type Ascriptions to Sets/Collections

**Before** (stuck):
```lean
have : {f', g'} = {f, g} := ...  -- ❌ What type of set?
```

**After** (works):
```lean
have : ({f', g'} : Finset (Finset E)) = ({f, g} : Finset (Finset E)) := ...
-- ✅ Finset typeclass instances can be inferred
```

#### 4. Name Hypotheses Instead of Chaining `this`

**Before** (can confuse elaborator):
```lean
have : ... := ...
have : ... := this
rw [this] at this  -- ❌ Which this?
exact this
```

**After** (clearer):
```lean
have h_eq : ... := ...
have h_mem : ... := h_eq
rw [h_eq] at h_mem
exact h_mem
```

### When to Apply These Techniques

**Red flags** that you need explicit type help:
- Error mentions "metavariables"
- Error mentions "stuck" or "cannot synthesize"
- Functions with `_` placeholders for implicit arguments
- Lambda functions in higher-order contexts
- Generic collection types (`Finset`, `Set`, `List`) without element type visible

**General principle**: Help the elaborator by being more explicit when it gets stuck. Think: "What would I need to know to infer these instances?"

## Converting Between Logical and Finset Forms

### Problem: Disjunction vs. Set Membership

Sometimes you have `x = a ∨ x = b` but need `x ∈ {a, b}`, or vice versa.

### Solution: Use `simp` to Convert

```lean
-- Disjunction → Set membership
have h_or : f.1 = f' ∨ f.1 = g' := ...
have h_in : f.1 ∈ ({f', g'} : Finset (Finset E)) := by
  simp; exact h_or  -- ✅ simp knows they're equivalent

-- Set membership → Disjunction
have h_in : f.1 ∈ ({f', g'} : Finset (Finset E)) := ...
simp at h_in  -- Now h_in : f.1 = f' ∨ f.1 = g'
```

### Why Not Manual Rewrite?

❌ **Don't do this**:
```lean
have h_or : f.1 = f' ∨ f.1 = g' := ...
rw [h_set_eq] at h_or  -- ❌ Error: Did not find an occurrence of the pattern
```

Rewriting doesn't work directly on disjunctions when the pattern appears inside the disjuncts.

✅ **Do this**:
```lean
have h_or : f.1 = f' ∨ f.1 = g' := ...
have h_in : f.1 ∈ ({f', g'} : Finset (Finset E)) := by simp; exact h_or
rw [h_set_eq] at h_in  -- ✅ Works on set membership
simp at h_in  -- Convert back to disjunction if needed
```

## Simplification Tactics: When to Use What

### The Hierarchy

1. **`simp`** - Let Lean figure it out
2. **`simp [lemma1, lemma2, ...]`** - Guide simp with specific lemmas
3. **Manual rewrites** - Last resort when simp can't help

### Example: Cardinality of 2-Element Sets

**Over-engineered** ❌:
```lean
have hcard : ({f', g'} : Finset (Finset E)).card = 2 := by
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  · norm_num  -- Or rfl, or ...
  · simp; exact hfg'_ne
```

**Let simp do the work** ✅:
```lean
have hcard : ({f', g'} : Finset (Finset E)).card = 2 := by
  simp [Finset.card_insert_of_notMem, hfg'_ne]
```

### Key Lesson

**Trust `simp` more!** It knows about:
- Set/finset cardinalities
- Membership in literal sets
- Basic arithmetic
- Logical equivalences

Only drop down to manual tactics when `simp` genuinely can't solve it.

### Common Patterns

```lean
-- Membership in literal finsets
simp  -- Converts {a, b}.card, x ∈ {a, b}, etc.

-- With specific lemmas
simp [Finset.card_insert_of_notMem, h_ne]

-- Clear hypothesis after simplification
simp at h

-- Simplify and close goal
simp [h1, h2]; exact h3  -- or just: simpa [h1, h2] using h3
```

## Working with Paths and Relations

### Projecting ReflTransGen Paths

When you have a path over a subtype and need a path over the underlying type:

```lean
-- Given: h_path : ReflTransGen R (a : Face G) (b : Face G)
-- Need:  path over Finset E (the underlying type of Face G)

-- Use Relation.ReflTransGen.lift to project
have h_path_finset : ReflTransGen (fun f'' g'' : Finset E => ...) a.1 b.1 := by
  apply Relation.ReflTransGen.lift (fun (f : Face G) => f.1) _ h_path
  intro x y h_rel
  -- Show that if R x y, then the projected relation holds for x.1 y.1
  exact ...
```

**Key point**: `Relation.ReflTransGen.lift` requires you to prove the relation is preserved under projection.

### Symmetric Relation Path Reversal

If your relation is symmetric, you can reverse paths:

```lean
-- Define relation
let R : α → α → Prop := fun x y => ∃ e ∈ edges, e ∈ x ∧ e ∈ y

-- Prove symmetry
have h_sym : Symmetric R := by
  intro x y ⟨e, hmem, hx, hy⟩
  exact ⟨e, hmem, hy, hx⟩  -- Just swap hx and hy

-- Reverse path
have h_path : ReflTransGen R a b := ...
have h_path_rev : ReflTransGen R b a :=
  rflTransGen_reverse_of_symmetric h_sym h_path
```

**Caveat**: Make sure `rflTransGen_reverse_of_symmetric` is available (may need import).

## References

- [Lean 4 Tactic Reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Mathlib4 Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Stack Exchange: Synthesizing decidability for Finset.filter](https://proofassistants.stackexchange.com/questions/4587/synthesizing-decidablity-for-finset-filter)
- GPT-5 Pro's predicate-based architecture (2025-11-09) - Four Color Project
