# Question for GPT-5 Pro: Kempe Chain Evenness Proof

## Context

We're formalizing the Four Color Theorem in Lean 4. We've successfully implemented a **predicate-based Kempe chain API** that avoids decidability issues, and proven the **interior property** in 1 line.

**ONE SORRY REMAINS** in the core Kempe API: proving that Kempe chains have **even incidence** at every vertex.

## What We Have (All Proven - 0 Sorries!)

### 1. Zero-Boundary Property
```lean
structure InZero (D : ZeroBoundaryData V E) (x : E → Color) : Prop where
  isZeroBoundary : ∀ v : V, ∑ e ∈ D.incident v, x e = (0, 0)  -- Sum in F₂²
  boundaryZero : ∀ e ∈ D.boundaryEdges, x e = (0, 0)
```

### 2. Kempe Chain Predicate (With Interior Built-In!)
```lean
def KempePred (incident : V → Finset E) (D : ZeroBoundaryData V E)
    (x : E → Color) (v : V) (α β : Color) : E → Prop :=
  fun e =>
    (x e = α ∨ x e = β) ∧               -- Edge is colored α or β
    e ∉ D.boundaryEdges ∧               -- Interior edge
    ∃ e₀, e₀ ∈ incident v ∧              -- Seed edge at vertex v
          (x e₀ = α ∨ x e₀ = β) ∧
          e₀ ∉ D.boundaryEdges ∧
          ReflTransGen (twoColorInteriorAdj incident D x α β) e₀ e

-- twoColorInteriorAdj is line graph adjacency restricted to αβ-interior edges
def twoColorInteriorAdj (incident : V → Finset E) (D : ZeroBoundaryData V E)
    (x : E → Color) (α β : Color) (e e' : E) : Prop :=
  edgeAdj incident e e' ∧              -- Share a vertex in original graph
  (x e = α ∨ x e = β) ∧
  (x e' = α ∨ x e' = β) ∧
  e ∉ D.boundaryEdges ∧
  e' ∉ D.boundaryEdges
```

### 3. Color Swap Preservation (PROVEN!)
```lean
lemma swap_preserves_vertex_sum_pred
    (x : E → Color) (p : E → Prop) [DecidablePred p] (α β : Color)
    (even_at : ∀ v : V, Even ((incident v).filter (fun e => p e ∧ (x e = α ∨ x e = β))).card) :
  ∀ v, ∑ e ∈ incident v, x e
      = ∑ e ∈ incident v, (if p e then swap α β (x e) else x e)
```

This is **fully proven** using F₂ arithmetic!

### 4. Interior Property (PROVEN!)
```lean
lemma kempePred_interior ... :
    ∀ e, KempePred incident D x v α β e → e ∉ D.boundaryEdges := by
  intro e he
  exact he.2.1  -- Second conjunct of KempePred!
```

## What We Need (THE LAST SORRY!)

```lean
lemma kempeFix_preserves_zero ... (hx : InZero D x) :
    InZero D (kempeFix D x v) := by
  ...
  apply edgeKempeSwitchP_preserves_zero D x c₁ c₂ (KempePred D.incident D x v c₁ c₂) hx
  · -- Even-incidence at each vertex:
    sorry  -- ← THIS IS THE ONLY REMAINING SORRY!
  · -- Interior property:
    exact fun e he => kempePred_interior ...  -- ✓ PROVEN
```

**Goal type of the sorry**:
```lean
∀ w : V, Even ((D.incident w).filter (fun e => KempePred D.incident D x v c₁ c₂ e ∧ (x e = c₁ ∨ x e = c₂))).card
```

**Simplifies to** (because `KempePred` already includes `x e = c₁ ∨ x e = c₂`):
```lean
∀ w : V, Even ((D.incident w).filter (fun e => KempePred D.incident D x v c₁ c₂ e)).card
```

## Mathematical Intuition

### Line Graph Component Structure
- Kempe chain = connected component in **line graph** of αβ-interior edges
- Two edges adjacent in line graph ⟺ they share a vertex in original graph
- Connected components in line graphs have **2-regular** structure on their support

### F₂ Parity Argument
- Zero-boundary: `∀ v, ∑ e ∈ incident v, x e = (0, 0)` in F₂²
- Colors are elements of F₂² = {(0,0), (1,0), (0,1), (1,1)}
- For two specific colors α, β, the count of edges colored α or β at vertex v has some parity
- **Question**: Does zero-boundary imply even count of αβ-edges at each vertex?

## The Question for GPT-5 Pro

**Given**:
1. Graph with edge coloring `x : E → F₂²`
2. Zero-boundary property: `∀ v, ∑ e ∈ incident v, x e = (0, 0)` in F₂²
3. Two specific colors `α, β ∈ F₂²`
4. Kempe chain `K` = connected component of αβ-edges (reachable via shared vertices)

**Prove**: For every vertex `w`, the number of Kempe chain edges incident to `w` is **even**.

### Sub-questions:

**Q1 (Direct F₂ approach)**:
Can we prove evenness directly from the zero-boundary property using F₂ arithmetic?

For example, if we know `∑ e ∈ incident w, x e = (0, 0)`, can we deduce that
`|{e ∈ incident w : x e ∈ {α, β}}|` is even?

**Q2 (Line graph regularity approach)**:
Is the standard proof via **2-regularity** of connected components in line graphs?

The argument would be:
- In a line graph, each edge connects to edges that share its endpoints
- A connected component forms a 2-regular graph on its edge support
- 2-regular ⟹ even degree at every vertex in original graph

**Q3 (Which approach works in Lean 4?)**:
Which proof strategy is **easiest to formalize** in Lean 4?
- Direct F₂ calculation (algebraic)
- Graph-theoretic (2-regularity lemmas)
- Some other clever argument?

**Q4 (Concrete proof sketch)**:
Please provide a **detailed proof sketch** for Lean 4, showing:
- What lemmas we need to prove first
- The main proof structure
- Any non-trivial steps that need careful formalization

## Available Lean 4 Infrastructure

### From Mathlib
- `ReflTransGen` (reflexive transitive closure)
- `Finset.sum`, `Finset.filter`, `Finset.card`
- `Even n` (decidable predicate)
- F₂ arithmetic via `ZMod 2`
- Standard graph theory (limited)

### From Our Codebase
- `edgeAdj incident e e'` (edges share a vertex)
- `boundaryEdges`, `incident v` (graph structure)
- All the F₂ lemmas in `Triangulation.lean` (swap preservation, etc.)

### What We DON'T Have (Yet)
- Explicit "2-regularity of line graph components" lemma
- Component decomposition of line graphs
- Path/cycle enumeration for Kempe chains

## Desired Output

Please provide:

1. **Mathematical proof** (informal but rigorous)
2. **Proof strategy** for Lean 4 (which lemmas to build)
3. **Concrete Lean 4 code sketch** for the main lemma
4. **Any "gotchas"** about formalizing this (decidability, finiteness, etc.)

## Why This Matters

Once this evenness proof is complete:
- ✅ `kempeFix_preserves_zero` will be **fully proven** (0 sorries!)
- ✅ Unlocks 5-7 downstream theorems in `KempeExistence.lean`
- ✅ Core Kempe switching infrastructure = **COMPLETE**

This is **THE CRUX** of the whole formalization. Everything else builds on this.

---

**Thank you, GPT-5 Pro!** 🙏

This is the last piece of the Kempe API puzzle. Your monotone invariant approach already gave us the interior property for free. Now we need your insight on the evenness proof!
