# FourColor/Tait.lean and Related Files: Formalization Analysis

## 1. ZeroBoundaryData Structure

### Definition (Triangulation.lean, lines 790-793)
```lean
structure ZeroBoundaryData (V E : Type*)
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] where
  incident : V → Finset E
  boundaryEdges : Finset E
```

### What It Contains
- **`incident : V → Finset E`**: A function mapping each vertex to the set of edges incident to it
  - Represents the edge-vertex incidence relation
  - For a vertex v, `incident v` is the set of all edges touching v
  
- **`boundaryEdges : Finset E`**: A distinguished set of "boundary" edges
  - These are edges on the boundary of the region (in topological terms)
  - Acts as a constraint set for the zero-boundary condition

### Key Definitions Associated with ZeroBoundaryData

**isZeroBoundary** (Triangulation.lean, line 799):
```lean
def isZeroBoundary (x : E → Color) : Prop :=
  ∀ v : V, ∑ e ∈ D.incident v, x e = (0,0)
```
- Chain x vanishes (sums to (0,0)) at every vertex

**zeroBoundarySet** (Triangulation.lean, line 803):
```lean
def zeroBoundarySet : Set (E → Color) :=
  {x | D.isZeroBoundary x ∧ ∀ e ∈ D.boundaryEdges, x e = (0,0)}
```
- Chains that vanish on every vertex AND are zero on boundary edges
- This is the "kernel" of the algebraic/topological structure

---

## 2. Definition of "Interior" in the Four Color Theorem Proof

### Definition (KempeAPI.lean, lines 232-234)
```lean
def interior {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (D : ZeroBoundaryData V E) (e : E) : Prop :=
  e ∉ D.boundaryEdges
```

### Semantic Meaning
- An edge e is **interior** if it is NOT in the boundary edge set
- Simple complement: interior(e) := ¬(e ∈ boundaryEdges)
- This is used in Kempe chain definitions to ensure chains stay away from boundary

### Context in Proofs
In **KempeAPI.lean**, interior is used in:
- `twoColorInteriorAdj` (line 238-243): Adjacency relation that requires BOTH edges to be interior
- `KempePred` (line 250-256): Kempe chain predicate that includes interior as second component
- `kempePred_interior` (line 278-283): Lemma proving members of KempePred are interior

---

## 3. Existing Lemmas About Geometric Closure (Edge Relationships at Vertices)

### Key Lemma: `both_incident_edges_in_component` (Kempe/Edge.lean, lines 189-270)

**Statement**: If a Kempe chain component touches a vertex v, it contains both incident αβ-edges at v

```lean
lemma both_incident_edges_in_component
    (D : ZeroBoundaryData V E) (incident : V → Finset E) (x : E → Color)
    (ec : ThreeEdgeColoring incident) (hcubic : ∀ u, (incident u).card = 3)
    (v : V) (α β : Color) (hne : α ≠ β) :
    ∀ e, e ∈ ChainP D incident x v α β → e ∈ incident v →
    ∃ e', e' ∈ incident v ∧ e' ≠ e ∧ (x e' = α ∨ x e' = β) ∧
           ReflTransGen (twoColorAdj_int D incident x α β) e e'
```

### What This Says About Adjacent Edges
1. **At a cubic vertex v with 3 edges**: By `one_edge_of_each_color` (lines 54-153), exactly 1 edge has color α and exactly 1 has color β
2. **Direct adjacency**: If two edges share a vertex v and have colors α, β respectively, they are directly adjacent in the line graph (one step in `twoColorAdj_int`)
3. **Component connectivity**: If one αβ-edge at v is in the component, the other MUST be in the component (they're directly adjacent via v)

### Proof Structure
The proof uses:
- `one_edge_of_each_color` to establish exactly 1 α-edge and 1 β-edge at v
- Case split: if `e = e_α`, then provide `e_β` as the witness
- Direct construction of `twoColorAdj incident x α β e_α e_β` (the adjacency relation)
- Conversion to `twoColorAdj_int` by adding interior constraints
- Wrapping in `ReflTransGen.single` to show one-step reachability

---

## 4. Existing Lemmas About Graph Structure Preservation

### A. Interior-Preserving Adjacency: `chain_interior` (Kempe/Edge.lean, lines 37-51)

```lean
lemma chain_interior
    (D : ZeroBoundaryData V E) (incident : V → Finset E)
    (x : E → Color) (v : V) (α β : Color) :
    ∀ {e}, e ∈ ChainP D incident x v α β → e ∉ D.boundaryEdges
```

**Key Point**: Chain membership preserves interior property by induction on reachability
- Base: seed edge is interior
- Step: `twoColorAdj_int` requires interior on both endpoints, so reachable edges remain interior

### B. Two-Color Subgraph is Regular: `two_regular_at_v` (Kempe/Edge.lean, lines 157-183)

```lean
lemma two_regular_at_v
    (incident : V → Finset E) (ec : ThreeEdgeColoring incident) (v : V)
    (hcubic : ∀ u, (incident u).card = 3) :
    ((incident v).filter (fun e => ec.color e = EdgeColor.α ∨ ec.color e = EdgeColor.β)).card = 2
```

**What This Says**: When removing one color (γ), the remaining subgraph is 2-regular at each vertex
- Cubic property: 3 edges at each vertex
- Proper coloring: all 3 edges have different colors
- Exactly 1 α-edge, 1 β-edge, 1 γ-edge
- Removing γ leaves 2 edges (α ∪ β)

### C. One Edge Per Color: `one_edge_of_each_color` (Kempe/Edge.lean, lines 54-153)

```lean
lemma one_edge_of_each_color
    (incident : V → Finset E) (ec : ThreeEdgeColoring incident) (v : V)
    (hcubic : ∀ u, (incident u).card = 3) :
    ((incident v).filter (fun e => ec.color e = EdgeColor.α)).card = 1 ∧
    ((incident v).filter (fun e => ec.color e = EdgeColor.β)).card = 1 ∧
    ((incident v).filter (fun e => ec.color e = EdgeColor.γ)).card = 1
```

**Proof by Pigeonhole**: 3 edges, 3 colors, proper coloring → each color exactly once

---

## 5. Formalization of "Incident" Relationship

### Definition in WellFormed Structure (Tait.lean, lines 162-170)

```lean
structure WellFormed (V E : Type*)
    (incident : V → Finset E) (adj : V → V → Prop) (ends : Endpoints V E) : Prop :=
  (mem_iff : ∀ {v e}, e ∈ incident v ↔ v = ends.fst e ∨ v = ends.snd e)
  (no_parallel :
    ∀ {v e₁ e₂}, e₁ ∈ incident v → e₂ ∈ incident v → e₁ ≠ e₂ →
      (let other (e : E) : V := if v = ends.fst e then ends.snd e else ends.fst e
       ; other e₁ ≠ other e₂))
  (adj_iff_shared :
    ∀ {u v}, adj u v ↔ (∃ e, e ∈ incident u ∧ e ∈ incident v ∧ u ≠ v))
```

### How Incidence Is Formalized

**Three Components**:

1. **mem_iff**: Membership in incident set is equivalent to being an endpoint
   - `e ∈ incident v` ↔ `v ∈ {ends.fst e, ends.snd e}`

2. **no_parallel**: No two edges at the same vertex share the same other endpoint
   - Different edges at v have different neighbors (ensures simple graph structure)

3. **adj_iff_shared**: Vertex adjacency defined through edge incidence
   - Two vertices are adjacent iff they share an edge
   - `adj u v` ↔ `∃ e, e ∈ incident u ∧ e ∈ incident v`

### Incidence in Kempe Definitions (KempeAPI.lean)

**edgeAdj** (line 126-128): Line graph adjacency
```lean
def edgeAdj {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (incident : V → Finset E) (e e' : E) : Prop :=
  e ≠ e' ∧ ∃ v, e ∈ incident v ∧ e' ∈ incident v
```
- Two edges are adjacent if they share a vertex (line graph definition)

**twoColorAdj** (line 131-137): Two-color edge adjacency
```lean
def twoColorAdj {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (incident : V → Finset E) (x : E → Color) (α β : Color)
    (e e' : E) : Prop :=
  edgeAdj incident e e' ∧
  (x e = α ∨ x e = β) ∧
  (x e' = α ∨ x e' = β) ∧
  x e ≠ x e'
```
- Additionally requires the edges have complementary αβ-colors (alternating)

---

## 6. Safe Assumptions About Adjacent Edges at a Vertex

### Based on Formalization Patterns, We Can Safely Assume:

#### A. **Two Adjacent Edges at a Cubic Vertex in a Proper 3-Edge-Coloring**

If edges e₁ and e₂ both belong to `incident v` at a cubic vertex v with proper 3-edge-coloring:

1. **They have different colors**: e₁ ≠ e₂ ∧ (incident v).card = 3 ∧ proper_coloring → ec.color e₁ ≠ ec.color e₂
   - Source: `ThreeEdgeColoring.proper` (Tait.lean, line 223)

2. **They directly represent different neighbors**: By `no_parallel` property
   - If e₁, e₂ ∈ incident v, then other(e₁) ≠ other(e₂)
   - Source: `WellFormed.no_parallel` (Tait.lean, line 165-168)

3. **They are 1-step adjacent in the line graph**: ∃ v, e₁ ∈ incident v ∧ e₂ ∈ incident v
   - Source: `edgeAdj` definition (KempeAPI.lean, line 126)

4. **If both are in a Kempe chain component, they're in the same 2-regular subgraph**:
   - Source: `both_incident_edges_in_component` lemma (Kempe/Edge.lean, line 189)

#### B. **Interior Property Closure**

If e₁ is interior and belongs to a Kempe chain component starting from v:

1. **All reachable edges in the component are interior**: 
   - By `chain_interior` (Kempe/Edge.lean, line 37)
   - Reachability through `ReflTransGen twoColorAdj_int` preserves interior

2. **Interior doesn't propagate to boundary through the adjacency relation**:
   - `interior D e` means `e ∉ D.boundaryEdges`
   - `twoColorAdj_int` requires interior on both endpoints, so can't reach boundary
   - Source: Definition of `twoColorAdj_int` (Kempe/Edge.lean, line 23-25)

#### C. **Evenness Properties for Two-Color Subgraphs**

For edges colored in two colors (α, β) only at a vertex v in a cubic 3-edge-coloring:

1. **Exactly 2 edges have the two colors combined**:
   - By `two_regular_at_v` lemma
   - Source: Kempe/Edge.lean, line 160

2. **Both are directly adjacent to each other via vertex v**:
   - By pigeonhole and `one_edge_of_each_color`
   - One α-edge and one β-edge at v
   - Both share vertex v, so `edgeAdj` holds

3. **Any component touching v contains both**:
   - By `both_incident_edges_in_component`
   - If one is reachable from v, the other is too (one step away)

#### D. **Parity/Cycle Closure**

For closed paths (cycles) in proper 3-edge-colorings:

1. **Color parities are equal**: count(α) ≡ count(β) ≡ count(γ) (mod 2)
   - Source: `color_parities_equal_on_cycle` (Tait.lean, line 576-624)

2. **Two-color cycles have even counts for each color**:
   - Source: `even_counts_on_twoColor_cycle` (Tait.lean, line 506-560)
   - Proof: alternation at each vertex forces even length

3. **Path XOR sum is zero on any cycle**:
   - Source: `parity_sum_cycle_zero` (Tait.lean, line 638-699)
   - Ensures potential function is well-defined

---

## Summary: Safe Formalization Assumptions

The formalization patterns in Tait.lean and related files support:

1. **Incident edges at a cubic vertex with proper 3-coloring are always distinguishable** by both color and neighbor
2. **Interior property is preserved along reachability** in the line graph
3. **Two-color subgraphs at vertices are 2-regular** (exactly 2 edges per color pair)
4. **Adjacent edges (at same vertex) in different colors are always 1-step connected** in any component
5. **Closure via even parity**: Color counts in cycles satisfy parity equality, not individual evenness
6. **Boundary edges are excluded** from interior-preserving adjacency relations, making Kempe operations safe

These properties form the mathematical foundation for the Tait proof that cubic bridgeless planar graphs are 3-edge-colorable.
