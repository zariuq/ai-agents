# Smart Execution Plan: Dependency-Ordered Sorry Resolution

**Date**: 2025-11-06
**Strategy**: Bottom-up dependency order (à la Mario Carneiro)
**Goal**: Minimize rework, maximize each proof unlocking downstream proofs

---

## Dependency Graph Analysis

```
AXIOMS (Level 0 - No dependencies)
├── cubic_proper_coloring_missing_color
├── adj_iff_share_edge
└── adjacent_not_same_missing

BASIC LEMMAS (Level 1 - Depend on axioms)
├── tait_reverse final case → uses missing_color_injective ✅ (proven!)
├── kempeSwitch_proper cases → uses kempe_chain_colors ✅ (proven!)
└── adjacent_different_missing → uses axioms above

TAIT EQUIVALENCE (Level 2 - Needs Level 1)
├── tait_forward → needs adj_iff_share_edge + cubic axiom
└── four_color_equiv_tait → needs tait_forward + tait_reverse complete

DUAL INFRASTRUCTURE (Level 3 - Independent from Tait)
├── Dual graph construction → NEW INFRASTRUCTURE NEEDED
└── Dual-to-primal conversion → needs dual construction

KEMPE REACHABILITY (Level 4 - Needs Tait + Dual)
└── Kempe chain reachability → needs kempeSwitch_proper + dual graph

INTEGRATION (Level 5 - Everything else)
├── Apply Lemma 4.5 → connect to existing Triangulation.lean
├── Apply Strong Dual → connect to existing StrongDual.lean
└── Main theorem → orchestrates everything
```

---

## Optimal Execution Order

### **Phase 1: Prove Remaining Axioms** (Foundation)

**Why first**: These are leaves in the dependency graph - no dependencies, unlock everything else.

#### Task 1.1: `adj_iff_share_edge` ⭐ EASIEST
**File**: Tait.lean:152
**Lines**: ~15
**Dependencies**: None
**Unlocks**: `tait_forward`, `adjacent_different_missing`

```lean
axiom adj_iff_share_edge {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (incident : V → Finset E)
    (adj : V → V → Prop)
    (u v : V) :
    adj u v ↔ ∃! e, e ∈ incident u ∧ e ∈ incident v
```

**Strategy**: This is defining the adjacency relation. Should be provable from graph structure or take as additional hypothesis.

---

#### Task 1.2: `cubic_proper_coloring_missing_color` ⭐⭐ MEDIUM
**File**: Tait.lean:140
**Lines**: ~25
**Dependencies**: None
**Unlocks**: `tait_forward`, `adjacent_different_missing`, `tait_reverse`

```lean
axiom cubic_proper_coloring_missing_color {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (incident : V → Finset E)
    (cubic : IsCubic incident)
    (edge_coloring : @ThreeEdgeColoring V E _ _ incident)
    (v : V) :
    ∃! c : EdgeColor, c ∉ (incident v).image edge_coloring.color
```

**Strategy**:
- Vertex has degree 3 (cubic)
- 3 incident edges, 3 colors available
- Proper coloring → all 3 incident edges have different colors
- Therefore exactly one color is unused

**Proof sketch**:
1. `incident v` has cardinality 3 (from `IsCubic`)
2. Edge coloring is proper → 3 distinct colors used
3. Only 3 edge colors exist → exactly one missing

---

#### Task 1.3: `adjacent_not_same_missing` ⭐⭐⭐ HARDER
**File**: Tait.lean:164
**Lines**: ~30
**Dependencies**: `adj_iff_share_edge` (use shared edge), `cubic_proper_coloring_missing_color`
**Unlocks**: `adjacent_different_missing`

```lean
axiom adjacent_not_same_missing {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (incident : V → Finset E)
    (adj : V → V → Prop)
    (cubic : IsCubic incident)
    (edge_coloring : @ThreeEdgeColoring V E _ _ incident)
    {u v : V} (hadj : adj u v)
    {c : EdgeColor}
    (hcu : c ∉ (incident u).image edge_coloring.color)
    (hcv : c ∉ (incident v).image edge_coloring.color) :
    False
```

**Strategy**:
- u and v are adjacent → share edge e (from `adj_iff_share_edge`)
- u is missing color c → e is not colored c (since e ∈ incident u)
- v is missing color c → e is not colored c (since e ∈ incident v)
- But e must be colored something → e is colored c or not c
- If both miss c, and e connects them, then e must be colored c (only way for both to miss it)
- Contradiction!

**Wait, this needs more thought**:
- Actually: u misses c means u's 3 edges use the OTHER two colors
- v misses c means v's 3 edges use the OTHER two colors
- Shared edge e between them... hmm, e can't be colored c (or neither would miss it)
- But if u uses only 2 colors (not c) on 3 edges... that's impossible with proper coloring!
- **AH!** Proper means u's 3 edges are all different colors. So u MUST use all 3 colors. Contradiction.

**Corrected strategy**:
1. u has 3 incident edges with 3 distinct colors (proper + cubic)
2. Only 3 edge colors exist
3. Therefore u's edges use all 3 colors {α, β, γ}
4. Therefore u cannot be "missing" any color
5. Contradiction with hypothesis

**Actually this axiom might be FALSE as stated!** Let me reconsider...

---

### **Phase 2: Complete Tait Equivalence** (Core Theory)

#### Task 2.1: `tait_reverse` final case ⭐ TRIVIAL
**File**: Tait.lean:231
**Lines**: ~5
**Dependencies**: `missing_color_injective` ✅ (already proven!)
**Unlocks**: `four_color_equiv_tait`, main theorem

```lean
-- Line 253: This would be: apply missing_color_injective cu cv hne after establishing
--           that vertexColorOf u depends only on cu and vertexColorOf v depends only on cv
sorry
```

**Strategy**: Just apply the proven lemma. Trivial.

---

#### Task 2.2: `kempeSwitch_proper` case analyses ⭐⭐ TEDIOUS
**File**: Tait.lean:321, 347, 352
**Lines**: ~60 total
**Dependencies**: `kempe_chain_colors` ✅ (already proven!)
**Unlocks**: Kempe reachability

**Current state**: Structure in place, 3 sorries for case analysis

**Strategy**:
- Case 1 (both in K): Show swapping c₁ ↔ c₂ preserves distinctness
  - If both had c₁: contradiction (proper coloring)
  - If u had c₁, v had c₂: after swap u has c₂, v has c₁, still different
  - Other cases: unchanged colors remain different

- Case 2 (u in K, v not): u swaps, v unchanged → still different
- Case 3 (v in K, u not): symmetric

**Key lemma needed**: Color swap is injective on {c₁, c₂}

---

#### Task 2.3: `tait_forward` ⭐⭐⭐ MEDIUM-HARD
**File**: Tait.lean:116
**Lines**: ~40
**Dependencies**: `adj_iff_share_edge`, `cubic_proper_coloring_missing_color`
**Unlocks**: `four_color_equiv_tait`

**Strategy** (from comments):
```lean
-- Given 4-vertex-coloring of triangulation:
-- 1. For each edge e with endpoints colored c₁, c₂:
--    - Two colors used (c₁, c₂)
--    - Two colors unused
--    - Map unused pair to edge color deterministically
-- 2. Prove proper:
--    - At dual vertex (= primal face with 3 corners):
--    - 3 edges with different endpoint color pairs
--    - Map to 3 different edge colors
```

**Implementation**:
```lean
-- Color assignment: edge (u,v) gets color corresponding to "missing" colors
def edgeColorOf (e : E) : EdgeColor :=
  let u := endpoint₁ e
  let v := endpoint₂ e
  let used := {vertex_coloring.color u, vertex_coloring.color v}
  let unused := {VertexColor.red, .blue, .green, .yellow} \ used
  -- Map 2 unused colors to 1 edge color deterministically
  if VertexColor.red ∈ unused ∧ VertexColor.blue ∈ unused then EdgeColor.α
  else if VertexColor.red ∈ unused ∧ VertexColor.green ∈ unused then EdgeColor.β
  else if VertexColor.blue ∈ unused ∧ VertexColor.green ∈ unused then EdgeColor.γ
  else ... -- handle other cases

-- Prove proper: adjacent dual edges (= primal edges sharing a face vertex)
-- have different endpoint color pairs → map to different edge colors
```

---

### **Phase 3: Dual Graph Infrastructure** (New Code Needed)

#### Task 3.1: Dual Graph Construction ⭐⭐⭐⭐ DESIGN REQUIRED
**File**: FourColorTheorem.lean:60
**Lines**: ~80-100
**Dependencies**: Rotation system infrastructure
**Unlocks**: Dual-to-primal conversion, main theorem

**What's needed**:
```lean
structure DualGraph (G : Geometry.RotationSystem V E) where
  -- Dual vertices are primal faces
  dual_vertices : Finset (Finset E)  -- Each face is a set of edges

  -- Dual edges are primal edges (shared by 2 faces)
  dual_edges : E → Bool  -- True if interior edge

  -- Incidence: which edges are incident to which dual vertex (face)
  dual_incident : (Finset E) → Finset E

  -- Prove cubic: each internal face has degree 3 (for triangulation)
  dual_is_cubic : ∀ f ∈ dual_vertices, (dual_incident f).card = 3
```

**Strategy**:
- Use existing `internalFaces` from Disk geometry
- For triangulation: each internal face has 3 edges
- Define `dual_incident f = f` (face's edges are its incident edges in dual)
- Prove cubic from triangulation property

**This is the BIGGEST infrastructure gap!**

---

#### Task 3.2: Dual-to-Primal Conversion ⭐⭐⭐ DESIGN
**File**: FourColorTheorem.lean:109
**Lines**: ~50
**Dependencies**: Dual graph construction, `tait_reverse`
**Unlocks**: Main theorem

**What's needed**:
```lean
-- Given: 3-edge-coloring of dual graph (vertices = Finset E)
-- Want: 4-vertex-coloring of primal graph (vertices = V)

def dualColoringToPrimal
    (dual_coloring : (Finset E) → VertexColor)  -- coloring on dual vertices (faces)
    : V → VertexColor :=
  fun v =>
    -- v is a primal vertex
    -- v is surrounded by faces f₁, f₂, f₃ (in cyclic order from rotation system)
    -- In dual: these are 3 vertices forming a "face" around v
    -- The 3 dual vertices have 3 colors (from dual coloring)
    -- Map these to a primal vertex color
    sorry
```

**This needs geometric insight**: The dual of the dual is the primal!

---

### **Phase 4: Integration** (Glue Code)

#### Task 4.1: Apply Lemma 4.5 ⭐⭐ CONNECTION
**File**: FourColorTheorem.lean:82
**Lines**: ~20
**Dependencies**: Existing Triangulation.lean proof
**Unlocks**: Main theorem flow

**Strategy**:
- Lemma 4.5 already proven in Triangulation.lean (around line 850)
- Need to instantiate it with the right parameters
- Should be straightforward connection

---

#### Task 4.2: Apply Strong Dual ⭐⭐ CONNECTION
**File**: FourColorTheorem.lean:88
**Lines**: ~20
**Dependencies**: Existing StrongDual.lean infrastructure
**Unlocks**: Main theorem flow

**Strategy**:
- Strong Dual already developed in StrongDual.lean
- Need to connect to zero-boundary chains
- Should be straightforward connection

---

#### Task 4.3: Kempe Chain Reachability ⭐⭐⭐⭐⭐ HARDEST
**File**: FourColorTheorem.lean:97
**Lines**: ~100-150
**Dependencies**: `kempeSwitch_proper`, dual graph, Lemma 4.5, Strong Dual
**Unlocks**: Main theorem!

**Strategy** (high-level):
```lean
-- Prove by contradiction:
-- Suppose 3-edge-coloring doesn't exist
-- Then by Kempe chain argument, we can construct a contradiction
-- using the zero-boundary structure from Lemma 4.5

-- Key insight: If we can't 3-edge-color, then for any attempted coloring,
-- there's an edge e that "blocks" us. But Kempe switches allow us to
-- recolor locally without affecting global structure. This gives contradiction
-- with zero-boundary spanning (Lemma 4.5).
```

**This is the DEEPEST mathematical content!**

---

## Recommended Execution Order

### **Sprint 1: Foundation (Axioms)** ⚡ ~70 lines, 2-3 hours

1. ✅ `missing_color_injective` - DONE!
2. ⭐ `adj_iff_share_edge` - 15 lines
3. ⭐⭐ `cubic_proper_coloring_missing_color` - 25 lines
4. ⭐⭐⭐ `adjacent_not_same_missing` - 30 lines (NEEDS REVIEW - might be false!)

**Output**: All axioms proven, foundation solid

---

### **Sprint 2: Tait Equivalence** ⚡ ~105 lines, 3-4 hours

5. ⭐ `tait_reverse` final case - 5 lines (trivial)
6. ⭐⭐ `kempeSwitch_proper` cases - 60 lines (tedious)
7. ⭐⭐⭐ `tait_forward` - 40 lines (medium)

**Output**: Tait equivalence complete, ready for integration

---

### **Sprint 3: Dual Infrastructure** ⚡ ~130-150 lines, 4-6 hours

8. ⭐⭐⭐⭐ Dual graph construction - 80-100 lines (design needed)
9. ⭐⭐⭐ Dual-to-primal conversion - 50 lines (depends on #8)

**Output**: Can convert between primal and dual colorings

---

### **Sprint 4: Integration & Kempe** ⚡ ~140-170 lines, 6-10 hours

10. ⭐⭐ Apply Lemma 4.5 - 20 lines (connection)
11. ⭐⭐ Apply Strong Dual - 20 lines (connection)
12. ⭐⭐⭐⭐⭐ Kempe chain reachability - 100-150 lines (HARD!)

**Output**: Main theorem proven! 🎉

---

## Critical Path

```
adj_iff_share_edge ──┐
                     ├──> tait_forward ──┐
cubic_missing_color ─┘                   ├──> four_color_equiv_tait ──┐
                                         │                              │
missing_color_inj ✅ ──> tait_reverse ──┘                              │
                                                                        │
kempe_chain_colors ✅ ──> kempeSwitch_proper ──> Kempe reachability ──┤
                                                                        │
                   Dual graph construction ──> Dual-to-primal ─────────┤
                                                                        │
                   Lemma 4.5 connection ──────────────────────────────┤
                   Strong Dual connection ─────────────────────────────┤
                                                                        │
                                                                        v
                                                              Main Theorem ✅
```

---

## Risk Assessment

### ⚠️ **High Risk: `adjacent_not_same_missing` axiom**

This axiom might be **false as stated**. Need to check:
- In cubic graph with proper 3-edge-coloring
- Each vertex's 3 edges must use 3 different colors
- But there are only 3 edge colors total
- So each vertex's edges use ALL 3 colors
- Therefore no vertex can be "missing" a color!

**Resolution**: Either:
1. The axiom is wrongly stated (fix the statement)
2. The context is different (dual graph? different graph structure?)
3. Need additional hypotheses

**Action**: Review this before proving!

### ⚠️ **High Risk: Dual graph construction**

Biggest infrastructure gap. Need to carefully design:
- How faces map to vertices
- How edges are shared
- How to prove cubic property
- Connection to rotation system

**Action**: May need to create separate module `DualGraph.lean`

### ⚠️ **High Risk: Kempe reachability**

Deepest mathematical content. Might discover missing lemmas during proof.

**Action**: Break into smaller lemmas as needed

---

## Success Metrics

- **Sprint 1 complete**: 3 axioms proven, foundation solid
- **Sprint 2 complete**: Tait equivalence done, can convert colorings
- **Sprint 3 complete**: Dual infrastructure in place
- **Sprint 4 complete**: PROOF DONE! 🏆

**Total estimate**: 445-495 lines, 15-23 hours of focused work

---

**Strategy**: Work bottom-up, each proof unlocks the next. If blocked, can work on independent branches (e.g., dual construction while proving axioms).

**Next step**: START WITH SPRINT 1! 🚀
