# Session 2025-11-12: Path 2 - Disk Kempe-Closure Spanning Lemma

**Date**: 2025-11-12
**Status**: ✅ **INITIATED PATH 2 - THE PROPER APPROACH**
**Focus**: Formalizing Goertzel's Disk Kempe-Closure Spanning Lemma (Theorem 4.10)

---

## Executive Summary

After confirming with the user which path to take, we've identified **Path 2** as the **most proper and thorough** approach - it's exactly what Goertzel's 4CP proof does. This session initiates the formalization of the Disk Kempe-Closure Spanning Lemma, the core technical contribution of the proof.

**Key Decision**: Path 2 (Formalize Spanning Lemma) > Path 1 (Iterate pairs) or Path 3 (Planarity)

---

## Why Path 2? Reading Goertzel's Paper

### From the Abstract

> "We give a complete human proof of the **Disk Kempe-Closure Spanning Lemma** for the between-region annulus of a trail."

This is THE key technical contribution.

### Theorem 4.10: Disk Kempe-Closure Spanning (Strong Dual)

```
If z ∈ W₀(H) and z ⊥ 𝒢 ∪ {Mr, Mb}, then z = 0
Equivalently: W₀(H) ⊆ span(𝒢 ∪ {Mr, Mb})
```

Where:
- **W₀(H)** = zero-boundary cycle space (boundary-compatible colorings)
- **𝒢** = face generators from Kempe-closure
- **Mr, Mb** = meridional generators (annular topology)

### The Proof Technique (Section 4)

**Not iteration through pairs** - instead:

1. **Purification** (Lemmas 4.3-4.4)
   - Express face generators as boundary-only vectors
   - B^f_αβ = γ · 1_{∂f ∩ (αβ)}

2. **Dual forest decomposition** (Lemma 4.7)
   - Interior dual graph F (faces as vertices)
   - Spanning forest T for peeling structure

3. **Orthogonality peeling** (Lemma 4.9)
   - Induction on leaf-subtrees
   - At each cut edge e*, use orthogonality to force z(e*) = 0

4. **Vector space spanning**
   - Linear algebra over F₂×F₂
   - Annihilator argument: if z ⊥ 𝒢, then z = 0

---

## What We Created

### File: `FourColor/Kempe/Spanning.lean`

**Purpose**: Formalize the Disk Kempe-Closure Spanning Lemma (Goertzel Theorem 4.10)

**Key Definitions**:

1. **ColorGroup (F₂²)**
   ```lean
   abbrev ColorGroup := Bool × Bool
   def ColorGroup.zero : ColorGroup := (false, false)
   ```

2. **Zero-Boundary Cycle Space W₀(H)**
   ```lean
   def W₀ (H : GraphRegion V E) : Set (F2Chain E) :=
     { x | (boundary condition) ∧ satisfies_kirchhoff H x }
   ```

3. **Face Generators X^f_αβ(C)**
   ```lean
   def face_generator (H : GraphRegion V E) (f : Face V E)
       (α β γ : EdgeColor) (coloring : E → EdgeColor) : F2Chain E
   ```

4. **Purified Generators B^f_αβ**
   ```lean
   def purified_face_generator (H : GraphRegion V E) (f : Face V E)
       (α β γ : EdgeColor) : F2Chain E
   ```

5. **Main Theorem**
   ```lean
   theorem disk_kempe_closure_spanning (H : GraphRegion V E) (C₀ : E → EdgeColor) :
       ∀ z ∈ W₀ H, (∀ g ∈ face_generators H C₀, z ⊥ g) → z = 0
   ```

---

## From Goertzel's Paper: Key Insights

### Page 3: "The Transition to Linear Algebra"

> "The critical insight is recognizing where topological methods must yield to algebraic ones. While formations beautifully capture the local structure of colorings, proving global properties requires **linear algebra over F₂**."

> "We encode the three edge colors as vectors in F₂²: red as (1, 0), blue as (0, 1), and purple as (1, 1). A formation becomes a map from edges to these vectors, and Kempe switches correspond to adding cycle vectors to the current coloring."

### Page 4: "The Parity Contradiction"

> "The spanning lemma guarantees that if a minimal counterexample existed, we could transform between two specific configurations... However, the Parity Lemma shows that the number of curves modulo 2 is invariant under all permitted operations."

### Page 11: Proposition 4.11 (Local Reachability)

> "For any trail, the following are equivalent:
> (i) The extended graph is 3-edge-colorable
> (ii) Starting from any proper boundary-compatible coloring, one can complete across the empty edge by Kempe switches in the between-region."

---

## Mathematical Structure

### The Three Levels (from Goertzel's CDL perspective)

| Topological      | CDL/Lattice           | Algebraic                |
|------------------|-----------------------|--------------------------|
| Formation curves | Distinctions          | Generating vectors       |
| Kempe switches   | Inverse distinctions  | Co-boundary addition     |
| Shared segments  | Lattice meets         | Linear combinations      |
| Completability   | Support spanning      | Vector space spanning    |

**Key Point**: While formations provide geometric intuition, the impossibility of a counterexample emerges only through **linear algebra** (dimension counting and orthogonality).

---

## Why NOT Path 1 (Iterate Pairs)?

Iterating through 6 color pairs is:
- ❌ Not what Goertzel's proof does
- ❌ Tedious case analysis (45-60 min)
- ❌ Misses the deep structure (vector space spanning)
- ❌ Less general and elegant

**Goertzel's approach**: The spanning lemma **guarantees** that some pair works, without needing to check all 6 explicitly.

---

## Why NOT Path 3 (Planarity via Degree ≤ 5)?

Classical planarity arguments:
- ❌ Not Goertzel's approach
- ❌ Uses degree bounds (degree ≤ 5)
- ❌ Combinatorial rather than algebraic
- ❌ Misses the linear algebra structure

**Goertzel's approach**: Planarity enters via the **annular topology** and Jordan-Schönflies theorem, not through degree bounds.

---

## Implementation Roadmap

### Phase 1: Foundational Definitions ✅ (Today)
- [x] ColorGroup (F₂²) infrastructure
- [x] GraphRegion H (annulus structure)
- [x] W₀(H) (zero-boundary cycle space)
- [x] Face generator stubs
- [x] Main theorem statement

### Phase 2: Kirchhoff and Faces (Next Session, ~2 hours)
- [ ] Proper Kirchhoff constraint formalization
- [ ] Face boundary structure
- [ ] Two-color runs on ∂f
- [ ] Run completion via interior arcs
- [ ] Face generator X^f_αβ(C) implementation

### Phase 3: Purification (2-3 hours)
- [ ] Lemma 4.2: Run invariance under Kempe switches
- [ ] Lemma 4.3: Per-run purification (XOR complementary arcs)
- [ ] Lemma 4.4: Face-level purification (B^f_αβ ∈ span 𝒢)

### Phase 4: Dual Forest (1-2 hours)
- [ ] Interior dual graph F
- [ ] Spanning forest T
- [ ] Leaf-subtree identification
- [ ] Cut parity lemma (Lemma 4.8)

### Phase 5: Orthogonality Peeling (2-3 hours)
- [ ] Lemma 4.9: Orthogonality forcing on leaf cut
- [ ] Induction on forest T
- [ ] Annihilator inclusion
- [ ] Main theorem proof (Theorem 4.10)

### Phase 6: Local Reachability (1 hour)
- [ ] Proposition 4.11: Local reachability equivalence
- [ ] Connect to Kauffman's reduction (Theorem 3.1)
- [ ] Derive 4CT (Theorem 5.1)

**Total Estimated Time**: 8-11 hours of focused work

---

## Commits This Session

**460b36bb** - Start Disk Kempe-Closure Spanning Lemma formalization (Path 2)
- Created `FourColor/Kempe/Spanning.lean`
- Defined ColorGroup, W₀(H), face generators
- Stated main theorem (disk_kempe_closure_spanning)
- Organized Goertzel PDFs into literature/Goertzel_4CP/

---

## Key Quotes from User Discussion

**User**: "What way do you think is the most proper or thorough? Probably 1 or 2? Which is done in the 4CP proof? Should be Path 2?"

**Response**: "You're absolutely right - Path 2 is the Most Proper and Thorough. Reading Goertzel's paper confirms: Path 2 (Formalize the Disk Kempe-Closure Spanning Lemma) is precisely what Goertzel's proof uses as its core technical contribution."

---

## Next Session Goals

1. **Kirchhoff Constraint** (30 min)
   - Formalize proper even-degree constraint
   - Edge-incidence structure
   - Vertex sums in F₂²

2. **Face Structure** (60 min)
   - Face boundary as cyclic list
   - Two-color runs on ∂f
   - Maximal contiguous blocks

3. **Run Completion** (30 min)
   - Interior arc selection
   - Cycle closure
   - Third-color scaling

4. **Test Build** (10 min)
   - Verify types check
   - Fix any import issues

---

## Comparison: Three Paths

| Aspect           | Path 1 (Iterate)  | Path 2 (Spanning) ⭐ | Path 3 (Planarity) |
|------------------|-------------------|----------------------|--------------------|
| Used in Goertzel | ❌ No             | ✅ Yes (core proof)  | ❌ No              |
| Mathematical     | Combinatorial     | Linear Algebra       | Degree bounds      |
| Elegance         | Low (case split)  | High (spanning)      | Medium             |
| Generality       | Specific          | General              | Graph-specific     |
| Formalization    | 45-60 min         | 8-11 hours           | 30-45 min          |
| Rigor            | Correct but tedious| Most rigorous       | Correct but dated  |

---

## Conclusion

This session marks a **critical milestone**: we've committed to **Path 2**, the proper and thorough approach that matches Goertzel's actual proof. The Disk Kempe-Closure Spanning Lemma is the **heart of the 4CP proof** - it's where topological intuition yields to algebraic precision.

**Status**: 🟢 **PATH 2 INITIATED**
**Confidence**: 🟢 **VERY HIGH** (aligned with source material)
**Next**: Formalize Kirchhoff constraint and face structure

The foundational file `Spanning.lean` is created with:
- ✅ Type signatures for all key definitions
- ✅ Main theorem statement
- ✅ Proof strategy documented
- ✅ Clear roadmap for completion

**This is the right path forward.**

---

**Date**: 2025-11-12
**Duration**: 60 minutes
**Commits**: 1
**Files Created**: 1 (Spanning.lean)
**Lines Added**: ~250
**Session Status**: ✅ **FOUNDATIONAL WORK COMPLETE**
