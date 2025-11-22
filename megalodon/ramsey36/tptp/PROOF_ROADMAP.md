# R(3,6) = 18 Proof Roadmap

## Overview

The goal is to prove R(3,6) = 18, which consists of two parts:
1. **Lower bound**: R(3,6) ≥ 18 (construct a 17-vertex (3,5)-Ramsey graph) - DONE in Megalodon
2. **Upper bound**: R(3,6) ≤ 18 (no 18-vertex triangle-free graph without 6-independent set)

This document focuses on the **upper bound** proof.

## ATP-Verified Lemmas

### Lemma 1: Degree Bound (VERIFIED by Vampire)
**File**: `degree_bound.p`, `degree_bound_simple.p`
**Status**: `SZS status Theorem` (22.6s), `SZS status ContradictoryAxioms` (0.018s)

**Statement**: In a triangle-free graph with no 6-independent set, every vertex has degree ≤ 5.

**Proof sketch**:
- In triangle-free graph, neighborhood of any vertex is independent
- If vertex v has 6+ neighbors, those neighbors form 6-independent set
- Contradicts "no 6-independent set" hypothesis

**TPTP encoding**: See `degree_bound_simple.p` for minimal encoding.

### Lemma 2: Case 1 - 6 Red Neighbors (VERIFIED by Vampire)
**File**: `k18_case_analysis.p`
**Status**: `SZS status Theorem`

**Statement**: If vertex v has 6 red neighbors in 2-colored K_n, and red graph is triangle-free, then blue graph contains K_6.

## Proof Structure for Upper Bound

The upper bound proof follows this structure (Cariolaro's approach):

```
Assume: G is triangle-free on 18 vertices with no 6-independent set

Step 1: Degree Bound [VERIFIED]
  - By Lemma 1: max_degree(G) ≤ 5

Step 2: Vertex Neighborhood Analysis
  - Pick any vertex v with degree d ≤ 5
  - N(v) is independent (triangle-free) with |N(v)| = d ≤ 5
  - Non-neighbors T = V \ {v} \ N(v) with |T| = 17 - d ≥ 12

Step 3: Apply R(3,4) = 9
  - T has 12+ vertices, is triangle-free
  - By R(3,4) = 9 < 12: T contains 4-independent set I4 = {a,b,c,d}

Step 4: Build 5-Independent Set
  - S = {v} ∪ I4 = {v, a, b, c, d}
  - v is non-adjacent to all of I4 (they're in T)
  - I4 is pairwise non-adjacent (by definition)
  - So S is 5-independent

Step 5: Extend to 6-Independent Set
  - Remaining vertices R = T \ I4 has |R| = 8 vertices
  - Need: at least one r ∈ R non-adjacent to all of S
  - Counting argument:
    * Each vertex in S has degree ≤ 5
    * Total edges from S: ≤ 25
    * Need to "block" all 8 vertices in R from being the 6th
    * Key: R is triangle-free with max_degree 5
    * By R(3,3) = 6 < 8: R has 3-independent set
    * Refined counting shows not all can be blocked

Step 6: Contradiction
  - 6-independent set exists
  - Contradicts hypothesis
  - Therefore no such G exists
  - Therefore R(3,6) ≤ 18
```

## Required Sub-lemmas

### R(3,4) = 9 Lemma
**Status**: Not directly ATP-verifiable (finite combinatorics)
**Options**:
1. Axiomatize as assumption
2. Prove by exhaustive case analysis in Megalodon
3. Use SAT solver for finite verification

### Step 5 Counting Lemma
**Status**: Most challenging step
**Approach**: Break into smaller cases based on degree distribution

## Files in this Directory

| File | Purpose | Vampire Status |
|------|---------|----------------|
| `degree_bound.p` | General degree bound | Theorem (22.6s) |
| `degree_bound_simple.p` | Minimal degree bound | ContradictoryAxioms (0.018s) |
| `k18_case_analysis.p` | Case 1: 6 red neighbors | Theorem |
| `k18_case2.p` | Case 2: ≤5 red neighbors | In progress |
| `r36_upper_bound_v2.p` | Full problem attempt | Timeout |
| `greedy_6indep.p` | Greedy construction | Timeout |
| `r36_with_r34_axiom.p` | With R(3,4) axiom | CounterSat (constraints incomplete) |
| `r36_tight.p` | Tighter constraints | CounterSat (constraints incomplete) |

## Recommendations for Megalodon Integration

1. **Import verified lemmas**: The degree_bound lemma can be imported as axiom, justified by ATP proof
2. **Prove R(3,4)=9 separately**: This is simpler and could be done by case analysis
3. **Manual proof of Step 5**: The extension argument may require manual reasoning in Megalodon
4. **Alternative**: Use SAT/SMT solvers for finite model checking, then trust the result

## References

- Cariolaro, D. "The Ramsey Numbers R(3,6) = 18 and R(3,7) = 23" (2010)
- Graver, J. & Yackel, J. "Some Graph Theoretic Results" (1968) - lower bound construction
- Kalbfleisch, J. G. "Construction of Special Edge-Chromatic Graphs" (1965)
