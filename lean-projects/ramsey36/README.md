# Ramsey36 — Lean 4 Formalization of R(3,6) = 18

A complete, axiom-clean Lean 4 proof that the Ramsey number **R(3,6) = 18**:
among any 18 people, either 3 are mutual friends or 6 are mutual strangers.

```
#print axioms ramsey_three_six
-- 'ramsey_three_six' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `native_decide`. No `sorry`. Standard Lean 4 foundations only.

## Statement

```lean
theorem ramsey_three_six : ramseyNumber 3 6 = 18
```

where `ramseyNumber` is defined as the infimum of the set of positive `n` for which
every `n`-vertex graph contains a 3-clique or a 6-independent set.

The classical Radziszowski characterization is also formalized:

```lean
theorem isRamseyNumber_3_6_18 : IsRamseyNumber 3 6 18
-- IsRamseyNumber k l n ↔ n = ramseyNumber k l  (proved in RamseyAlt.lean)
```

## Proof Structure

The proof follows Cariolaro's elementary argument, formalized as
`Nat.le_antisymm` of a lower bound (§ lower) and upper bound (§ upper).

### Lower bound — 17-vertex critical graph (`Critical17.lean`)

The Graver–Yackel graph on 17 vertices is triangle-free with independence number 5.
Embedding it into any graph on ≤ 17 vertices shows R(3,6) ≥ 18.

Both properties (triangle-free, no 6-independent set) are proved via the
**IndepSetChecker** architecture below.

### Upper bound — Cariolaro's argument (`Basic.lean`, 12,859 lines)

Assume a triangle-free graph on 18 vertices with no 6-independent set. Derive False via:

1. **Claim 1** (`claim1_five_regular`): the graph is 5-regular
2. **Claim 2** (`claim2_neighbor_structure`): non-neighbors share 1 or 2 common neighbors
3. **Claim 3** (`claim3_four_cycle`): the set P (non-neighbors sharing 1 common neighbor) induces a 4-cycle
4. **Final contradiction** (`final_contradiction`): the labeling forces two vertices to share 3 common neighbors, contradicting Claim 2

### Small Ramsey dependencies (`SmallRamsey.lean`)

The upper bound uses R(3,3)=6, R(3,4)=9, R(3,5)=14 (all formalized, all with the
same axiom footprint). Critical graphs: C₅, C₈(1,4), Paley(13).

## The IndepSetChecker Architecture

The key technical contribution: a **verified** kernel-checked backtracking search
that avoids both the C(17,6)=12,376 kernel blowup of naive `decide` and the
`Lean.ofReduceBool` axiom of `native_decide`.

### File layout (Mathlib-free computation layer at the bottom)

```
IndepSetFunc.lean      (38 lines)   — Bool backtracking search, NO Mathlib
    ↑ imported by
IndepSub17.lean        (88 lines)   — 12 sub-problems, by decide, NO Mathlib
IndepSmall.lean        (93 lines)   — small graph checks (R33/R34/R35), NO Mathlib
    ↑ imported by
IndepSplit.lean        (32 lines)   — chains sub-problems via hasIndepSetAux_false_of_compat
IndepSetChecker.lean   (222 lines)  — completeness theorem + SimpleGraph bridge
```

The sub-problem files import **only** `IndepSetFunc.lean`, so kernel evaluation
runs at ~100 MB instead of the ~5 GB from loading Mathlib `.oleans`.

### Completeness theorem (the key correctness guarantee)

```lean
theorem hasIndepSetAux_complete
    {n : ℕ} {adj : Fin n → Fin n → Bool} ... {s : Finset (Fin n)}
    (h_fuel   : n ≤ start + fuel)
    (h_card   : s.card = remaining)
    (h_ge     : ∀ v ∈ s, start ≤ v.val)
    (h_indep  : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → adj v w = false)
    (h_compat : ∀ v ∈ s, ∀ w ∈ chosen, adj v w = false) :
    hasIndepSetAux n adj remaining start chosen fuel = true
```

Contrapositive: a `false` return is an **axiom-free kernel theorem** — not trusted
execution. The search is sound by construction (each vertex is added only when
compatible with all prior choices), but this direction is not needed for the proof.

### Bridge to Mathlib's `SimpleGraph`

```lean
-- Accept any Bool adjacency extensionally equal to decide (G.Adj · ·)
theorem noKIndepSet_of_adj_checker_false
    (hadj : ∀ v w : Fin n, adj v w = decide (G.Adj v w))
    (h    : hasIndepSet n adj k = false) : NoKIndepSet k G

-- Triangle-free via complement adjacency
theorem triangleFree_of_adj_checker_false
    (hadj : ∀ v w : Fin n, adjNot v w = !decide (G.Adj v w))
    (h    : hasIndepSet n adjNot 3 = false) : TriangleFree G
```

The bridge specs (`adj17Bool_spec`, `adj17NotBool_spec`) verify 289 pairs by `decide` — fast because each pair is a closed O(5)-step computation.

## Module Index

| File | Lines | Role |
|------|------:|------|
| `RamseyDef.lean` | 98 | Core definitions: `HasRamseyProperty`, `ramseyNumber` |
| `RamseyAlt.lean` | 173 | Textbook characterization `IsRamseyNumber` + equivalence proof |
| `IndepSetFunc.lean` | 38 | Bool backtracking search (Mathlib-free) |
| `IndepSub17.lean` | 88 | 12 sub-problems for 17-vertex graph (Mathlib-free) |
| `IndepSmall.lean` | 93 | Small graph Bool checks (Mathlib-free) |
| `IndepSplit.lean` | 32 | Combines sub-problems |
| `IndepSetChecker.lean` | 222 | Completeness theorem + SimpleGraph bridge |
| `Critical17.lean` | 146 | Graver–Yackel graph: triangle-free, α=5 |
| `SmallRamsey.lean` | 1,416 | R(3,3)=6, R(3,4)=9, R(3,5)=14 |
| `FiveCycleLemma.lean` | 229 | 5-vertex structural lemma |
| `Helpers.lean` | 213 | Shared combinatorial helpers |
| `Basic.lean` | 12,859 | Upper bound: Cariolaro's proof |
| `MainTheorem.lean` | 30 | `ramsey_three_six` + axiom declaration |

## Build

```bash
cd lean-projects/ramsey36
lake exe cache get        # fetch Mathlib cache
export LAKE_JOBS=3
nice -n 19 lake build

# Verify axiom footprint
lake env lean Ramsey36/MainTheorem.lean
# Expected: 'ramsey_three_six' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Requires Lean 4.28.0 (see `lean-toolchain`).

## Paper

`paper/ramsey36_lean.tex` — a 17-page ITP-style paper describing the formalization,
with special focus on the IndepSetChecker architecture.

## References

- Cariolaro, D. (1999). *An easy proof that R(3,6)=18*
- Graver, J. E. & Yackel, J. (1968). *Some graph theoretic results associated with Ramsey's theorem*
- Greenwood, R. E. & Gleason, A. M. (1955). *Combinatorial relations and chromatic graphs*
- Radziszowski, S. P. *Small Ramsey Numbers*, Electronic Journal of Combinatorics, DS1
