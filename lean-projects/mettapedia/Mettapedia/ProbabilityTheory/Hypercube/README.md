# Probability Hypercube Formalization

Lean 4 formalization of the **Probability Hypercube** framework, which unifies multiple probability theories through lattice-theoretic axiomatizations.

## Overview

The probability hypercube is a geometric framework for understanding relationships between different probability theories. Each vertex represents a distinct probability theory characterized by which lattice axioms it satisfies:

- **Kolmogorov (Classical)**: Boolean algebra (distributive orthomodular lattice)
- **Dempster-Shafer**: Non-distributive, uses belief functions on power sets
- **Fuzzy Probability**: Different handling of conjunction
- **Quantum Probability**: Orthomodular lattice (non-distributive)
- **Imprecise Probability**: Interval-valued

**Key Insight**: The presence or absence of **commutativity** in orthomodular lattices determines the classical/quantum boundary. Commuting elements generate Boolean (classical) sublattices within the quantum structure.

## Primary References

### Knuth-Skilling Framework
- **Knuth, K. & Skilling, J. (2012)**. "Foundations of Inference." *Axioms* 1(1), 38-73.
  - [https://doi.org/10.3390/axioms1010038](https://doi.org/10.3390/axioms1010038)
  - Derives probability calculus from lattice symmetries without continuity assumptions

- **Skilling, J. & Knuth, K. (2019)**. "A Symmetrical Foundation for Quantum Theory." *AIP Conference Proceedings* 2131, 020003.
  - Extension to quantum theory via orthomodular lattices

### Orthomodular Lattice Theory
- **Foulis, D.J. (1962)**. "A note on orthomodular lattices." *Portugaliae Math.* 21(1), 65-72.
  - Proves commuting elements generate distributive sublattices

- **Kalmbach, G. (1983)**. *Orthomodular Lattices*. Academic Press.
  - Standard reference for OML theory, exchange property

- **Beran, L. (1985)**. *Orthomodular Lattices, Algebraic Approach*. D. Reidel.
  - Symmetry of commutativity, detailed proofs

### Dempster-Shafer Theory
- **Dempster, A.P. (1967)**. "Upper and lower probabilities induced by a multivalued mapping." *Ann. Math. Statist.* 38(2), 325-339.

- **Shafer, G. (1976)**. *A Mathematical Theory of Evidence*. Princeton University Press.

- **Smets, P. & Kennes, R. (1994)**. "The transferable belief model." *Artificial Intelligence* 66(2), 191-234.
  - Generalization to arbitrary lattices

## File Organization

### Core Theory Files

#### `NovelTheories.lean` (43 KB)
Orthomodular lattice foundations and quantum probability structures:
- **`OrthomodularLattice` class**: Axiomatization with orthomodular law, de Morgan laws, complementation
- **Orthogonality → Disjointness** `inf_eq_bot_of_le_compl`: `a ≤ bᶜ → a ⊓ b = ⊥`
- **Important Note on Disjointness vs Orthogonality**: Documents that in general OML, `a ⊓ b = ⊥` does NOT imply `a ≤ bᶜ` (with Hilbert space counterexample)
- **Commutativity Predicate** `commutes`: Defines when elements behave classically
- **`QuantumMassFunction`**: Mass functions on finite orthomodular lattices
- **`QuantumState`**: Probability measures on OMLs (orthoadditive, normalized)

**Key Mathematical Insight**:
The "quasi-distributivity" property `(a ⊔ b) ⊓ aᶜ ≤ b` is **FALSE** in general OML!
Counterexample in Hilbert lattice of ℂ²: `a = span{(1,0)}, b = span{(1,1)}` gives
`(a ⊔ b) ⊓ aᶜ = span{(0,1)} ⊈ span{(1,1)} = b`. This asymmetry is fundamental to quantum logic.

#### `NeighborTheories.lean` (52 KB)
Commutativity theory and the classical/quantum boundary:
- **Commutativity Lemmas**:
  - `commutes_symm`: Symmetry of commutativity
  - `commutes_compl`: Preservation under complement
  - `commutes_self`, `commutes_top`, `commutes_bot`: Basic cases
  - `commutes_of_le_compl`: Orthogonality implies commutativity
- **Exchange Property (Bidirectional)**:
  - `exchange_of_commutes`: `a C b → a ⊓ (aᶜ ⊔ b) = a ⊓ b`
  - `commutes_of_exchange`: Converse direction
  - `commutes_iff_exchange`: Full characterization
- **Foulis-Holland Theorem (Complete!)**:
  - `commutes_inf`: `a C b ∧ a C c → a C (b ⊓ c)`
  - `commutes_sup`: `a C b ∧ a C c → a C (b ⊔ c)`
- **Quantum Logic Note**: Disjunctive syllogism does *not* hold in general OMLs; `NeighborTheories.lean`
  deliberately avoids an unconditional `oml_disjunctive_syllogism` lemma.
- **Orthocomplement Uniqueness (Safe Form)**:
  - `orthocomplement_unique_of_commutes`: complements are unique *among commuting candidates*

**Novel Contributions**:
- **Complete Foulis-Holland theorem**: Commuting elements are closed under ⊓ and ⊔
- Bidirectional exchange characterization (first rigorous formalization)
- De Morgan duality proof for `commutes_sup` via `commutes_inf`

#### `Basic.lean` (54 KB)
The **master probability hypercube**:
- Defines all hypercube axes (e.g. `CommutativityAxis`, `DistributivityAxis`, …)
- Defines `ProbabilityVertex` (one record holding all axes)
- Defines named theories as vertices (`kolmogorov`, `cox`, `knuthSkilling`, `dempsterShafer`, `quantum`, …)
- Defines basic navigation (`isNaturalEdge`, `hammingDistance`, `isMoreGeneral`, …)

Note: this file classifies Dempster–Shafer/quantum/etc as vertices, but it does *not* implement
full belief-function combination rules; those belong in separate developments.

#### `KnuthSkilling.lean` + `KnuthSkilling/` (slice modules)
K&S-focused modules that situate the Appendix A development inside the master hypercube:
- `KnuthSkilling/Connection.lean`: conceptual bridge to the master `ProbabilityVertex` view
- `KnuthSkilling/Neighbors.lean`: local neighbor analysis around the `knuthSkilling` vertex
- `KnuthSkilling/Proofs.lean`: small fully-checked “shape lemmas” (toy derivation graph)
- `KnuthSkilling/Theory.lean`: K&S-centered theory notes (interval/ℚ/ℝ viewpoints)

#### `Taxonomy.lean` (17 KB)
**Weakness / generality ordering** for the full hypercube:
- Defines `≤` on each axis (as a `PartialOrder`), with `⊥` = most constrained and `⊤` = most permissive
- Gives the product `PartialOrder` on `ProbabilityVertex` (so the hypercube becomes a genuine poset)
- Proves equivalence to `Basic.lean`’s manual `isMoreGeneral` predicate (`le_iff_isMoreGeneral`)
- Provides “thin-category” perspective: vertices + weakening maps form a preorder/poset

#### `WeaknessOrder.lean` (3 KB)
Goertzel-style weakness preorder (as an opposite category):
- Defines `V ≼ W` as `isMoreGeneral V W`
- Packages the weakness relation as `ProbabilityVertexᵒᵈ` (a preorder-category)
- Provides `Nonempty (V ⟶ W) ↔ (V ≼ W)` in the preorder-category

#### `QuantaleSemantics.lean` (25 KB)
Uniform **quantale semantics** and morphisms for all `QuantaleType` cases:
- Concrete carriers for commutative / interval / noncommutative / free / boolean / monotone cases
- A `semanticsOfQuantaleType` “picker” (avoids global instance clashes)
- Canonical `QuantaleHom`s into `BoolQuantale` / `CommQuantale`
- `QuantaleHom.map_weakness` can transport Goertzel’s weakness measure along these maps

#### `ThetaSemantics.lean` (5 KB)
Abstract “Θ-family ⇒ credal/interval semantics” API:
- `intervalOfFamily` builds lower/upper envelopes from a set of completions
- `Subsingleton` families collapse to point semantics (`lower = upper`)

#### `ScaleDichotomy.lean` and `DensityAxisStory.lean` (5 KB total)
Formal bridge from “density axis” to the subgroup dichotomy:
- Additive subgroups in archimedean ordered groups are either dense or `ℤ•g`
- Packages `AddSubgroup.dense_or_cyclic` into hypercube-friendly lemmas

#### `UnifiedTheory.lean` (10 KB)
Abstract framework for lattice-based probability:
- Generic `LatticeProbability` structure
- Unifies classical, quantum, and imprecise probability
- Shows Kolmogorov as special case

### Advanced Constructions

#### `StayWellsConstruction.lean` (19 KB)
Stey-Wells embedding of classical D-S into quantum:
- Embeds `Finset Ω` into orthomodular lattices
- Preserves belief function semantics
- Shows classical D-S as quantum special case

#### `OperationalSemantics.lean` (12 KB)
Dynamic epistemic update rules:
- Bayesian conditioning
- Jeffrey's rule
- Dempster-Shafer update

### Examples and Counterexamples

#### `CentralQuestionCounterexample.lean` (1.3 KB)
Minimal counterexample showing `quantaleAnd` ≠ lattice meet in general

## Key Theoretical Results

### 1. Disjointness vs Orthogonality (Important Discovery!)
In Boolean algebras: `a ⊓ b = ⊥ ↔ a ≤ bᶜ` (disjointness = orthogonality)

**In general OML: `a ≤ bᶜ → a ⊓ b = ⊥` but NOT the converse!**

The "quasi-distributivity" property `(a ⊔ b) ⊓ aᶜ ≤ b` is **FALSE** in general OML.
Counterexample in ℂ²: `a = span{(1,0)}, b = span{(1,1)}` gives `(a ⊔ b) ⊓ aᶜ = span{(0,1)} ⊈ b`.

This asymmetry is fundamental to quantum logic and distinguishes it from classical logic.

### 2. Exchange Property (Bidirectional Characterization)
**Theorem** `commutes_iff_exchange`: `a C b ↔ a ⊓ (aᶜ ⊔ b) = a ⊓ b`

From Kalmbach (1983). This is THE key property distinguishing commuting (classical-like) from non-commuting (quantum) pairs of events. We proved both directions rigorously.

### 3. Foulis-Holland Theorem (Complete!)
**Theorem** `commutes_inf`: If `a C b` and `a C c`, then `a C (b ⊓ c)`
**Theorem** `commutes_sup`: If `a C b` and `a C c`, then `a C (b ⊔ c)`

Commuting elements are closed under lattice operations. Distributivity for commuting triples is
recorded as `commuting_distributive` (proved). This is part of the standard story
of why classical probability emerges from quantum probability when measuring compatible observables.

**Proof Strategy**:
- For `commutes_inf`: Use exchange characterization. Since `b ⊓ c ≤ b, c`, the exchange bounds combine to give `a ⊓ (aᶜ ⊔ (b ⊓ c)) = a ⊓ b ⊓ c`.
- For `commutes_sup`: De Morgan duality. `b ⊔ c = (bᶜ ⊓ cᶜ)ᶜ`, apply `commutes_inf` to complements, then `commutes_compl`.

## Building the Formalization

```bash
cd lean-projects/mettapedia
export LAKE_JOBS=3
ulimit -Sv 6291456
nice -n 19 lake build Mettapedia.ProbabilityTheory.Hypercube
```

**Dependencies**:
- Lean 4.25.0
- Mathlib v4.25.0

## Current Status

### Build (last checked 2026-01-11)

`lake build Mettapedia.ProbabilityTheory.Hypercube` succeeds with **0** `sorry`s.

### Completed (sorry-free)
- ✅ Orthomodular lattice axiomatization + basic quantum structures (`NovelTheories.lean`)
- ✅ Classical Dempster–Shafer on `Finset Ω` (`Basic.lean`)
- ✅ Neighbor investigations (`NeighborTheories.lean`) are `sorry`-free
- ✅ Hypercube taxonomy order (`Taxonomy.lean`) is `sorry`-free
- ✅ Weakness preorder as a category (`WeaknessOrder.lean`)
- ✅ Quantale semantics + morphisms (`QuantaleSemantics.lean`)
- ✅ Θ-family ⇒ interval semantics API (`ThetaSemantics.lean`)
- ✅ Dense-vs-cyclic scale dichotomy bridge (`ScaleDichotomy.lean`, `DensityAxisStory.lean`)

### Corrected Misconceptions
- ❌ ~~OML fundamental lemma (quasi-distributivity)~~ - **FALSE in general OML!**
- ❌ ~~Bidirectional orthogonality criterion~~ - Only forward direction holds

### In Progress
- ⚠️ Infinite lattice case for quantum beliefs (requires measure theory)

## Relationship to Other Formalizations

### Knuth-Skilling Appendix A (`../KnuthSkilling/`)
Parallel formalization of K-S Appendix A (representation theorem):
- Different focus: derives real-valued probability from abstract lattice symmetries
- This directory: concrete instantiations (classical, quantum, D-S)

### Common Foundations (`../Common/`)
Shared infrastructure:
- `Lattice.lean`: Basic lattice utilities
- `Valuation.lean`: Abstract valuation functions
- `LatticeValuation.lean`: Normalized valuations, orthoadditive valuations
- `LatticeSummation.lean`: Summation over lattice principal ideals
- `MobiusFunction.lean`: Möbius inversion on lattices

### Belief Functions (`../BeliefFunctions/`)
Extended Dempster-Shafer theory:
- `Basic.lean`: Full D-S calculus with combination rules
- Bridges to hypercube formalization

## Design Philosophy

1. **No `sorry`**: files in this directory build without `sorry`; open directions live in comments/README, not as “Prop-as-proof” placeholders
2. **Source Attribution**: Every theorem cites original papers
3. **Modular Structure**: Each theory in separate file
4. **Computational Content**: Definitions executable on finite lattices
5. **Mathlib Integration**: Uses standard mathlib lattice theory where possible

## Future Work

1. ~~**Complete Foulis-Holland**~~ ✅ DONE: `commutes_inf`, `commutes_sup` proven
2. ~~**Distributive Sublattices**~~ ✅ DONE: `commuting_distributive` proven
3. **Weakness via Semantics**: connect `WeaknessOrder.lean` to `QuantaleSemantics.lean` morphisms
4. **Hypercube Edges**: formalize more edges (theory transformations) as explicit morphisms
5. **Measure Theory Bridge**: extend finite quantum beliefs to σ-algebras
6. **Concrete Examples**: MO5 lattice, projective geometries
7. **Decision Procedures**: automated reasoning about commutativity

## Contact

Part of the Mettapedia project formalizing mathematical foundations of inference, probability, and universal AI.

For questions about this formalization, see `lean-projects/mettapedia/CLAUDE.md`.

## Literature

See `literature/KS_codex/README.md` for complete bibliography including:
- Knuth-Skilling papers
- Cox's theorem proofs
- Ordered semigroup embeddings (Hölder, Alimov)
- Functional equations (Aczél)
- Orthomodular lattice theory (Kalmbach, Beran, Foulis)
