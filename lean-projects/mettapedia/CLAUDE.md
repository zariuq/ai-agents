# MeTTapedia — Lean 4 + Mathlib Formalization Project

## What This Is
Formal verification of the mathematical foundations underlying OpenCog Hyperon / MeTTa / PLN.
~2300 Lean files, ~700K lines. Lake project with Mathlib dependency.

## Build & Check
```bash
lake build              # full project build (slow)
lake env lean <file>    # check single file (preferred for dev)
```

## Key Directories

### `Mettapedia/GSLT/` — Graph-Structured Lambda Theories
- `Core/` — Lambda theories as categories (CCC + finite limits + subobject fibration)
- `GraphTheory/` — Graph models, Böhm trees, parallel reduction, Church-Rosser
- `Topos/` — Presheaf topos (Yoneda, subobject classifier, predicate fibration)
- `Meredith/` — **Meredith (2026) framework** formalization
  - `GSLT.lean` — Def 2.1: GSLT triple (terms, equations, rewrites)
  - `LambdaTheory.lean` — Def 4.1: Lambda theory (CCC + Pr + ⇝ + base rewrites)
  - `RhoExample.lean` — Rho calculus as GSLT instance
  - `Modal/` — Hypercube modal layer (§5: ⟨K_j⟩ modalities, ♢, Π)

### `Mettapedia/OSLF/` — Operational Semantics in Logical Form
- `Framework/` — Core OSLF machinery:
  - `ModalHypercube.lean` — Sort slots, equational center Z (Def 5.1)
  - `RewriteSystem.lean` — Base rewrites
  - `GeneratedTyping.lean` — Automated typing from language defs
  - `ReversibilityEnvelope.lean` — Time-symmetric S†
  - `BisimulationFiber.lean` — Bisimulation structure
  - `HypercubeGSLTFunctor.lean` — Hypercube ↔ GSLT bridge

### `Mettapedia/Languages/ProcessCalculi/`
- `RhoCalculus/` — Full ρ-calculus: syntax, reduction, structural congruence, contexts, types, soundness
- `PiCalculus/` — π-calculus with encoding to/from ρ
- `MQCalculus/` — MQ-calculus
- `MeTTaCalculus/` — MeTTa as process calculus
- `MORK/` — MORK execution engine

### `Mettapedia/Logic/` — PLN and reasoning
- `WorldModelCore.lean` — World model calculus
- `EvidenceClass.lean`, `BinaryEvidence.lean` — Evidence theory
- PLN inference rules, deduction, temporal/causal inference

### `Mettapedia/ProbabilityTheory/` — Probability foundations
- `Hypercube/` — Probability hypercube (PLN's setting)
- `KnuthSkilling/` — Knuth-Skilling foundations of inference
- `QuantumProbability/` — Quantum probability basics

### `Mettapedia/CategoryTheory/` — Category-theoretic infrastructure
- `LambdaTheory.lean`, `NativeTypeTheory.lean`, `Hypercube.lean`

### `Mettapedia/Languages/GF/` — Grammatical Framework bridge
### `Mettapedia/Languages/MeTTa/` — MeTTa language formalization

## Conventions
- **Use Mathlib**: Category, Functor, Frame, Setoid, etc. Don't reinvent.
- **Cite sources**: Every definition docstring references the paper/section it formalizes.
- **No hacks**: Definitions must faithfully represent the mathematics. `sorry` only for deep lemmas (mark with `-- TODO: prove`).
- **Bottom-up**: Each file must compile independently with its imports.
- **Compile check**: Always run `lake env lean <file>` after writing/editing.
- **Namespaces**: Follow `Mettapedia.<Area>.<Subarea>` pattern.

## Source Papers (in `papers/`)
See `papers/README.md` for full index. Key references:
- `papers/meredith/` — Meredith's GSLT/Hypercube framework (2026)
- `papers/meredith/FORMALIZATION-PLAN.md` — Detailed gap analysis and plan

## Current Focus
Formalizing Meredith (2026) framework: GSLT → Lambda theories → Modal hypercube → Physical structure.
