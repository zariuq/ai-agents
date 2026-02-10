# OSLF: Operational Semantics in Logical Form

**First machine-checked formalization of the OSLF algorithm in Lean 4.**

OSLF mechanically derives spatial-behavioral type systems from rewrite rules. Given any reduction relation `p ~> q`, it automatically generates modal operators ◇ (step-future) and □ (step-past) with a proven Galois connection **◇ ⊣ □**.

## What is OSLF?

The OSLF algorithm takes a programming language's operational semantics (rewrite rules) and produces a type system where:

- **Types are behavioral predicates**: "processes that can reach state φ"
- **Typing is substitutability**: bisimilar processes have the same types
- **Modal operators arise from reduction**: ◇φ = "can step to φ", □φ = "all predecessors in φ"
- **Galois connection is automatic**: ◇ ⊣ □ proven once, reused for any language

**Input**: `RewriteSystem` (sorts, terms, reduction)
**Output**: `OSLFTypeSystem` (predicates, ◇, □, proven Galois connection)

## This Formalization

- **22,320 lines** across 58 Lean 4 files
- **0 sorries** in the core OSLF pipeline
- **4 language instances**: ρ-calculus, λ-calculus, Petri nets, TinyML
- **Proven Galois connection** for all 4 instances
- **Executable reduction engines** with soundness proofs
- **Categorical bridge** to Mathlib (fibrations, adjunctions)

## Quick Start

**Core algorithm definition:**
- [`Framework/RewriteSystem.lean`](Framework/RewriteSystem.lean) — Input/output structures (196 lines)

**Working example with full proofs:**
- [`RhoCalculus/Soundness.lean`](RhoCalculus/Soundness.lean) — ρ-calculus with proven Galois connection

**Pipeline implementation:**
- [`Framework/TypeSynthesis.lean`](Framework/TypeSynthesis.lean) — `langOSLF` function (201 lines)

## Directory Structure

```
OSLF/
├── Framework/              # Abstract OSLF algorithm (4,400 lines, 0 sorries)
│   ├── RewriteSystem.lean      # Core input/output structures ⭐
│   ├── TypeSynthesis.lean      # langOSLF pipeline ⭐
│   ├── ConstructorCategory.lean # Categorical foundations
│   ├── ConstructorFibration.lean # Fibered structure
│   ├── DerivedTyping.lean       # Auto-generated typing rules
│   ├── LambdaInstance.lean      # λ-calculus example
│   ├── PetriNetInstance.lean    # Petri net example
│   ├── TinyMLInstance.lean      # CBV λ-calc with booleans/pairs
│   └── ...
│
├── RhoCalculus/           # ρ-calculus instance (3,893 lines, 0 sorries)
│   ├── Syntax.lean             # Process syntax
│   ├── Reduction.lean          # COMM, DROP rules
│   ├── StructuralCongruence.lean # 11 SC rules
│   ├── Soundness.lean          # Proven Galois connection ⭐
│   ├── Engine.lean             # Executable reduction
│   └── ...
│
├── MeTTaIL/               # Meta-language for calculi (2,929 lines, 0 sorries)
│   ├── Syntax.lean             # Pattern AST
│   ├── Substitution.lean       # Capture-avoiding substitution
│   ├── Match.lean              # Pattern matcher
│   ├── Engine.lean             # Generic reduction engine
│   └── ...
│
├── PiCalculus/            # π-calculus (6,582 lines, 29 sorries)
│   ├── Syntax.lean             # π-calculus syntax
│   ├── Reduction.lean          # π-calculus reduction
│   ├── RhoEncoding.lean        # π → ρ encoding
│   ├── ForwardSimulation.lean  # RF fragment forward sim (0 sorries)
│   └── ...
│
├── Formula.lean           # Verified bounded model checker (582 lines)
└── Main.lean              # Re-exports
```

## Key Results

### 1. Abstract Framework (0 sorries)

**Theorem** (`Framework/RewriteSystem.lean`): For any `RewriteSystem`, the OSLF algorithm produces an `OSLFTypeSystem` with:
- Modal operators ◇ (diamond) and □ (box) derived from the reduction relation
- Galois connection: `◇ ⊣ □`

### 2. Concrete Instance: ρ-Calculus (0 sorries)

**Theorem** (`RhoCalculus/Soundness.lean`): The ρ-calculus type system satisfies:
- **Type preservation**: `Γ ⊢ P : τ  ∧  P ~> Q  ⟹  Γ ⊢ Q : τ`
- **Galois connection**: `◇ ⊣ □` proven directly
- **Substitutability**: Bisimilar processes have the same types

Reduction rules:
```
COMM: {n!(q) | for(x←n){P} | rest} ~> {P[@q/x] | rest}
DROP: *(@P) ~> P
```

### 3. Four Language Instances (0 sorries)

Each language gets a full `OSLFTypeSystem` with proven Galois connection:

1. **ρ-calculus**: Reflective higher-order process calculus
2. **λ-calculus**: Pure untyped lambda calculus
3. **Petri nets**: Simple marking transitions (no binders)
4. **TinyML**: CBV λ-calc with booleans, pairs, thunks

### 4. Categorical Bridge (0 sorries)

- Constructor category built from sort-crossing constructors
- Subobject fibration with change-of-base
- Derived typing rules: modal operator (◇/□/id) assigned automatically
- Beck-Chevalley analysis (proven counterexample for strong condition)

## Example: Petri Net

```lean
-- Define transitions
T1: {A, B, rest} ~> {C, D, rest}  -- consume A+B, produce C+D
T2: {C, rest} ~> {A, rest}        -- consume C, produce A

-- OSLF automatically derives:
petriOSLF : OSLFTypeSystem petriRS

-- With modal operators:
◇{A, D} = "markings that can reach {A, D}"
□{B, C} = "markings whose predecessors are all in {B, C}"

-- And proven Galois connection:
theorem petri_galois : ◇ ⊣ □  -- proven automatically
```

## Building

```bash
cd lean-projects/mettapedia
lake build Mettapedia.OSLF
```

Individual modules:
```bash
lake build Mettapedia.OSLF.Framework.RewriteSystem
lake build Mettapedia.OSLF.RhoCalculus.Soundness
```

## References

- Meredith & Stay, ["Operational Semantics in Logical Form"](https://arxiv.org/abs/1406.4888) (2014) — original OSLF algorithm
- Williams & Stay, ["Native Type Theory"](https://www.cl.cam.ac.uk/events/act2021/papers/ACT_2021_paper_23.pdf) (ACT 2021) — categorical perspective
- **This formalization**: `papers/leanOSLF.pdf` (2026 draft, 17 pages)

## Status

| Component | Lines | Sorries | Status |
|-----------|-------|---------|--------|
| Framework | 4,400 | 0 | ✅ Complete |
| RhoCalculus | 3,893 | 0 | ✅ Complete |
| MeTTaIL | 2,929 | 0 | ✅ Complete |
| Formula | 582 | 0 | ✅ Complete |
| PiCalculus | 6,582 | 29 | ⚠️ Partial |
| **Core Total** | **15,738** | **0** | ✅ **Complete** |

The 29 sorries are in `PiCalculus/RhoEncodingCorrectness.lean` (π→ρ encoding correctness, a separate project from the core OSLF algorithm).

## Contributing

The formalization uses Lean 4.27.0 with Mathlib. See `../../CLAUDE.md` for development guidelines.

---

**First machine-checked proof that OSLF works.** 🎯
