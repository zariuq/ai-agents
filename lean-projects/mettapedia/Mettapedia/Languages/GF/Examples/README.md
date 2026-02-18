# End-to-End Pipeline Examples

Three worked examples proving the complete GF-to-evidence pipeline:

```
GF Abstract Tree -> Pattern -> GrammarState (V1-V4) -> QFormula2 -> Evidence
```

Each example exercises different visible semantic actions (V1-V4 from TUG theory)
and proves correctness at every pipeline stage.

## Examples

### EveryManWalks.lean
**"Every man walks"** — Universal quantification.

Pipeline stages (all proven):
1. GF tree: `UseCl (TTAnt TPres ASimul) PPos (PredVP (DetCN every_Det (UseN man_N)) (UseV walk_V))`
2. Pattern matching and grammar rule application
3. V1: Quantifier storage (every -> store)
4. QFormula2: `forall x. man(x) -> walk(x)`
5. Closedness proof and evidence structure

### ScopeAmbiguity.lean
**"Every man loves a woman"** — Scope ambiguity with two quantifiers.

Demonstrates nondeterministic scope choice:
- Surface scope: `forall x. man(x) -> exists y. woman(y) /\ loves(x,y)`
- Inverse scope: `exists y. woman(y) /\ forall x. man(x) -> loves(x,y)`

Proven: both readings are well-formed, scope ordering is preserved,
auto-assembly succeeds for both readings.

### AnaphoraBinding.lean
**Cross-sentential anaphora** — Pronoun binding across sentences.

Demonstrates V3 (referent introduction) + V4 (pronoun binding):
1. First sentence introduces a referent into the store
2. Second sentence contains a pronoun
3. V4 binds the pronoun to the referent
4. Evidence changes from bottom (unresolved) to real value

Proven: store resolution, semantic change (bottom -> evidence),
base-visible separation, functional bind, unique referent invariant.

## What's Proven

Every pipeline stage in every example has a corresponding Lean theorem.
Zero sorries, zero axioms. The proofs establish that the semantic pipeline
is end-to-end correct for these examples.
