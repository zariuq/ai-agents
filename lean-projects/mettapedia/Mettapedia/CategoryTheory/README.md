# Category Theory foundations for OSLF, PLN & de Finetti (Lean 4)

`Mettapedia/CategoryTheory` provides the categorical foundations the rest of
Mettapedia builds on: a lambda-theory / native-type-theory strand (for OSLF and
PLN) and a categorical de Finetti strand (exchangeability as a limit-cone
universal property).

## Architecture

- The architecture is three main strands.
- Strand one is lambda theory and native type theory across seven files.
- Strand two is categorical de Finetti across the `DeFinetti*` files (interfaces, permutation/kernel cones, Giry/Markov bridges, exports, plus a smoke test and a counterexample).
- Strand three is supporting files for fuzzy frames, graph theory, and internal language.

### Lambda theory and native type theory strand

- `LambdaTheory.lean`
  - LambdaTheory.lean defines SubobjectFibration and LambdaTheory with finite limits and Heyting fibers

- `NativeTypeTheory.lean`
  - NativeTypeTheory.lean defines NativeTypeBundle as a Grothendieck construction

- `PLNInstance.lean`
  - PLNInstance.lean defines PLN as a frame-fiber instance with modal composition

- `PLNTerms.lean`
  - PLNTerms.lean defines PLN term syntax and reduction relation

- `ModalTypes.lean`
  - ModalTypes.lean defines modal types via comprehension and rely-possibly semantics

- `Hypercube.lean`
  - Hypercube.lean defines the H_Sigma endofunctor for modal type generation

- `PLNSemiringQuantale.lean`
  - PLNSemiringQuantale.lean defines a semiring quantale on Evidence with tensor and plus

### Categorical de Finetti strand

- `DeFinettiCategoricalInterface.lean`
  - DeFinettiCategoricalInterface.lean defines a qualitative factorization interface

- `DeFinettiPermutationCone.lean`
  - DeFinettiPermutationCone.lean proves permutation commutation of finite-prefix laws

- `DeFinettiKernelInterface.lean`
  - DeFinettiKernelInterface.lean defines kernel-level categorical de Finetti interfaces

- `DeFinettiSequenceKernelCone.lean`
  - DeFinettiSequenceKernelCone.lean defines sequence-kernel permutation cones on Bool power N

- `DeFinettiHausdorffBridge.lean`
  - DeFinettiHausdorffBridge.lean proves Hausdorff moment uniqueness links

- `DeFinettiPerNDiagram.lean`
  - DeFinettiPerNDiagram.lean defines per-n permutation diagram surfaces

- `DeFinettiGlobalFinitaryDiagram.lean`
  - DeFinettiGlobalFinitaryDiagram.lean defines global finitary-permutation indexing

- `DeFinettiLimitConePackage.lean`
  - DeFinettiLimitConePackage.lean packages the universal-property layer

- `DeFinettiKleisliGirySkeleton.lean`
  - DeFinettiKleisliGirySkeleton.lean defines Kleisli Giry global diagrams and IID cones

- `DeFinettiMarkovCategoryBridge.lean`
  - DeFinettiMarkovCategoryBridge.lean provides a MarkovCategoryCore viewpoint

- `DeFinettiExternalBridge.lean`
  - DeFinettiExternalBridge.lean provides bridges to vendored exchangeability formalization

- `DeFinettiStableExports.lean`
  - DeFinettiStableExports.lean provides stable alias exports

- `DeFinettiExports.lean`
  - DeFinettiExports.lean provides the recommended import surface

### Other

- `FuzzyFrame.lean`
  - FuzzyFrame.lean formalizes the unit interval frame for PLN truth values

- `GeneralizedOpenMaps.lean`
  - GeneralizedOpenMaps.lean defines the minimal generalized-open-map core:
    `BisimulationKit`, `GOpen`, `PathBisim`, `StrongPathBisim`, and `(E,S)`-style
    span witness equivalence (`pathBisim_iff_esBisimilar`)

- `TOGL.lean`
  - TOGL.lean formalizes Greg Meredith's theory of graphs

- `Topos/InternalLanguage.lean`
  - Topos/InternalLanguage.lean formalizes Kripke-Joyal semantics for OSLF

## Open-map bridge map

- `GeneralizedOpenMaps.lean`
  - Core theorem: `pathBisim_iff_esBisimilar`
- `../Languages/ProcessCalculi/PiCalculus/WeakBisimOpenMapBridge.lean`
  - Core theorem: `weakRestrictedBisim_iff_pathBisim`
- `../Languages/ProcessCalculi/PiCalculus/BranchingBisim.lean`
  - Core theorem: `branching_implies_weak`
- `../Logic/WeightedOpenMaps.lean`
  - Core theorem: `weightedBisim_iff_gopen_span`
- `../Logic/OSLFOpenMapBridge.lean`
  - Core theorem: `fullOpenWitness_implies_obsEq`

## Proof status

Every `.lean` file in this directory (29 as of 2026-05-31) is `sorry`-free,
`admit`-free, and `axiom`-free. Reproduce from this directory:

```bash
# real sorry/admit tactics + axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(sorry|admit)\b|^\s*(@\[[^]]*\]\s*)*(noncomputable\s+)?axiom\s' .
# the only "sorry"/"admit" tokens are in comments and prose (e.g. "processes admit a factorization"):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
```

## Dependency flow

The dependency flow is the following architecture diagram.

```
LambdaTheory -> PLNInstance -> NativeTypeTheory
                    |
              PLNTerms -> ModalTypes -> Hypercube

DeFinettiCategoricalInterface -> PermutationCone -> KernelInterface
  -> SequenceKernelCone -> HausdorffBridge -> PerNDiagram
  -> GlobalFinitaryDiagram -> KleisliGirySkeleton -> StableExports -> Exports
```
