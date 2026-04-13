# Bridge

Mettapedia/Bridge connects cross-module formalizations.

## Files

### `BitVectorEvidence.lean` (0 sorry)

Geometric semantics for PLN evidence. Positive and negative evidence counts
correspond to known bits in partial bit vectors. Unknown bits give a
combinatorial interpretation of uncertainty.

Key results:
- `completions_card`: |completions(v)| = 2^(countUnknown v)
- `completions_mean_weight`: average Hamming weight = (pos + unknown/2) / n
- `toEvidence_strength`: Evidence.strength = expected fraction of 1s

This bridge connects discrete evidence to continuous Beta distribution theory.

### `CeTTaExplicitSubst.lean` (0 sorry)

Builds the formal support layer for CeTTa's Layer 3 explicit-substitution
story. It already contains the core closure/materialization definitions and a
useful set of support lemmas, but it does not yet establish the strongest
roundtrip and composition bridge theorems.

Key definitions:
- `ExplicitClosure`: The ⟨M, σ⟩ closure type (skeleton + env)
- `materialize`: Apply substitution (M[σ])
- `canonicalize`: Extract free variables into closure
- `composeEnv`: Substitution composition (σ₁ ∘ σ₂)
- `slotName`: Slot naming convention (_slot_0, _slot_1, ...)
- `enumFrom`: Helper for indexed enumeration
- `buildSlotMaps`: Construct slotEnv and reverseMap from free variables

Key theorems:
- `materialize_eq_applySubst`: Definitionally true (rfl)
- `materialize_trivial`: Empty env case (rfl)
- `materialize_empty_env`: Empty env contract (rfl)
- `materialize_trivial_closure`: Trivial closure case (rfl)
- `Nat.repr_injective`: Decimal rendering is injective
- `slotName_injective`: Slot names are injective
- `enumFrom_length`: Length preservation
- `mem_enumFrom`: Index membership
- `mem_enumFrom_of_mem`: Element membership
- `skeletonEquiv_refl/symm/trans`: Equivalence relation
- `canonicalize_ground`: Ground patterns have empty env

Still missing:
- `canonicalize_materialize_id`: Roundtrip property
- `applySubst_compose`: Composition distributes
- `env_compose_assoc`: Composition is associative

References:
- Abadi et al., "Explicit Substitutions", JFP 1991
- CeTTa: `c-projects/CeTTa-TermUniverse/src/variant_shape.h`
- Roadmap: `papers/cetta_roadmap.tex` Section 8 (Dual-Target Architecture)

## Status

- BitVectorEvidence: 0 sorry (complete)
- CeTTaExplicitSubst: 0 sorry (support layer complete enough to compile cleanly,
  but the main bridge theorems are still deferred)
