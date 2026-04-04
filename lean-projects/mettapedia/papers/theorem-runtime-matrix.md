# Theorem → Runtime → Regression Matrix

Maps each proved Lean theorem to its CeTTa runtime seam and regression test target.

## PathMap / Candidate Architecture

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `twoPhase_eq_direct` | CandidateArchitecture.lean | `space_match_backend.c` candidate+filter | `test_candidate_filter_correctness.metta` |
| `concrete_twoPhase_eq_direct` | CandidateArchitecture.lean | `space_match_backend.c` trie selector | `test_trie_candidate_selection.metta` |
| `trieCandidates_subset_support` | CandidateArchitecture.lean | `space_match_backend.c` no-phantom | `test_no_phantom_candidates.metta` |
| `addAtom_support_of_mem` | CandidateArchitecture.lean | `space.c` `space_add` duplicate path | `test_dup_add_no_trie_change.metta` |
| `addAtom_support_of_not_mem` | CandidateArchitecture.lean | `space.c` `space_add` new atom path | `test_new_add_extends_support.metta` |
| `decCount_support_of_high` | CandidateArchitecture.lean | `space.c` `space_remove` high-count | `test_remove_high_count_stable.metta` |
| `decCount_support_of_last` | CandidateArchitecture.lean | `space.c` `space_remove` last copy | `test_remove_last_shrinks.metta` |
| `support_stable_preserves_all_queries` | CandidateArchitecture.lean | `table_store.c` cache policy | `test_dup_add_cache_valid.metta` |
| `cache_policy_growing` | CandidateArchitecture.lean | `table_store.c` selective invalidation | `test_new_add_invalidates_matching.metta` |
| `cache_policy_shrinking` | CandidateArchitecture.lean | `table_store.c` selective invalidation | `test_remove_invalidates_matching.metta` |
| `BackendContract` | CandidateArchitecture.lean | `space_match_backend.c` contract | (structural, not test-level) |
| `prefixCandidates_sound` | CandidateArchitecture.lean | PathMap prefix descent | `test_prefix_narrowing_sound.metta` |
| `realPrefixSelector_sound` | CandidateArchitecture.lean | **Real subtreeAt descent** | `test_real_prefix_descent.metta` |
| `realPrefixSelector_subset_support` | CandidateArchitecture.lean | No-phantom for real descent | `test_real_prefix_no_phantom.metta` |
| `subtreeAt_lookup` | FiniteTrie.lean | Trie prefix navigation | (structural invariant) |
| `lookup_mem_entries` | LookupEntries.lean | Lookup ↔ entries bridge | (structural invariant) |

## Trie Correctness

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `graftAtPath_lookup_under` | FiniteTrie.lean | trie mutation | `test_graft_lookup_under.metta` |
| `graftAtPath_preserves_lookup` | FiniteTrie.lean | trie mutation | `test_graft_disjoint_preserved.metta` |
| `join_sorted` | SortedPreservation.lean | trie join | (structural invariant) |
| `fromPathList_mem` | SortedPreservation.lean | trie build | `test_pathlist_all_findable.metta` |
| `cata_recCount` | MorphismCorrectness.lean | trie fold | (structural invariant) |
| `cata_rebuild_lookup` | MorphismCorrectness.lean | trie fold | (structural invariant) |

## Zipper Navigation

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `ascend_descend_roundtrip` | HuetZipper.lean | zipper navigation | (structural invariant) |
| `focus_lookup_general` | HuetZipper.lean | zipper query | (structural invariant) |
| `rebuild_of_reachable` | HuetZipper.lean | zipper rebuild | (structural invariant) |

## HE Backend Bridge

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `support_bind` | BagSupportBridge.lean | query composition | (semantic invariant) |
| `same_support_same_trie` | HEBridge.lean | trie dedup | `test_dup_atoms_one_trie_entry.metta` |
| `add_dup_trie_invariant` | HEBridge.lean | `space.c` add path | `test_dup_add_trie_unchanged.metta` |
| `end_to_end_pipeline` | HEInterface.lean | full backend | (integration theorem) |

## HE Matcher Instance

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `he_twoPhase_eq_direct` | PathMapMatcherInstance.lean | `space_match_backend.c` with HE matching | `test_he_matcher_twoPhase.metta` |
| `matchAtoms_self_symbol` | PathMapMatcherInstance.lean | `match_atoms_epoch` identity case | (structural) |
| `matchAtoms_var_any` | PathMapMatcherInstance.lean | `match_atoms_epoch` variable case | (structural) |
| `not_match_not_in_direct` | PathMapMatcherInstance.lean | match failure = exclusion | (structural) |

## Worked Example

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `worked_twoPhase_eq_direct` | WorkedExample.lean | End-to-end 5-atom | `test_five_atom_query.metta` |
| `directQuery_is_full_support` | WorkedExample.lean | Variable query = full support | `test_var_query_all_atoms.metta` |

## Full Pipeline

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `full_pipeline` | HEInterface.lean | **Complete backend chain** | (integration theorem) |

## Canonical Universe (term_universe.c / atom.c)

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `applyRenaming_of_epochFree` | CanonicalUniverse.lean | `term_universe_store_atom` no-op path | (structural) |
| `applyRenaming_epochFree_output` | CanonicalUniverse.lean | `term_universe_canonicalize_atom` output | (structural) |
| `findPosition_injective` | CanonicalUniverse.lean | ordinal assignment | (structural) |
| `mkCanonicalRenaming_injective` | CanonicalUniverse.lean | **co-reference preservation** | `test_coref_preserved_after_store.metta` |
| `hashConsSafe_of_varFree_immutable` | CanonicalUniverse.lean | `atom_can_hashcons()` | (structural) |
| `varFree_implies_epochFree` | CanonicalUniverse.lean | var-free → epoch-free | (structural) |

## Binding / Co-reference (CB's domain)

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `store_preserves_coreference` | (planned: CanonicalUniverse.lean) | `term_universe.c` | `test_coref_preserved_after_store.metta` |
| `binding_extension_compose` | BindingComposition.lean | `space_match_backend.c` seed/rematch | `test_binding_compose_correct.metta` |
| `variant_key_faithful` | VariantQueryCorrectness.lean | `table_store.c` cache key | `test_variant_key_cache_hit.metta` |
| `simpleMatch_rename_bisim` | VariantQueryCorrectness.lean | `table_store.c` variant-key bisimulation | (integration theorem) |
| `variant_queries_same_rhs` | VariantQueryCorrectness.lean | `table_store.c` variant RHS stability | (integration theorem) |
| `applyAtomTotal_injective` | CoReferencePreservation.lean | `term_universe.c` canonical injective | (structural) |

## Seeded Rematch (space_subst_match_with_seed)

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `seedRematch_extends_seed` | SeedRematchContract.lean | `space_subst_match_with_seed` | `test_seed_rematch_extends.metta` |
| `seedRematchSafe_no_loop` | SeedRematchContract.lean | `bindings_has_loop` rejection | `test_loop_rejected.metta` |
| `conjunctionStep_sound` | SeedRematchContract.lean | `space_query_conjunction_default` | `test_conjunction_correct.metta` |
| `imported_seedRematch_binding_parity` | SeedRematchContract.lean | imported candidates + rematch | `test_imported_binding_parity.metta` |
| `skip_rematch_correct` | SeedRematchContract.lean | `sm->exact` fast path | `test_exact_skip_ground.metta` |
| `full_rematch_required` | SeedRematchContract.lean | non-exact rematch boundary | (structural) |

## CeTTa Runtime Contracts

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `Canonicalization.apply_injective` | CeTTaRuntimeContracts.lean | `term_universe_canonicalize_atom` | `test_canon_roundtrip_contracts.metta` |
| `Canonicalization.preserves_beq` | CeTTaRuntimeContracts.lean | `term_canon.c` BEq | (structural) |
| `Canonicalization.variant_cache_safe` | CeTTaRuntimeContracts.lean | `table_store.c` variant key | (integration theorem) |
| `BindingsBuilder.rollback_discards_new` | CeTTaRuntimeContracts.lean | `search_context_rollback` | (structural) |
| `BindingsBuilder.rollback_idempotent` | CeTTaRuntimeContracts.lean | double-rollback safety | (structural) |
| `lowering_eligible_iff_pure` | CeTTaRuntimeContracts.lean | `runtime_effect_classes.json` | (structural) |
| `he_compat_always_available` | CeTTaRuntimeContracts.lean | `session.c` profile | (structural) |

## PathMap Byte-Order Refinement (scheduler fragment)

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `symbolSizeTag_nat_mono` | PathMapByteOrderRefinement.lean | tag byte monotonicity | (structural) |
| `ascii_byte_order` | PathMapByteOrderRefinement.lean | byte = char order for ASCII | (structural) |
| `scheduler_byte_faithful` | PathMapByteOrderRefinement.lean | abstract = byte order on fragment | (structural) |
| `scheduler_pop_order_correct` | PathMapByteOrderRefinement.lean | `metta_calculus` pop order | (structural) |

## MM2 Bridge Round-Trip

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `mm2_raise_lower` | Mm2BridgeRoundTrip.lean | `mm2_lower.c` / `mm2_raise_atom` | `mm2_lowering_core.metta` |
| `mm2_lower_injective` | Mm2BridgeRoundTrip.lean | symbol uniqueness | (structural) |
| `mm2_raise_surjective` | Mm2BridgeRoundTrip.lean | every IR sym raiseable | (structural) |

## Incremental Tabling

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `TableEntry.addAnswer_sound` | IncrementalTableSemantics.lean | future `table_store_check_insert` | (spec-first) |
| `TableEntry.exact_is_sound` | IncrementalTableSemantics.lean | table completion | (spec-first) |
| `tableEntry_addAtom_invalidates` | IncrementalTableSemantics.lean | revision invalidation | (spec-first) |

## Producer Choice Points

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `save_rollback_identity` | ProducerChoicePoint.lean | `search_context_save/rollback` | (structural) |
| `nested_save_rollback` | ProducerChoicePoint.lean | nested backtracking | (structural) |
| `producer_rollback_consumer_stable` | ProducerChoicePoint.lean | consumer isolation | (structural) |

## Imported Row Contract (space_match_backend.c imported_query)

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `importedFallbackParity` | ImportedRowContract.lean | `imported_query` V2 path | `test_imported_candidates_correct.metta` |
| `importedQuery_always_correct` | ImportedRowContract.lean | full decision tree | (integration theorem) |
| `accepted_iff_not_rejected` | ImportedRowContract.lean | side check at line 1625 | (structural) |
| `PacketRow.isAccepted` | ImportedRowContract.lean | query-side-only validation | (structural) |
| `uniqueSupport_count_pos` | ImportedRowContract.lean | logical vs unique | (structural) |
| `queryResult_depends_on_uniqueSupport` | ImportedRowContract.lean | query uses support only | (structural) |
| `localWrite_shadows_base` | ImportedRowContract.lean | overlay shadow semantics | (structural) |
| `SingleVarSafe` | ImportedRowContract.lean | single-var fragment preconditions | `test_single_var_binding_conformance.metta` |
| `singleVarSafe_implies_rematchFreeSafe` | ImportedRowContract.lean | single-var → general safety | (structural) |
| `ground_value_no_loop_risk` | ImportedRowContract.lean | ground values can't loop | (structural) |
| `singleBinding_merge_decidable` | ImportedRowContract.lean | merge has one decision point | (structural) |

## Overlay / Merkle / Serialization

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `overlay_lookup_eq_join` | ProductOverlayZipper.lean | with-space-snapshot | (structural) |
| `descendPath_lookup` | ProductOverlayZipper.lean | overlay prefix descent | (structural) |
| `merkleHash_deterministic` | Merkleization.lean | content-addressable identity | (structural) |
| `merkleHash_singleton_cons` | Merkleization.lean | hash step unfold | (structural) |
| `serialize_deterministic` | Serialization.lean | wire format stability | (structural) |
| `serialize_leaf` | Serialization.lean | leaf format correct | (structural) |

## Space Engine Boundary

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `shared_space_surface` | SpaceEngineBoundary.lean | `space_add/match/get_type` universal | (structural) |
| `pathmap_query_surface_only` | SpaceEngineBoundary.lean | PathMap has no execStep | (structural) |
| `step_semantics_only_mork` | SpaceEngineBoundary.lean | execStep is MORK-exclusive | (structural) |
| `act_artifact_not_exec_authority` | SpaceEngineBoundary.lean | ACT is storage, not execution | (structural) |
| `mm2_requires_exec_surface` | SpaceEngineBoundary.lean | MM2 needs MORK | (structural) |
| `engine_surface_inclusion_native_pathmap_mork` | SpaceEngineBoundary.lean | native ⊂ pathmap ⊂ mork | (structural) |

## Native Ground Fast Path (match.c dispatch)

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `ground_symbol_eq` | NativeGroundFastPath.lean | `match_atoms_ground` symbol branch | (structural) |
| `ground_grounded_eq` | NativeGroundFastPath.lean | `match_atoms_ground` grounded branch | (structural) |
| `open_ground_simpleMatch_complete` | NativeGroundFastPath.lean | open-pattern + ground-target dispatch | (structural) |
| `open_open_requires_matchAtoms` | NativeGroundFastPath.lean | open-open needs full match_atoms | (structural) |
| `ground_candidate_no_loop_check_needed` | NativeGroundFastPath.lean | skip `bindings_has_loop` for ground | (structural) |
| `ground_dispatch_symbol_eq` | NativeGroundFastPath.lean | dispatch = simpleMatch for symbols | (structural) |
| `ground_dispatch_open_ground` | NativeGroundFastPath.lean | dispatch = simpleMatch for open patterns | (structural) |

## ACT Artifact Boundary

| Theorem | Lean File | Runtime Seam | Regression Test |
|---------|-----------|-------------|-----------------|
| `act_never_grants_exec` | ACTArtifactBoundary.lean | all ACT ops exec-free | (structural) |
| `act_artifact_engine_neutral` | ACTArtifactBoundary.lean | ACT works with any engine | (structural) |
| `act_open_shared_query_surface` | ACTArtifactBoundary.lean | `mork_space_open_act_native` | (structural) |
| `act_not_mm2_semantics` | ACTArtifactBoundary.lean | ACT ≠ MM2 execution | (structural) |
| `act_helpers_refine_space_engine_boundary` | ACTArtifactBoundary.lean | format + ops exec-free | (structural) |

## Status Key

- **Proved**: theorem exists, 0 sorry, build green
- **Planned**: theorem identified, not yet formalized
- **Structural**: theorem protects an invariant, not directly testable at MeTTa level
- **Integration**: theorem bundles multiple properties, tested via constituent parts
