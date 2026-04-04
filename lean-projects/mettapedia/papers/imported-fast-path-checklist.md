# Imported Fast-Path Enablement Checklist

**For MORK/PathMap implementers considering enabling more of the imported-row
fast path without losing CeTTa semantics.**

## Current Status (April 2026)

CeTTa's imported backend operates in **dual-layer defensive mode**:
- Bridge provides **candidate indices only** (not bindings)
- Every candidate is **rematched natively** via `space_subst_match_with_seed`
- The V2 binding packet path is **disabled** (`__attribute__((unused))`)
- Comment: "bridge-side binding packets were semantically brittle on real recursive workloads"

This is binding-correct by the proved theorems in `SeedRematchContract.lean`.

## Proved Theorems (Lean 4, 0 sorry)

| Theorem | File | What it guarantees |
|---------|------|-------------------|
| `importedFallbackParity` | ImportedRowContract.lean | bridge candidates + native rematch = correct candidate set |
| `seedRematch_extends_seed` | SeedRematchContract.lean | seeded rematch extends seed (no dropped bindings) |
| `seedRematchSafe_no_loop` | SeedRematchContract.lean | loop detection rejects unsound chains |
| `conjunctionStep_preserves_seed` | SeedRematchContract.lean | conjunction loop preserves all prior bindings |
| `skip_rematch_correct` | SeedRematchContract.lean | exact + loop-free → skip rematch safely |
| `full_rematch_always_safe` | SeedRematchContract.lean | full rematch always correct |
| `accepted_iff_not_rejected` | ImportedRowContract.lean | packet acceptance/rejection complementary |

## Checklist: What Must Be True Before Enabling Direct Bridge Bindings

### Gate 1: Packet Validation (currently enforced)

- [x] **All bindings are query-side only** (`side == 0`)
  - Runtime check: `space_match_backend.c:1625`
  - Lean precondition: `PacketRow.isAccepted`
  - Status: ENFORCED. Candidate-side bindings are rejected.

- [x] **No VarRef tags in value payloads**
  - Runtime check: `space_match_backend.c:765-769`
  - Lean precondition: `RematchFreeSafe.valuesGround`
  - Status: ENFORCED. Values with varref prefix are rejected.

- [x] **No ambiguous 63-byte tokens**
  - Runtime check: `space_match_backend.c:710-716`
  - Lean precondition: not formalized (encoding detail)
  - Status: ENFORCED. 63-byte tokens are rejected.

### Gate 2: Query Classification (currently enforced)

- [x] **No epoch-tagged variables in query**
  - Runtime check: `space_match_backend.c:1908` `imported_atom_has_epoch_vars`
  - Lean precondition: `RematchFreeSafe.queryNoEpoch`
  - Status: ENFORCED. Epoch queries go to candidates-only mode.

### Gate 3: Binding Correctness (NOT yet verified for bridge bindings)

- [ ] **Bridge bindings match what `simpleMatch` would produce**
  - Lean precondition: `RematchSkipCondition.exact`
  - Status: NOT VERIFIED. This is the main blocker.
  - What's needed: prove that `imported_bridge_parse_value_raw_query_only_v2`
    produces the same bindings as `match_atoms` for the supported fragment.

- [ ] **Merged bindings are loop-free**
  - Lean precondition: `RematchSkipCondition.noLoop`
  - Status: ENFORCED in the fast path (`bindings_has_loop` check at line 2571),
    but the overall path is disabled.

- [ ] **`bindings_clone_merge` preserves seed + adds new bindings**
  - Lean precondition: `Bindings.Extends` (from `BindingComposition.lean`)
  - Status: NOT FORMALLY VERIFIED. The C implementation uses
    `bindings_try_merge_inplace` which unifies conflicting bindings
    via `match_atoms` — this is correct but not formally proved.

### Gate 4: Bridge State Synchronization

- [ ] **Bridge is synchronized with live space (no stale candidates)**
  - Lean precondition: `ImportedCandidates.sound` (bridge returns superset of true matches)
  - Status: PARTIALLY ENFORCED. The `dirty` flag and rebuild logic exist,
    but late adds between rebuild and query can cause under-approximation.
  - Related test: `test_imported_fallback_late_add_regression.metta`

## Recommended Enablement Path

### Phase 1: Validate bridge binding correctness (no code changes)

1. Add a **diagnostic mode** that runs BOTH paths (bridge bindings AND native rematch) and compares results.
2. Use the existing `CETTA_RUNTIME_COUNTER_IMPORTED_BRIDGE_V2_FALLBACK` counter to measure how often the bridge path would be taken.
3. Run the full test suite in diagnostic mode. Any disagreement = bridge binding bug.

### Phase 2: Enable for ground-only queries — IMPLEMENTED

The safest fragment, now enabled in `space_match_backend.c`:
- Query has NO variables (checked by `imported_atom_has_vars()`)
- Match result is trivially exact (no bindings to produce)
- Tracked by `CETTA_RUNTIME_COUNTER_IMPORTED_V2_GROUND_SKIP`

Implementation: in `imported_query()`, before the V2 fallback counter,
ground queries are routed to `imported_bridge_query_bindings_query_only_v2()`.
If the bridge succeeds, the result is returned directly. If it fails,
execution falls through to the existing native rematch path.

For this fragment:
- `RematchSkipCondition.exact` is trivially satisfied (ground match = exact)
- `RematchSkipCondition.noLoop` is trivially satisfied (no bindings = no loops)
- All `RematchFreeSafe` conditions are met

### Phase 3: Enable for single-variable queries — SPECIFIED (not enabled)

Next safest: queries like `(= "constant" $x)` where only one variable binds.

**Lean preconditions** (proved in `ImportedRowContract.lean §6b`):
- `SingleVarSafe.queryNoEpoch` — no epoch variables
- `SingleVarSafe.bindingsQuerySide` — query-side only
- `SingleVarSafe.singleBinding` — exactly one binding entry
- `SingleVarSafe.valueGround` — binding value is structurally ground
- `singleVarSafe_implies_rematchFreeSafe` — implies the general safety condition
- `ground_value_no_loop_risk` — ground values cannot create binding loops
- `singleBinding_merge_decidable` — merge has exactly one decision point

**Remaining blockers before enablement:**
- [ ] Verify `imported_bridge_parse_value_raw_query_only_v2` correctly decodes the bound value for single-variable cases
- [ ] Verify the decoded value is structurally identical to what `simpleMatch` would produce
- [ ] Add a runtime check: `atomVarCount(query) == 1 && atomIsGround(decoded_value)`

**Conformance tests** (already passing under native rematch):
- `test_single_var_binding_conformance.metta` — positive cases
- `test_single_var_negative_cases.metta` — boundary cases that must stay native

### Phase 4: Enable for multi-variable queries (full V2)

Requires:
- Full `bindings_clone_merge` correctness verification
- Multi-variable loop detection
- Epoch variable handling for nested equation matching

## Regression Tests Needed

| Test | What it verifies | Maps to |
|------|-----------------|---------|
| `test_seed_rematch_extends.metta` | Seed bindings survive through match chain | `seedRematch_extends_seed` |
| `test_imported_binding_parity.metta` | Bridge + rematch = native for binding content | `imported_seedRematch_binding_parity` |
| `test_exact_skip_ground.metta` | Ground match skips rematch correctly | `skip_rematch_correct` |
| `test_single_var_binding_conformance.metta` | Single-var queries produce correct bindings | `SingleVarSafe` |
| `test_single_var_negative_cases.metta` | Multi-var/non-ground cases stay native | `SingleVarSafe` (negation) |

## Runtime Counter Reference

| Counter | What it tracks |
|---------|---------------|
| `CETTA_RUNTIME_COUNTER_IMPORTED_BRIDGE_V2_FALLBACK` | Times V2 binding path fell back to native |
| `CETTA_RUNTIME_COUNTER_IMPORTED_BRIDGE_V3_FALLBACK` | Times conjunction fast path fell back |

## Files Reference

| File | Role |
|------|------|
| `space_match_backend.c:1900-1960` | `imported_query` decision tree |
| `space_match_backend.c:2561-2600` | `space_subst_match_with_seed` |
| `space_match_backend.c:2082-2125` | `space_query_conjunction_default` |
| `space_match_backend.c:1625` | Side check (candidate-side rejection) |
| `space_match_backend.c:750-830` | Packet value parsing/validation |
| `mork_space_bridge_runtime.h` | Bridge API |
| `specs/pathmap_bridge_varid_abi.json` | V2 packet format spec |
