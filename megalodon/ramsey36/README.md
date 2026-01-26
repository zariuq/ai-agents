# Ramsey R(3,6)=18 Proof - Megalodon Formalization

**Goal**: Prove R(3,6) = 18 to claim 800 bar ProofGold bounty at address `TMbJ1MogStdKCGN3J3j1hThprkcWjA8ggEB`.

**Source**: Complete Lean 4 proof (15,021 lines, zero sorries) at `/home/zar/claude/lean-projects/ramsey36/`

**Plan**: `/home/zar/.claude/plans/mighty-greeting-gizmo.md` (16 weeks, ~5,700 lines estimated)

## Phase 1: COMPLETE ✅ (2025-12-18)

**Deliverables**:
- ✅ Workspace set up at `/home/zar/claude/megalodon/ramsey36/`
- ✅ `preamble.mgs` (6107 lines) - Full Egal theory foundation
- ✅ `r36_definitions.mg` (27 lines) - Graph theory foundations, compiles successfully

**Files**:
```bash
./bin/megalodon -I preamble.mgs r36_definitions.mg  # EXIT 0
```

**Definitions included**:
- `TwoRamseyProp` - Core Ramsey property definition
- `is_graph` - Graph validity (symmetric, irreflexive)
- `triangle_free` - No 3-cliques
- `no_k_indep` - No k-independent sets
- `neighbors` - Neighborhood function
- `common_neighbors` - Intersection of neighborhoods
- `degree` - Vertex degree (equip-based)
- `k_regular` - Regular graph predicate

## Phase 2: R(3,4) = 9 (Weeks 3-5)

**Status**: Not started

**Deliverable**: `r36_small_ramsey.mg` with complete proof of R(3,4)=9

**Strategy**:
- Lower bound: 8-vertex witness graph (triangle-free + no 4-IS)
- Upper bound: Decision tree using R(3,3)=6 as sublemma
- Estimated: ~800 lines

**Source Lean file**: `Ramsey36/SmallRamsey.lean` lines 20-400

## Phase 3: R(3,5) = 14 (Weeks 6-8)

**Status**: Not started

**Deliverable**: `r36_small_ramsey.mg` extended with R(3,5)=14

**Strategy**:
- Lower bound: 13-vertex witness graph
- Upper bound: Decision tree using R(3,4)=9
- Estimated: ~1000 lines

**Source Lean file**: `Ramsey36/SmallRamsey.lean` lines 400-1367

## Phase 4: Lower Bound R(3,6) > 17 (Weeks 9-10)

**Status**: Not started

**Deliverable**: `r36_lower_bound.mg` proves `~TwoRamseyProp 3 6 17`

**Strategy**: 17-vertex witness (Graver-Yackel variant)
- Structural proof of triangle-free (NOT 680-triple enumeration)
- Structural proof of no 6-IS (NOT 12,376-subset enumeration)
- Estimated: ~500 lines

**Source Lean file**: `Ramsey36/Critical17.lean`

## Phase 5: Upper Bound R(3,6) ≤ 18 (Weeks 11-15)

**Status**: Not started

**Deliverable**: `r36_upper_bound.mg` proves `TwoRamseyProp 3 6 18`

**Strategy**: Cariolaro method (regularity constraints)
- Claim 1: 5-regularity (~800 lines)
- Claim 2: P/Q partition (~1000 lines)
- Claim 3: P forms 4-cycle (~800 lines)
- Final contradiction (~600 lines)
- Estimated: ~3000 lines

**Source Lean file**: `Ramsey36/Basic.lean` (12,919 lines)

## Phase 6: Final Assembly (Week 16)

**Status**: Not started

**Deliverable**: `r36_main.mg` combines all proofs, generates `.pfg`

**Success criteria**:
- All files compile: `megalodon -I preamble.mgs r36_main.mg` → EXIT 0
- No `Admitted` statements: `grep Admitted *.mg` → EMPTY
- Valid `.pfg`: `megalodon -I preamble.mgs -pfg r36_main.mg > r36_proof.pfg` → EXIT 0
- Correct theorem name: `grep "Thm TwoRamseyProp_3_6_18" r36_proof.pfg` → FOUND
- Size within limits: `ls -lh r36_proof.pfg` → < 400KB

## Key Lessons from Failed November 2025 Attempt

**What went wrong**:
- Brute-force enumeration: 277K lines of explicit triple/subset checks
- Files too large for Megalodon to compile
- Never generated valid `.pfg` document

**Our approach**:
- ✅ Structural mathematical proofs (regularity, pigeonhole)
- ✅ Following proven R(3,3)=6 style (xm cascades, set-theoretic reasoning)
- ✅ Incremental verification (compile after each phase)
- ✅ Rigorous proof strategy (prove R(3,4), R(3,5) first - no axioms)

## Current Status Summary

| Phase | Status | Lines | Verified |
|-------|--------|-------|----------|
| 1. Foundations | ✅ DONE | 27 | ✅ Compiles |
| 2. R(3,4)=9 | ⏳ Next | ~800 | - |
| 3. R(3,5)=14 | - | ~1000 | - |
| 4. Lower bound | - | ~500 | - |
| 5. Upper bound | - | ~3000 | - |
| 6. Assembly | - | ~50 | - |
| **TOTAL** | **Phase 1/6** | **~5400** | **27/5400** |

**Next immediate action**: Begin Phase 2 (R(3,4)=9 lower bound witness graph)

**Timeline**: Started 2025-12-18, estimated completion 2026-04-18 (16 weeks)

**References**:
- Chad Brown's R(3,3)=6: `Megalodon/examples/egal/Ramsey_3_3_6.mg`
- Bounty specification: `Megalodon/examples/pfgbounties/RamseyConjsWithBounties.mg:61`
- Full plan: `/home/zar/.claude/plans/mighty-greeting-gizmo.md`
