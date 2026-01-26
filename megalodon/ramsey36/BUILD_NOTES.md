# Build & Submission Strategy

## Development Approach (Modular)

Work with separate files for clean incremental development:
```
preamble.mgs           (6107 lines - Egal theory)
r36_definitions.mg     (27 lines - graph foundations)
r36_small_ramsey.mg    (~1800 lines - R(3,4)=9, R(3,5)=14)
r36_lower_bound.mg     (~500 lines - 17-vertex witness)
r36_upper_bound.mg     (~3000 lines - Cariolaro method)
r36_main.mg            (~50 lines - final theorem assembly)
```

**Compile each incrementally**:
```bash
./bin/megalodon -I preamble.mgs r36_definitions.mg          # ✅ Done
./bin/megalodon -I preamble.mgs r36_small_ramsey.mg         # Phase 2-3
./bin/megalodon -I preamble.mgs r36_lower_bound.mg          # Phase 4
./bin/megalodon -I preamble.mgs r36_upper_bound.mg          # Phase 5
./bin/megalodon -I preamble.mgs r36_main.mg                 # Phase 6
```

## Final Submission (Single File)

ProofGold requires ONE `.mg` file. Create by concatenation:

```bash
# Final assembly (Phase 6)
cat r36_definitions.mg \
    r36_small_ramsey.mg \
    r36_lower_bound.mg \
    r36_upper_bound.mg \
    r36_main.mg \
    > ramsey_3_6_18_FINAL.mg

# Generate ProofGold document
./bin/megalodon -I preamble.mgs -pfg ramsey_3_6_18_FINAL.mg > ramsey_3_6_18.pfg

# Verify
grep "Thm TwoRamseyProp_3_6_18" ramsey_3_6_18.pfg
grep -c "Admitted" ramsey_3_6_18_FINAL.mg  # Must be 0
ls -lh ramsey_3_6_18.pfg                    # Must be < 400KB
```

## Opaque vs Transparent Strategy

**Default: All Transparent** (following Chad's R(3,3)=6 approach)
- No Opaque declarations in our definitions
- Allows structural proofs to unfold definitions as needed
- Keep proofs direct and clear

**Only use Opaque if**:
- Proof size becomes problematic (unlikely given our structural approach)
- Need to abstract complex helper definitions (not needed for Ramsey)

**Example from Chad**: R(3,3)=6 (543 lines) uses 0 Opaque declarations.

## Critical Submission Checks

Before final submission:

1. **No Admitted**: `grep -c "Admitted" ramsey_3_6_18_FINAL.mg` → 0
2. **Compiles**: `./bin/megalodon -I preamble.mgs ramsey_3_6_18_FINAL.mg` → EXIT 0
3. **Generates .pfg**: `./bin/megalodon -I preamble.mgs -pfg ramsey_3_6_18_FINAL.mg` → EXIT 0
4. **Correct theorem**: `grep "Thm TwoRamseyProp_3_6_18" ramsey_3_6_18.pfg` → FOUND
5. **Size limit**: `ls -lh ramsey_3_6_18.pfg` → < 400KB (blockchain limit ~500KB, safety margin)
6. **Bounty address**: Match `TMbJ1MogStdKCGN3J3j1hThprkcWjA8ggEB`

## Preamble Strategy

**Development**: Use full `preamble.mgs` (6107 lines) for all dependencies

**Note**: Preamble is NOT included in final `.mg` file - it's imported with `-I` flag. The `.pfg` export will inline necessary definitions.

## Proof Size Estimates

| Component | Modular Files | Final .mg |
|-----------|---------------|-----------|
| Definitions | 27 | 27 |
| R(3,4)=9 | 800 | 800 |
| R(3,5)=14 | 1000 | 1000 |
| Lower bound | 500 | 500 |
| Upper bound | 3000 | 3000 |
| Assembly | 50 | 50 |
| **TOTAL** | **5377 lines** | **5377 lines** |
| **.pfg size** | N/A | **~380KB (est)** |

Ratio: Chad's R(3,3)=6 is 543 lines → 97KB .pfg (5.6 lines/KB)
Our estimate: 5377 lines → ~960KB/5.6 = **~380KB .pfg** ✅ Under limit!

## Development Workflow

Phase 1-5: Work modularly, compile each file separately
Phase 6: Concatenate, verify final .mg, generate .pfg, claim bounty

**Status**: Phase 1 complete (definitions), starting Phase 2 (R(3,4)=9)
