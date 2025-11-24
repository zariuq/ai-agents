# Megalodon <-> MeTTa Bridge

This directory contains tools for bijective translation between Megalodon (`.mg`) files and MeTTa S-expressions.
This enables using MeTTa as an intermediate language for analyzing, transforming, or translating Megalodon proofs, and connecting Megalodon to other systems like TPTP via MeTTa.

## Tools

### 1. `mg_to_metta.py`
Parses `.mg` files into structured MeTTa S-expressions.
- Preserves structure (Definitions, Theorems, Proofs).
- **Handles Comments:** Correctly strips `(* ... *)` comments (including multiline).
- **Handles Declarations:** Preserves `Infix`, `Prefix`, `Binder`, `Title`, `Author`, etc.
- Parses terms into S-expressions:
  - `forall x:A, P` -> `(forall ((x A)) P)`
  - `A -> B` -> `(-> A B)`
  - `fun x => y` -> `(fun ((x Any)) y)`
  - `f x` -> `(f x)`

**Usage:**
```bash
python3 mg_to_metta.py file.mg > file.metta
```

### 2. `metta_to_mg.py`
Converts the MeTTa S-expressions back to valid Megalodon syntax.
- Intelligently formats terms using standard Megalodon notation.
- Reconstructs `Infix`, `Prefix`, etc.
- Handles `forall`, `fun`, `->`, `Admitted`, `exact` proofs, etc.

**Usage:**
```bash
python3 metta_to_mg.py file.metta > file_new.mg
```

## Verification

The bridge has been verified to round-trip valid Megalodon code such that the output is accepted by the Megalodon kernel.

### Test Case: `valid_test.mg`

1. **Input:** `valid_test.mg` (contains comments, `Infix`, `Definition`, `Theorem`, `exact` proof).
2. **Convert to MeTTa:** `mg_to_metta.py` -> `valid_test.metta`
   - Comments are stripped.
   - Structure preserved.
3. **Convert back to Megalodon:** `metta_to_mg.py` -> `valid_test_roundtrip.mg`
4. **Kernel Check:** `./bin/megalodon valid_test_roundtrip.mg` -> **Success** (Exit code 0).

### Running the Test
```bash
# From project root
python3 metta-tools/megalodon-bridge/mg_to_metta.py metta-tools/megalodon-bridge/valid_test.mg > metta-tools/megalodon-bridge/valid_test.metta
python3 metta-tools/megalodon-bridge/metta_to_mg.py metta-tools/megalodon-bridge/valid_test.metta > metta-tools/megalodon-bridge/valid_test_roundtrip.mg
megalodon/bin/megalodon metta-tools/megalodon-bridge/valid_test_roundtrip.mg
```

### One-shot harness (auto-finds the Megalodon binary)
```bash
# Kernel + fixtures (auto-locates megalodon/bin/megalodon or use MEGALODON_BIN)
python3 metta-tools/megalodon-bridge/tests/test_bridge_full.py --include-fixtures

# Add fuzz corpus or examples as needed
python3 metta-tools/megalodon-bridge/tests/test_bridge_full.py \
  --include-fixtures \
  --include-fuzz metta-tools/megalodon-bridge/tests/fuzz \
  --include-examples /home/zar/claude/megalodon/examples
```

You can override the binary path with `--megalodon-bin /path/to/megalodon` or the `MEGALODON_BIN` environment variable.

## Data Format

The MeTTa representation mirrors the Megalodon AST:

```lisp
(Definition Name Type Body)
(Theorem Name Type Proof)
(Parameter Name Type)
(Axiom Name Type)
(Infix Operator Precedence Assoc Def)
```
