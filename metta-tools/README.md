# Mizar to MeTTa/MORK Conversion Tools

Tools for converting Mizar Mathematical Library to S-expressions for use with MeTTa and MM2/MORK.

## Overview

This directory contains Python tools that convert mizar-rs JSON output into various S-expression formats suitable for:
- **MeTTa**: Hyperon's executable symbolic AI language
- **MM2/MORK**: Queryable mathematical database format

## Prerequisites

1. **mizar-rs with our patches** (already applied in this repo)
2. **Python 3.x**
3. **MeTTa** (optional, for testing): `conda activate hyperon`
4. **Mizar MML**: Set `MIZFILES=/home/zar/claude/mizar/share`

## Quick Start

```bash
# 1. Set environment variables
export MIZFILES=/home/zar/claude/mizar/share
export MIZAR_RS_OUTPUT_DIR=/tmp/mizar-output
mkdir -p $MIZAR_RS_OUTPUT_DIR

# 2. Extract JSON from Mizar
cd /home/zar/claude/mizar-rs
cargo build --release
./target/release/mizar-rs --json-parse-out tarski

# 3. Convert to S-expressions (choose format below)
cd metta-tools
python3 mizar_rs_to_sexp.py $MIZAR_RS_OUTPUT_DIR/tarski.mzp.json output.sexp
```

## Tools Description

### 1. `mizar_rs_to_sexp.py` - Basic S-expression Converter
The foundation converter that produces clean S-expressions from mizar-rs JSON.

**Features:**
- Handles all mizar-rs JSON AST structures
- Fixed parenthesis balancing bug
- Preserves full theorem structure with justifications
- Outputs clean S-expressions (no Python artifacts)

**Usage:**
```bash
python3 mizar_rs_to_sexp.py input.mzp.json output.sexp
```

**Output format:**
```lisp
(theorem (pos 29 1)
  (imp
    (forall (("x" (mode 1 "object")))
      (iff (pred + 2 "in" ((var "x") (var "X")))
           (pred + 2 "in" ((var "x") (var "Y")))))
    (pred + 0 "=" ((var "X") (var "Y"))))
  (by (ref 1 "tarski_0" ((thm 1)))))
```

### 2. `mizar_to_metta.py` - MeTTa-Specific Format
Converts to MeTTa-executable format with type annotations.

**Features:**
- Type declarations for MeTTa
- Executable definitions
- Pattern matching examples
- Query examples

**Usage:**
```bash
python3 mizar_to_metta.py input.mzp.json output.metta
```

**Output format:**
```lisp
(: singleton (-> Object Set))
(= (in $x (singleton $y))
   (eq $x $y))
```

### 3. `mizar_universal_sexp.py` - Universal Format
Creates S-expressions that work in BOTH MeTTa and MM2/MORK.

**Features:**
- Pure S-expression syntax
- Optional type annotations (used by MeTTa, ignored by MM2)
- Database assertions for MORK
- Query examples for both systems

**Usage:**
```bash
python3 mizar_universal_sexp.py input.mzp.json output.sexp
```

**Output format:**
```lisp
;; Works in both systems
(define singleton
  (lambda (y)
    (set-of x (eq x y))))

;; MeTTa type annotation (optional)
(type-decl Object Type)

;; MM2/MORK assertion
(assert (in a (singleton a)))

;; MeTTa query
(query (match &self (theorem $name) $name))
```

### 4. `mizar_proof_verifier.py` - Proof Verification Format
Extracts proofs and creates verification structure.

**Features:**
- Verification rules (modus ponens, universal instantiation, etc.)
- Justification extraction
- Verification status tracking
- Works in both MeTTa (execute) and MM2 (query)

**Usage:**
```bash
python3 mizar_proof_verifier.py input.mzp.json verifiable.sexp
```

**Output format:**
```lisp
;; Verification rule
(verify-rule modus-ponens
  (premises (fact A) (fact (implies A B)))
  (conclusion (fact B)))

;; Theorem with verification
(theorem tarski-1
  (statement (forall (x) (is x set)))
  (justified-by (ref tarski_0 thm-0))
  (verify-step
    (check-references (ref tarski_0 thm-0))
    (status pending)))
```

## Which Tool to Use?

- **For raw conversion**: Use `mizar_rs_to_sexp.py`
- **For MeTTa only**: Use `mizar_to_metta.py`
- **For both MeTTa and MORK**: Use `mizar_universal_sexp.py` ⭐ **RECOMMENDED**
- **For proof checking**: Use `mizar_proof_verifier.py`

## Processing the Entire MML

```bash
# Set up
export MIZFILES=/home/zar/claude/mizar/share
export MIZAR_RS_OUTPUT_DIR=/tmp/mizar-output
mkdir -p $MIZAR_RS_OUTPUT_DIR

# Process all articles
cd /home/zar/claude/mizar-rs
for article in $(cat $MIZFILES/mml.lar); do
    echo "Processing $article..."
    ./target/release/mizar-rs --json-parse-out $article 2>/dev/null
done

# Convert all to universal format
cd metta-tools
for json in $MIZAR_RS_OUTPUT_DIR/*.mzp.json; do
    base=$(basename $json .mzp.json)
    python3 mizar_universal_sexp.py $json $MIZAR_RS_OUTPUT_DIR/$base.sexp
done

# Combine into single database
cat $MIZAR_RS_OUTPUT_DIR/*.sexp > mml_complete.sexp
```

## Testing in MeTTa

```bash
# Activate MeTTa environment
conda activate hyperon

# Test the converters
python3 mizar_to_metta.py  # Runs built-in test

# Or load in MeTTa directly
python3 -c "
from hyperon import MeTTa
metta = MeTTa()
with open('output.metta', 'r') as f:
    result = metta.run(f.read())
print(result)
"
```

## Known Issues

1. Some Mizar articles cause mizar-rs parser to panic - this is a limitation of mizar-rs, not our tools
2. SchemeBlock items are not fully implemented yet (shows as raw dict)
3. Some complex proof structures are simplified in the output

## Documentation

- `HOW_TO_MIZAR_RS.md` - Complete pipeline documentation
- `MIZAR_TO_SEXP_DEMO.md` - Examples and demonstrations
- `MIZAR_IMPORT_SUCCESS.md` - Achievement summary

## Patches Applied to mizar-rs

The parent directory contains our patches to mizar-rs:
1. Added `MIZAR_RS_OUTPUT_DIR` environment variable support
2. Commented out auxiliary file writes (.idx, .dcx, .frx)
3. Fixed JSON export to work with read-only MML

See `../mizar-rs-export-fix.patch` for details.

## License

These tools are provided as-is for use with the mizar-rs project.

## Authors

Created during Claude Code session, November 2025
For the Hyperon AGI project