# PeTTa Metamath Verifier (pverify)

**Location:** `/home/zar/claude/hyperon/metamath/pverify/`

**Goal:** Pure Prolog+PeTTa Metamath parser and verifier (replaces Python mmverify.py)

## Architecture

**CDTools-inspired design** with clean two-layer separation:

### Prolog Layer (`mm_primitives.pl`)
**CDTools-style: Complete tokenization in Prolog**:
- File I/O: `read_mm_file/2`
- **High-level tokenization**: `tokenize_mm_file/2` - Returns complete token list
- DCG patterns: `mm_token`, `mm_whitespace`, `mm_comment` (internal)
- Character classification: `is_whitespace/1`, `is_mm_printable/1`, `is_dollar/1`

**Design rationale**: Prolog does ALL low-level iteration (like CDTools C scanner), avoiding PeTTa non-determinism.

### PeTTa Layer (`pverify.metta`)
**High-level parsing and verification**:
- Statement recognition (pattern matching on token lists)
- Token stream processing (split at $. delimiters)
- Statement parsing (all 9 statement types: $c, $v, $f, $e, $a, $p, $d, ${, $})
- Integration with verification (`mmverify-utils_petta.metta`)
- Frame management (push-frame, pop-frame)

## Design Rationale

✅ **CDTools architecture** - Prolog does complete tokenization (like C scanner in CDTools)
✅ **Avoid PeTTa non-determinism** - Pattern matching on Prolog results creates exponential branching
✅ **Simple API** - Prolog returns plain list of atoms, PeTTa pattern matches on structure
✅ **Testable layers** - Can test tokenization and parsing independently

**Why this works**: Prolog's DCG handles iteration deterministically, PeTTa only pattern matches on final result.

## File Structure

```
/home/zar/claude/hyperon/metamath/pverify/
├── mm_primitives.pl           # Prolog tokenization (181 lines, DCG-based)
├── pverify.metta              # PeTTa parsing + verification (300 lines)
├── test_pverify.metta         # Full test suite
├── test_simple.metta          # Minimal tokenization test
├── DEBUG_FOR_GPT5.txt         # Debug info for DCG issue
├── ARCHITECTURE.md            # Detailed architecture docs
├── CDTOOLS_ANALYSIS.md        # Analysis of CDTools parser
├── CDTOOLS_VS_VERIFIER.md     # Comparison with mmverify.py
├── TEST_PLAN.md               # Testing roadmap
└── README.md                  # This file
```

## Dependencies

- `/home/zar/claude/hyperon/PeTTa/lib/lib_he.metta` - HE compatibility
- `/home/zar/claude/hyperon/PeTTa/lib/lib_prolog.metta` - Prolog interop
- `/home/zar/claude/hyperon/metamath/mmverify/mmverify-utils_petta.metta` - Verification logic

## Prolog API

**Primary function**:
- `tokenize_mm_file(+Filename, -Tokens)` - Read and tokenize file in one call

**Character classification** (for PeTTa if needed):
- `is_whitespace(+Code)` - Check if character code is whitespace
- `is_mm_printable(+Code)` - Check if printable (ASCII 33-126)
- `is_dollar(+Code)` - Check if dollar sign

**Low-level** (mostly internal, exported for debugging):
- `read_mm_file(+Filename, -Codes)` - Read file as character codes
- `next_token(+Codes, -Token, -Rest)` - Extract single token
- `skip_whitespace(+Codes, -Result)` - Skip whitespace
- `skip_comment(+Codes, -Result)` - Skip $( ... $) comments

## Statement Types (PeTTa)

All parsing logic in PeTTa produces these structures:

- `(CStmt symbols)` - $c constant declaration
- `(VStmt vars)` - $v variable declaration
- `(FStmt label type var)` - $f floating hypothesis
- `(EStmt label type math)` - $e essential hypothesis
- `(AStmt label type math)` - $a axiom
- `(PStmt label type math proof)` - $p provable assertion
- `(DStmt vars)` - $d disjoint variable constraint
- `OpenFrame` - ${ frame open
- `CloseFrame` - $} frame close

## Usage

From PeTTa directory:

```bash
cd /home/zar/claude/hyperon/PeTTa
./run.sh /home/zar/claude/hyperon/metamath/pverify/test_pverify.metta --silent
```

Or directly verify a file:

```metta
!(import! &self /home/zar/claude/hyperon/metamath/pverify/pverify)
!(verify-mm-file "/path/to/file.mm" True)
```

## Testing Against Test Suite

The `/home/zar/claude/hyperon/metamath/metamath-test/` directories contain LLM-generated test suites:

- **proptest/** - Property-based testing framework
- **canonical-tests/** - Canonical good/bad test cases

These can validate parsing of malformed files, edge cases, etc.

## Current Status

**✅ Architecture**: CDTools-style separation complete
**✅ Prolog tokenization**: `tokenize_mm_file/2` works - parses demo0.mm → 166 tokens
**✅ Prolog structured parsing**: `parse_mm_file/2` works - returns structured Prolog terms
**⚠️ PeTTa integration**: Prolog lists don't directly map to PeTTa `Cons` lists
**🔄 Next**: Fix Prolog-to-PeTTa list conversion or use Prolog structured terms directly

**See**: `DEBUG_FOR_GPT5.txt` for complete debugging information to share with GPT-5.

## Future Work

- [ ] **FIX DCG bug** - Get `mm_tokens//1` working (current blocker)
- [ ] Test against canonical-tests suite
- [ ] Add property-based testing integration
- [ ] Optimize Prolog primitives for large files (target: <30s for set.mm)
- [ ] Add compressed proof support
- [ ] Parallel statement processing
- [ ] Error recovery and diagnostics
