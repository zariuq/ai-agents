# pverify - Hybrid Prolog+PeTTa Metamath Verifier

Integrated Metamath verifier combining Prolog parsing with PeTTa verification.

## Architecture

1. **Prolog** parses `.mm` files into structured lists (using DCG parser)
2. **PeTTa** processes statements and calls verification functions
3. No file generation - pure in-memory integration

## Verifier Variants

### pmverify (MORK-optimized) - **Recommended**

Uses MORK (256-radix trie) spaces for O(log N) pattern matching on frame-scoped data:
- All frame-scoped data (Constants, Variables, DVars, FHyps, EHyps, FLists, ELists) in `&mork`
- Non-frame-scoped data (Assertions, Theorems, markers) in `$kb`

**Performance:** 24.85 seconds on hol.mm (87KB), slightly faster than pverify_hybrid (25.32s)

**Files:**
- `pmverify.metta` - MORK-optimized main verifier
- `../mmverify/mmverify-utils_pmork.metta` - MORK-optimized utilities

### pverify_hybrid (baseline)

Original implementation using standard MeTTa spaces with O(N) linear scans.

**Files:**
- `pverify_hybrid.metta` - Original main verifier
- `../mmverify/mmverify-utils_petta.metta` - Standard utilities

## Common Files

- `mm_primitives.pl` - Prolog DCG parser for Metamath
- `env_utils.pl` - Environment variable access for PeTTa
- `verify_mm.sh` - Wrapper script for command-line usage
- `pverify_codegen.metta` - Code generator for debugging

## Usage

### pmverify (MORK-optimized)

```bash
cd /home/zar/claude/hyperon/PeTTa
./run.sh /home/zar/claude/hyperon/metamath/pverify/pmverify.metta /path/to/file.mm --silent
```

### pverify_hybrid (baseline)

```bash
cd /home/zar/claude/hyperon/PeTTa
./run.sh /home/zar/claude/hyperon/metamath/pverify/pverify_hybrid.metta /path/to/file.mm --silent
```

### Using the wrapper script

```bash
/home/zar/claude/hyperon/metamath/pverify/verify_mm.sh path/to/file.mm
```

### Using environment variable

```bash
export MM_INPUT_FILE="/path/to/file.mm"
cd /home/zar/claude/hyperon/PeTTa
./run.sh /home/zar/claude/hyperon/metamath/pverify/pmverify.metta --silent
```

## Testing

Comprehensive test suite in `../metamath-test/`:

```bash
cd /home/zar/claude/hyperon/metamath/metamath-test

# Test pmverify (MORK-optimized)
./run-testsuite-all ./test-pmverify --small-only

# Test pverify_hybrid (baseline)
./run-testsuite-all ./test-pverify --small-only
```

**Test Results:** 138/138 tests passing (100%) for both verifiers

## Performance

| File | Size | pmverify (MORK) | pverify_hybrid |
|------|------|----------------|----------------|
| demo0.mm | 1.3 KB | 0.64s | 0.65s |
| hol.mm | 87 KB | 24.85s | 25.32s |

**Memory:** ~349 MB RSS for hol.mm

## MORK Optimization Strategy

The MORK optimization focuses on frame-scoped data because:
- Frame-scoped data has FSDepth tags for O(log N) trie lookups
- Frequent pattern matching during proof verification benefits from trie structure
- Non-frame-scoped data (Theorems/Assertions) accessed less frequently

This provides a foundation for future optimizations using MORK exec rules.
