# pverify - Hybrid Prolog+PeTTa Metamath Verifier

Integrated Metamath verifier combining Prolog parsing with PeTTa verification.

## Architecture

1. **Prolog** parses `.mm` files into structured lists (using DCG parser)
2. **PeTTa** processes statements and calls verification functions
3. No file generation - pure in-memory integration

## Files

- `pverify_hybrid.metta` - Main verifier
- `mm_primitives.pl` - Prolog DCG parser for Metamath
- `env_utils.pl` - Environment variable access for PeTTa
- `pverify-utils.metta` - Verification utilities (copy of mmverify-utils_petta with lib_he import commented out)
- `verify_mm.sh` - Wrapper script for command-line usage
- `pverify_codegen.metta` - Code generator for debugging

## Usage

### Option 1: Using command-line argument (recommended)

```bash
cd /home/zar/claude/hyperon/PeTTa
./run.sh /home/zar/claude/hyperon/metamath/pverify/pverify_hybrid.metta /path/to/file.mm --silent
```

### Option 2: Using the wrapper script

```bash
/home/zar/claude/hyperon/metamath/pverify/verify_mm.sh path/to/file.mm
```

### Option 3: Using environment variable

```bash
export MM_INPUT_FILE="/path/to/file.mm"
cd /home/zar/claude/hyperon/PeTTa
./run.sh /home/zar/claude/hyperon/metamath/pverify/pverify_hybrid.metta --silent
```

### Option 4: Using default file

```bash
cd /home/zar/claude/hyperon/PeTTa
./run.sh /home/zar/claude/hyperon/metamath/pverify/pverify_hybrid.metta --silent
# Defaults to demo0.mm
```

## Performance

Typical runtime for demo0.mm: ~0.3 seconds
