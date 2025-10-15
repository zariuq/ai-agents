# Compilation Guide - Four Color Theorem Formalization

This guide explains how to compile and verify the Mizar formalization files.

## Prerequisites

### Required Software
- **Mizar System** 8.1.15 or later
- **MML (Mizar Mathematical Library)** - standard installation
- **Unix-like environment** (Linux, macOS, or WSL on Windows)

### Installation
If you don't have Mizar installed:
1. Download from [Mizar website](http://www.mizar.org/)
2. Follow installation instructions for your platform
3. Ensure `mizf` is in your PATH

Verify installation:
```bash
mizf --version
```

## Directory Structure

The project uses standard Mizar text/dict structure:
```
theories/
  MODULE_NAME/
    text/        # .miz source files
    dict/        # .voc vocabulary files
```

All compilation should be done from within the `text/` directories.

## Quick Start

### Compile All Files

From the project root:
```bash
# Chain algebra foundation
cd theories/01_chain_algebra/text
mizf chain_dot_constructive
cd ../../..

# Parity infrastructure
cd theories/02_parity/text
mizf face_boundary
mizf set_parity
cd ../../..

# Main theorems
cd theories/02_main_theorems/text
mizf span_constructive
mizf strong_dual
mizf kempe_purification
mizf disk_kempe_closure
mizf tait_equivalence
cd ../../..
```

### Compile Individual Files

Navigate to the appropriate text/ directory and run `mizf` with the filename (without .miz extension):

```bash
# Example: Compile span_constructive.miz
cd theories/02_main_theorems/text
mizf span_constructive
```

## Understanding Mizar Compilation

### The `mizf` Command

`mizf` is the Mizar compiler frontend that:
1. **Parses** the .miz file syntax
2. **Processes** environment declarations
3. **Analyzes** definitions and theorems
4. **Checks** proofs and type correctness

### Output Files

After running `mizf filename`, several output files are created:
- `filename.err` - Error listing (check this for compilation results)
- `filename.miz` - Original source (unchanged)
- Various intermediate files (.xml, .dno, etc.)

### Checking Compilation Success

**Error counts**: Check the `.err` file:
```bash
wc -l span_constructive.err
```

**Error categories**: Use grep to filter:
```bash
# Check for Error 72/73 (correctness conditions)
grep "72\|73" span_constructive.err | wc -l

# Check for Error 203 (import/modularity)
grep " 203" span_constructive.err | wc -l
```

**Successful compilation**: Time shown as `0:00` and parser/checker complete
```
Time of mizaring: 0:00
```

## Compilation Order

Files should generally be compiled in dependency order:

### 1. Foundation Layer
```bash
cd theories/01_chain_algebra/text
mizf chain_dot_constructive
```

### 2. Infrastructure Layer
```bash
cd theories/02_parity/text
mizf face_boundary
mizf set_parity
```

### 3. Main Theorems Layer
```bash
cd theories/02_main_theorems/text
mizf span_constructive      # Lemma 4.5
mizf strong_dual            # Theorem 4.9
mizf kempe_purification     # Lemmas 4.2-4.4
mizf disk_kempe_closure     # Theorem 4.10
mizf tait_equivalence       # Tait's equivalence & 4CT
```

## Troubleshooting

### Common Issues

**Issue**: `mizf: command not found`
- **Solution**: Ensure Mizar is installed and in your PATH

**Issue**: Errors about missing vocabulary
- **Solution**: Check that .voc files are in the `dict/` subdirectory
- **Solution**: Ensure you're running `mizf` from the `text/` directory

**Issue**: High error count
- **Solution**: Check the .err file for specific error types
- **Solution**: Most remaining errors are Import/modularity (Error 203) or proof completion
- **Note**: Error 72/73 should all be fixed (0 remaining)

**Issue**: Compilation seems to hang
- **Solution**: Mizar compilation can be slow for large files
- **Solution**: Wait for completion (usually under 1 minute per file)

### Error Types

**Error 72**: "Unexpected correctness condition"
- All fixed (0 remaining as of October 2025)

**Error 73**: "Correctness condition missing"
- All fixed (0 remaining as of October 2025)

**Error 203**: Import/modularity issues
- Most common remaining error
- Related to vocabulary and type imports

**Error 306**: Proof step issues
- Need additional justifications or lemmas

## Advanced Usage

### Verbose Output

For more detailed compilation information:
```bash
mizf -v filename
```

### Specific Phases

Run only specific compilation phases:
```bash
# Parse only
mizf -p filename

# Analyze only (requires successful parse)
mizf -a filename
```

### Clean Build

Remove intermediate files before compilation:
```bash
rm *.err *.dno *.dco *.dfr *.xml 2>/dev/null
mizf filename
```

## Verification

After compilation, verify the results:

### Check Error Count
```bash
wc -l *.err
```

### Check Specific Error Types
```bash
# Import/modularity errors (203)
grep " 203" *.err | wc -l

# Proof errors (306)
grep " 306" *.err | wc -l
```

### Verify Successful Phases
```bash
# Check that all phases completed
tail *.err
# Should show "Time of mizaring: 0:00"
```

## Continuous Integration

For automated testing, use this script:

```bash
#!/bin/bash
# compile_all.sh

set -e  # Exit on error

echo "Compiling 4CP formalization..."

# Foundation
echo "=== Chain Algebra ==="
cd theories/01_chain_algebra/text
mizf chain_dot_constructive || { echo "chain_dot_constructive failed"; exit 1; }

# Infrastructure
echo "=== Parity Infrastructure ==="
cd ../../02_parity/text
mizf face_boundary || { echo "face_boundary failed"; exit 1; }
mizf set_parity || { echo "set_parity failed"; exit 1; }

# Main theorems
echo "=== Main Theorems ==="
cd ../../02_main_theorems/text
mizf span_constructive || { echo "span_constructive failed"; exit 1; }
mizf strong_dual || { echo "strong_dual failed"; exit 1; }
mizf kempe_purification || { echo "kempe_purification failed"; exit 1; }
mizf disk_kempe_closure || { echo "disk_kempe_closure failed"; exit 1; }
mizf tait_equivalence || { echo "tait_equivalence failed"; exit 1; }

echo "All files compiled successfully!"
```

Make executable and run:
```bash
chmod +x compile_all.sh
./compile_all.sh
```

## Performance Notes

Typical compilation times (on modern hardware):
- Small files (< 200 lines): < 5 seconds
- Medium files (200-500 lines): 5-15 seconds
- Large files (500+ lines): 15-30 seconds

Current files all complete in under 1 minute.

## Further Reading

- [Mizar Documentation](http://www.mizar.org/project/)
- [MML Query](http://mizar.org/version/current/mml_query.html)
- [how_to_miz.md](how_to_miz.md) - Project-specific Mizar lessons

---

For questions or issues, see the main [README.md](README.md) or open an issue.
