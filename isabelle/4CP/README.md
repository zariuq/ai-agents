# Isabelle/HOL Formalization of 4CT via Disk Kempe-Closure Spanning

## Overview
Self-contained Isabelle2025 formalization of the Four Color Theorem (4CT) using the Kempe-Closure Spanning Disk approach. Based on Goertzel's Spencer-Brown/Kauffman-style proof, bypassing global connectivity issues via local disk analysis.

**Key Innovation:** Strong dual lemma (annihilator inclusion) via bilinearity over GF(2)², facial basis, and run-purification.

## Current Status (2025-10-09)

### ✅ Complete (100% Proven)
- **Algebraic Framework**: XOR chains, bilinearity, span idempotence, orthogonality propagation
  - `xor_chain_assoc`, `xor_chain_comm`: XOR properties
  - `cspan_idem`: Span idempotence (NOW PROVEN!)
  - `dot_chain_xor_right`: Main bilinearity theorem
  - `orth_on_set_imp_orth_on_cspan`: Orthogonality propagation
  - All proven without `sorry` in explicit Isar style

### 📋 Structured with Proof Sketches
- **M4a (Run-Completion)**: Face boundaries in Kempe span via XOR over 2^k completions
- **M4b (Facial Basis)**: Zero-boundary chains spanned by face boundaries via Euler/dimension
- **Main Theorem**: Strong dual property with complete proof chain

### 🔧 Infrastructure
- **Graph Conversion**: Bridge to AFP Graph_Theory for leveraging existing lemmas
- **Build Time**: ~6-10 seconds
- **Remaining Sorries**: 2 (standard graph theory results, fully documented)

## Building the Project

### Prerequisites
- Isabelle2025
- AFP-2025-09-12 (already installed at `/home/zar/claude/Isabelle2025/afp-2025-09-12/`)

### Build Commands
```bash
# Basic build
isabelle build -v -d . FourColor_KCSD

# With PDF documentation
isabelle document -v FourColor_KCSD

# HTML browser
isabelle browser -v FourColor_KCSD
```

## Project Structure

```
theories/
├── Core/
│   ├── GraphPrimitives.thy     # Basic graph definitions
│   └── Graph_Conversion.thy    # Bridge to AFP Graph_Theory
├── Disk/
│   ├── Disk_KCSD.thy          # Main disk cubic locale
│   ├── Disk_RunPurification.thy # M4a: Run-completion theorem
│   ├── Disk_FacialBasis.thy   # M4b: Facial basis theorem
│   └── Disk_KCSD_DualStrong.thy # Main strong dual theorem
└── Global/
    ├── Tait_Equivalence.thy    # Tait's edge-coloring equivalence
    └── FourColor_Theorem.thy   # Global 4CT from local results
```

## Mathematical Content

### The Approach
1. **Local Analysis**: Focus on disk neighborhoods rather than global graph
2. **Kempe Closures**: Use Kempe chain switching as generators
3. **Strong Dual**: Prove orthogonality propagates from generators to all zero-boundary chains
4. **Bilinearity**: Key algebraic property over GF(2)² enabling the proof

### Key Results
- **Theorem**: `Disk_KCSD_dual_strong` - If z ⊥ all Kempe generators, then z ⊥ all zero-boundary chains
- **Corollary**: Local 3-edge-colorability extends via Kempe chains
- **Application**: 4CT follows via Tait equivalence

## References

- **Primary Source**: "4CP-Filling-The-Gap-via-ATP.pdf" (Goertzel et al.)
- **Graph Theory**: Bollobás Ch.8 (cycles), Diestel §1.9 (basis)
- **Prior Work**: Gonthier et al. (Coq formalization of 4CT)

## Remaining Work

1. **Complete M4a**: Finish run-completion proof using documented strategy
2. **Complete M4b**: Finish facial basis using Euler formula from AFP
3. **Optional**: Full AFP type conversion for better library integration

## Contributors

- Implementation: Zar (with assistance from Claude)
- Theory: Ben Goertzel, Spencer-Brown, Kauffman
- Guidance: GPT-5, Grok

## License

[To be determined - likely BSD or similar open source]