# pverify — Status & Architecture Notes

**Last reviewed**: 2026-03-21 by Oruži  
**Codebase**: 7,676 lines across 26 files (11 MeTTa, 11 Prolog, 4 test Prolog)

## Architecture Overview

pverify is a **hybrid Prolog+MeTTa Metamath proof verifier** with multiple implementation variants. The core idea: Prolog handles parsing and efficient data structures (AVL trees, ordered sets), while MeTTa handles the verification logic.

### Layer Diagram

```
┌─────────────────────────────────────────────────────┐
│  MeTTa Verification Logic                           │
│  (process-statement, treat-step, apply-subst,       │
│   check-dvs, build-subst, compressed proof, ...)    │
├─────────────────────────────────────────────────────┤
│  Prolog FFI Bridge (pverify_ds.pl)                  │
│  Opaque data structures: assoc, ordset, stmt lists  │
│  Batched ops: ds_apply_subst, ds_find_vars          │
├─────────────────────────────────────────────────────┤
│  Prolog Parser (mm_primitives.pl, 1224 lines)       │
│  DCG-based Metamath parser, tokenizer, streaming    │
│  Handles: $c $v $f $e $a $p $d ${ $} comments      │
│  Supports: normal proofs, compressed proofs         │
└─────────────────────────────────────────────────────┘
```

### State Model

```
State = (state Constants FrameStack Labels)
  Constants:  Prolog ordset of declared constant symbols
  FrameStack: MeTTa list of Frame tuples (stack, head = top)
  Labels:     Prolog assoc (label → hyp/assertion entry)

Frame = (frame Vars DVs FHyps FLabels EHyps)
  Vars:     Prolog ordset of active variables
  DVs:      Prolog ordset of X-Y disjoint variable pairs
  FHyps:    MeTTa list of (Typecode Var) — floating hypotheses
  FLabels:  Prolog assoc (Var → Label)
  EHyps:    MeTTa list of (ep Label Stmt) — essential hypotheses
```

## File Inventory

### Core Prolog

| File | Lines | Role |
|------|-------|------|
| `mm_primitives.pl` | 1224 | DCG parser: tokenizer, statement parser, streaming, code generation |
| `pverify_ds.pl` | 227 | Data structure bridge: assoc, ordset, stmt list ops for MeTTa FFI |
| `pverify.pl` | 520 | **Pure Prolog verifier** — standalone, no MeTTa dependency |
| `env_utils.pl` | 39 | CLI/env helpers (get_env_var, is_flag_arg, halt_with_code) |
| `mm_bridge.pl` | 52 | Prolog↔MeTTa bridge utilities |
| `mm_verify.pl` | 55 | Verification helpers |
| `mm_executor.pl` | 17 | Executor stub |
| `mm_kb_loader.pl` | 20 | KB loader stub |
| `mm_stream.pl` | 75 | Streaming parser interface |
| `file_utils.pl` | 28 | File I/O utilities |

### MeTTa Verifier Variants

| File | Lines | Architecture | Notes |
|------|-------|-------------|-------|
| `pverify_op.metta` | 693 | **Optimized, purely functional** | State threading, Prolog FFI for data structures. Main variant. |
| `pverify_op_stream.metta` | 703 | Streaming variant | Same as op but parses statements one-at-a-time |
| `pverify_op_space.metta` | 658 | Space-based variant | Uses MapSpace/SetSpace for storage |
| `pmverify.metta` | 215 | MORK-optimized | Uses mmverify-utils_pmork import |
| `pverify_hybrid.metta` | 248 | Baseline hybrid | Original Prolog parse + MeTTa verify |
| `pverify.metta` | 248 | Legacy variant | Similar to hybrid |
| `pverify_pure.metta` | 248 | Pure MeTTa attempt | |
| `pverify_codegen.metta` | 97 | Code generation | Generates .metta from .mm |
| `demo0_generated.metta` | 37 | Generated test | demo0.mm → MeTTa |

### Shared Utilities

| File | Lines | Role |
|------|-------|------|
| `pverify-utils.metta` | 961 | Shared verification utilities (add_f, add_e, add_p, stack ops) |
| `pverify-utils-pure.metta` | 983 | Pure variant of utils |

### Tests

| File | Lines | Tests |
|------|-------|-------|
| `test_01_basic_dcg.pl` | 145 | DCG parser unit tests |
| `test_parse_structured.pl` | 70 | Structured parsing tests |
| `test_prolog_bridge.pl` | 49 | Prolog↔MeTTa bridge tests |
| `test_generate.pl` | 32 | Code generation tests |
| `test_fix.pl` | 24 | Regression fixes |
| `test_return_formats.pl` | 8 | Return format tests |

## Verification Algorithm

The core algorithm implements the standard Metamath RPN stack machine (matching `mmverify.py`):

1. **Parse** `.mm` file into structured statements (c, v, f, e, a, p, d, open_frame, close_frame)
2. **Process** statements sequentially, maintaining state:
   - `$c` → add to constants set
   - `$v` → add to current frame's variable set
   - `$f` → register floating hypothesis (type assignment for variable)
   - `$e` → register essential hypothesis
   - `$d` → register disjoint variable constraints
   - `$a` → register axiom (build assertion from mandatory hypotheses)
   - `$p` → **verify proof** then register as assertion
   - `${ / $}` → push/pop scope frame
3. **Proof verification** (for `$p` statements):
   - Walk proof labels as RPN instructions
   - Hypotheses push their statement onto the stack
   - Assertions pop N entries (floating + essential hyps), build substitution, check typecodes, check essential hyps match, check DV constraints, push substituted conclusion
   - Final stack must contain exactly the theorem's statement
4. **Compressed proofs**: decode base-26 encoding, handle mandatory hypothesis labels, saved statements (Z marker)

## Test Results (2026-03-21)

### Pure Prolog Verifier (`pverify.pl`)

| Test File | Statements | Result |
|-----------|-----------|--------|
| `demo0.mm` | 19 | ✅ All proofs verified |
| `disjoint2.mm` | 22 | ✅ All proofs verified |
| `hol_example_normal.mm` | 81 | ✅ All proofs verified |
| `set_example_normal.mm` | 433 | ✅ All proofs verified |
| `test_simple.mm` | 6 | ✅ All proofs verified |
| `test_nonv_vars.mm` | 9 | ✅ All proofs verified |
| `invalid_duplicate_floats.mm` | — | ✅ Correctly rejected (multiple active $f) |
| `test_modus_ponens.mm` | 14 | ❌ typecode_mismatch — test file has non-standard ax-mp (axiom, not inference rule); proof structure doesn't match |

### MeTTa Verifiers

**Cannot run on this machine** — require:
- PeTTa runtime (`/home/zar/claude/hyperon/PeTTa/`)
- MORK FFI (`libmork_ffi.so`)
- `lib_zar.metta` / `lib_zar.pl` (custom library)
- Specific directory layout (paths are relative to zariuq's dev environment)

Per git history, the MeTTa verifiers achieved **paper parity** (all 4 milestones M1-M4 closed) as of commit `84771606`.

## Key Design Decisions

1. **Opaque Prolog terms**: Math strings stay as Prolog lists because they contain literal `(` and `)` tokens which MeTTa interprets as grouping. All math operations go through `ds_stmt_*` FFI functions.

2. **Tagged e-hyps**: Essential hypotheses stored as `(ep $label $stmt)` triples — the `ep` tag prevents MeTTa from evaluating labels like `min` as built-in functions.

3. **Batched FFI**: Hot loops moved to single Prolog calls (`ds_apply_subst`, `ds_find_vars`) to reduce N per-token FFI crossings to 1.

4. **FFI profiling**: All `pverify_ds.pl` operations call `ffi_inc/1` for performance tracking.

5. **Multiple variants**: The codebase explores different state management strategies:
   - Pure functional state threading (`pverify_op`)
   - Mutable spaces (`pverify_op_space`)
   - Streaming parsing (`pverify_op_stream`)
   - MORK integration (`pmverify`)

## Evolution (from git history)

```
pverify basics → parser fixes → &kb → &mork migration →
non-determinism bug fixes → compressed proof support →
unicode support → paper parity (M1-M4) → pverify_op variants
```

Key commits:
- `0077c511` — Fixed non-determinism bug in merge vars for compressed proofs
- `2c3b6b7d` — Parser/tokenizer fix + integer safety
- `84771606` — All 4 paper-parity milestones closed
- `a92523ef` — pathmap tries + pverify_op (latest)

## Relationship to Other Projects

- **mmverify.py** (`/home/zarclaw/repos/mmverify.py/`) — Reference Python verifier; pverify aims for algorithm parity
- **mm-lean4** (`/home/zarclaw/repos/mm-lean4/`) — Lean 4 Metamath verifier; shares test files
- **PeTTa** (`/home/zarclaw/repos/PeTTa/`) — MeTTa runtime (Prolog-based)
- **MORK** (`/home/zarclaw/repos/MORK/`) — Rust-based MeTTa kernel for performance
- **Mettapedia** — Lean formalization project; potential bridge target for verified MM proofs
