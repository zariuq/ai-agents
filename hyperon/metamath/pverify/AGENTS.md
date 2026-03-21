# AGENTS.md — pverify

## What This Is
Hybrid Prolog+MeTTa Metamath proof verifier. See `STATUS.md` for full architecture.

## Quick Commands

### Run the pure Prolog verifier (standalone, no MeTTa needed)
```
swipl -g main -t halt pverify.pl -- <file.mm>
swipl -g main -t halt pverify.pl -- --compressed-dag <file.mm>
```

### Run Prolog tests
```
swipl -g run_tests -t halt test_01_basic_dcg.pl
```

### MeTTa verifiers — CANNOT RUN HERE
Require PeTTa runtime, MORK FFI, lib_zar — only available on zariuq's dev machine.

## Test Databases
- Local test `.mm` files: `/home/zarclaw/repos/mm-lean4/test_*.mm`
- mmverify.py examples: `/home/zarclaw/repos/mmverify.py/examples/`
- Invalid test files: `/home/zarclaw/repos/mm-lean4/test_databases/`
- See `CANONICAL_TEST_RESULTS.md` for current test status.

## Key Files
- `pverify.pl` — Pure Prolog verifier (520L, standalone)
- `mm_primitives.pl` — DCG parser (1224L)
- `pverify_ds.pl` — Data structure FFI bridge (227L)
- `pverify_op.metta` — Main MeTTa verifier variant (693L)
- `pverify-utils.metta` — Shared verification utilities (961L)

## Gotchas
- MeTTa files use opaque Prolog terms for math strings (literal parens conflict with MeTTa grouping)
- Essential hypotheses tagged as `(ep $label $stmt)` to prevent MeTTa eval of names like `min`
- `test_modus_ponens.mm` is malformed (ax-mp as axiom without $e hyps); use `test_modus_ponens_fixed.mm`

## Parent Project
Part of `/home/zarclaw/repos/ai-agents/hyperon/metamath/` — the broader Metamath formalization effort.
