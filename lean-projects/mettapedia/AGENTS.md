# AGENTS.md — Mettapedia

## What This Is
Lean 4 formalization library covering ethics, AI theory, category theory, algorithms,
and more. The main Lean project in the ai-agents ecosystem. Depends on Mathlib.

## Emulated Research Council

- For hard research, proof, architecture, or strategy work, use `/home/zarclaw/public/council.md` as an inspiration prompt.
- Treat the council as a perspective-broadening aid, not a literal approval gate. Do not invent fake consensus or exaggerated certainty.
- If blocked or uncertain, mentally simulate the strongest likely objections and approaches from that council before choosing a path.
- When useful, briefly report the dominant lines of reasoning and a grounded confidence/completeness estimate tied to actual code, proofs, tests, or experiments.

## Quick Commands

### Build
```bash
cd /home/zarclaw/repos/ai-agents/lean-projects/mettapedia
lake build                        # Build everything (slow — Mathlib dep)
lake build Mettapedia.GSLT        # Build a specific module
```

### Use Lean LSP tools (PREFERRED)
Use `lean_goal`, `lean_diagnostic_messages`, `lean_build`, `lean_file_outline`, etc.
These go through the proper Lake-managed LSP server — better than `lake env lean`.

### Lean toolchain
- Lean 4 v4.28.0
- Mathlib v4.28.0 (heavy dependency — first build downloads ~2GB)

## Key Modules
```
Mettapedia/
  Ethics/           — Formal ethics (FOET ontology)
  GSLT/             — Greg's GSLT framework formalization
  UniversalAI/      — AIXI, Solomonoff, universal intelligence
  CognitiveArchitecture/ — Cognitive architecture formalizations
  Algorithms/       — Algorithm formalizations
  Logic/            — Logic foundations
  CategoryTheory/   — Category theory
  Bridge/           — MeTTa↔Lean bridge
  HundredProofs.lean — Collection of 100 proof exercises
  ...and many more
```

## Local Dependencies (in lakefile.toml)
- `ordered_semigroups` — Eric Luap's ordered semigroups
- `Foundation` — Logic foundations
- `exchangeability` — Exchangeability with ForMathlib
- `provenance` — Provenance semiring
- `borel_det` — Borel determinacy
- `catLogic` — Categorical logic
- `Metatheory` — Metatheory
- `algorithms` — Pure algorithm checker kernels (Init-only)
- `mettail_core` — Shared MeTTaIL executable core
- `gf_core` — GF↔Lean AST bridge
- `certifyingDatalog` — Certifying Datalog (ITP 2025)

## Build Notes
- `weakLeanArgs = ["-j", "1"]` — forced single-threaded due to 6GB ulimit
- First build is very slow (Mathlib compilation)
- Subsequent builds use oleans cache

## Related Projects
- **mm-lean4** (`/home/zarclaw/repos/mm-lean4/`) — Metamath verifier in Lean
- **pverify** (`/home/zarclaw/repos/ai-agents/hyperon/metamath/pverify/`) — Prolog+MeTTa verifier
- **algorithms** (`/home/zarclaw/repos/ai-agents/lean-projects/algorithms/`) — Pure algorithm kernels
