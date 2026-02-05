# AI‑Assisted Formal Mathematics Projects

Workspace of Lean, Metamath, and ATP tooling developed with AI assistance.

## Primary Lean repos (most active)

- **`lean-projects/mettapedia/`** — broad Lean 4 formalization library; see its README for build/status.
- **`lean-projects/fourcolor/`** — Four‑color theorem work in Lean.
- **`lean-projects/ramsey36/`** — Ramsey R(3,6) formalization in Lean.

## Metamath verification / tooling

- **`hyperon/metamath/mm-lean4/`** — Lean 4 soundness proof of a Metamath verifier (see `CURRENT_STATUS.md`).
- **`hyperon/metamath/pverify/`** — Prolog + PeTTa Metamath verifier (see `STATUS.md` and `CANONICAL_TEST_RESULTS.md`).

## Resolution / TPTP tools

- **`tools/tptp-metta/`** — TPTP ↔ S‑expression ↔ MeTTa converters and a propositional resolution prototype.

## Status & review

Project status varies by subdirectory. Check the local README/CURRENT_STATUS, and run
`rg "sorry"` in the relevant code folders to see proof gaps.
