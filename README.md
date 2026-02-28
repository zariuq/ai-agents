# AI-assisted formal mathematics projects

This workspace includes Lean, Metamath and ATP tooling.

## Primary Lean repositories

- **`lean-projects/mettapedia/`** — Mettapedia provides a broad Lean formalization library.
- **`lean-projects/fourcolor/`** — Fourcolor formalizes the Four‑color theorem in Lean.
- **`lean-projects/ramsey36/`** — Ramsey36 formalizes Ramsey R(3,6) in Lean.

### Interesting repositories

Mettapedia hosts the Knuth–Skilling Foundations of Inference proofs.
mm-lean4 proves a Metamath verifier inside Lean.
pverify exercises a cross-language verification pipeline for interoperability between logic programming and MeTTa.

## Metamath verification tools

- **`hyperon/metamath/mm-lean4/`** — mm-lean4 proves the soundness of a Metamath verifier in Lean (see CURRENT_STATUS.md).
- **`hyperon/metamath/pverify/`** — pverify provides a Prolog + PeTTa Metamath verifier (see STATUS.md and CANONICAL_TEST_RESULTS.md).

## Resolution TPTP tools

- **`tools/tptp-metta/`** — tptp-metta provides a propositional resolution prototype for TPTP ↔ S‑expression ↔ MeTTa conversion.

## Status review

Project status varies by subdirectory.
Maintainers check the local README/CURRENT_STATUS.
Maintainers run `rg "sorry"` in the relevant code folders for proof-gap review.
