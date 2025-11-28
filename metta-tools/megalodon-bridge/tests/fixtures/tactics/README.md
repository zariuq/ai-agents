# Tactic-Focused Fixtures

Goal: small `.mg` files that exercise individual tactics/features in isolation so we can pinpoint parser/round-trip regressions.

## Current fixtures
- `01_apply_basic.mg` – single `apply` closing a trivial goal.
- `02_section_scope.mg` – Section/End scoping with a local variable and definition.

## Roadmap (to be filled out)
- Rewrite direction/`at` clauses, `{ }` blocks, `claim`, `assume`, `cases`, `prove`, `aby`, `Binder+`, Unicode aliases, and infix precedence stress cases.
- Each fixture should be kernel-checkable so the oracle harness can compare round-trip runs.

Usage will be wired into the bridge oracle harness once the tactic coverage stabilizes.
