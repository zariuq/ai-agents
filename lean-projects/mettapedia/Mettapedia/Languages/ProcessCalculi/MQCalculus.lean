import Mettapedia.Languages.ProcessCalculi.MQCalculus.MQCalculus

/-!
# Process Calculi: MQ-Calculus

Language-focused facade for the MQ-calculus formalization.

## Summary

The MQ-calculus (Stay & Meredith 2026) extends the π-calculus with quantum
measurement: communication IS measurement.  The Born rule `|⟨r|ψ⟩|²` determines
branching probabilities from first principles (derived, not axiomatized).

## Files

- `MQCalculus/Syntax.lean` — De Bruijn process grammar (sorry-free)
- `MQCalculus/Shift.lean` — Wire index shifting + all equational laws (sorry-free)
- `MQCalculus/StructuralCongruence.lean` — 4 SC axioms + closure (sorry-free)
- `MQCalculus/CommRule.lean` — Born-rule COMM branching + normalization theorem
- `MQCalculus/Reduction.lean` — Full `Reduces` + `MultiStep` (sorry-free)
- `MQCalculus/Denotational.lean` — Placeholder denotational semantics + invariance lemmas
- `MQCalculus/MQCalculus.lean` — Canary theorems + π/ρ-calculus connections
-/
