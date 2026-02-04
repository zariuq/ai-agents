import Mettapedia.Logic.HigherOrder.Basic
import Mettapedia.Logic.HigherOrder.HigherOrderReduction
import Mettapedia.Logic.HigherOrder.InferenceRuleBridge
import Mettapedia.Logic.HigherOrder.PredCode.Basic

/-!
# Higher-Order Probabilistic Logic Networks (HOI-PLN)

This module implements the HOI→FOI reduction from the PLN Book (Goertzel et al., 2009).

## Core Insight

**SatisfyingSets map Evaluation to Member**, enabling reduction of all higher-order
relations to first-order relations between sets.

## Main Components

- `HigherOrder.Basic`: Foundation and imports
- `HigherOrder.HigherOrderReduction`: Core HOI→FOI reduction theorems
- `HigherOrder.InferenceRuleBridge`: Bridge to existing PLN inference rules
- `HigherOrder.PredCode.Basic`: Predicate code definitions (WITHOUT Encodable - blocked)

## Status (Weeks 1-3 Complete, Week 4 Blocked)

✅ Week 1-2: All core definitions and reduction theorems (0 sorries, 0 axioms)
✅ Week 3: Strengthened structural properties (perfect implication/subset reflection)
❌ Week 4: PredCode BLOCKED - cannot prove Encodable for mutually recursive type
❌ Week 5: Solomonoff integration NOT STARTED - depends on Week 4

## Blockers

**Week 4 Blocker**: PredCode Encodable instance
- Mutually recursive inductive type creates circularity in instance resolution
- Requires custom derivation with well-founded recursion
- OR requires flattening to non-recursive representation
- This is NOT routine machinery - it requires substantial proof engineering

**Impact**: Without Encodable, cannot enumerate predicates for Solomonoff prior.
The evalPred function and basic properties are sound, but enumeration is blocked.

## Next Steps

- Resolve PredCode Encodable blocker (requires proof engineering expertise)
- OR explore alternative formalization that avoids mutual recursion
- Week 5 depends on Week 4 completion

## References

- PLN Book, Chapter 10, lines 1565-1612
- `PLNFirstOrder/` directory: 707 lines, 0 sorries
- `QuantaleWeakness.lean`: 820+ lines, complete weakness theory
-/
