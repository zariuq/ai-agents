import Mettapedia.OSLF.PathMap.Core
import Mettapedia.OSLF.PathMap.RelationBridge
import Mettapedia.OSLF.PathMap.Zipper
import Mettapedia.OSLF.PathMap.OSLFInstance
import Mettapedia.OSLF.PathMap.PLNBridge
import Mettapedia.OSLF.PathMap.SolomonoffBridge
import Mettapedia.OSLF.PathMap.Measure
import Mettapedia.OSLF.PathMap.WorldModelBridge

/-!
# PathMap Formalization

Lean 4 formalization of PathMap's algebraic interface, providing:

1. `PathMap.Core` — `AlgebraicResult`, `PathMapLattice`, `PathMapDistributiveLattice`,
   `PathMapQuantale` typeclasses with algebraic laws (`JoinComm`, `MeetComm`,
   `JoinIdem`, `MeetIdem`, `Absorption`).  Concrete instances for `Bool` (all 5
   laws) and `Finset α` (all 5 laws: `JoinComm`, `MeetComm`, `JoinIdem`,
   `MeetIdem`, `Absorption`) — proved without `sorry` or `native_decide`.

3. `PathMap.Zipper` — `ZipperMoving`, `ZipperValues`, `ZipperWriting`,
   `ZipperIteration`, `ZipperForking`, `ZipperAbsolutePath` typeclass hierarchy
   with the fundamental invariant ("focus cannot move above root") and
   `SubtractLeftBiased` (`psubtract` never returns `COUNTER_IDENT`).
   Also: `AlgebraicStatus` (in-place op result) and `joinAll`.

2. `PathMap.RelationBridge` — `RelationalSpace` typeclass abstracting the current
   `RelationEnv` (list-of-tuples) interface.  Shows that `RelationEnv` is a
   `RelationalSpace`, and that PathMap-backed stores also satisfy the interface.

## Relationship to OSLF

The OSLF's `RelationEnv` (`MeTTaIL/Engine.lean`) is the current concrete backend
for the `relationQuery` premise type.  PathMap is the planned replacement from
the MORK project.  The `RelationalSpace` typeclass in `RelationBridge` ensures
the OSLF formalization is not coupled to any specific storage backend.

## References
- PathMap `ring.rs`: `/home/zar/claude/hyperon/PathMap/src/ring.rs`
- PathMap book:      `1.01.00_algebraic_ops.md`, `1.01.01_algebraic_traits.md`
- MORK kernel:       `/home/zar/claude/hyperon/MORK/`
-/
