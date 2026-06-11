import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MultiStep
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-!
# Quiescent Outcomes for the ρ-Calculus

This file packages the semantic objects behind faithful run-to-quiescence:

- `MayReachable p`: all states reachable from `p` by zero or more reductions
- `Outcomes p`: the quiescent reachable states of `p`
- `SinglePathSafe p`: quiescent outcomes are unique, so a single-path run
  cannot silently discard observable behavior
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- All states semantically reachable from `p` in zero or more steps. -/
def MayReachable (p : Pattern) : Set Pattern :=
  { q | Nonempty (p ⇝* q) }

/-- The quiescent semantic outcomes of `p`. -/
def Outcomes (p : Pattern) : Set Pattern :=
  { q | Nonempty (p ⇝* q) ∧ NormalForm q }

/-- Single-path evaluation is semantically safe only when the quiescent
    outcome set is a subsingleton. -/
def SinglePathSafe (p : Pattern) : Prop :=
  (Outcomes p).Subsingleton

theorem mayReachable_refl (p : Pattern) :
    p ∈ MayReachable p := by
  exact ⟨ReducesStar.refl p⟩

theorem mayReachable_of_step {p q : Pattern}
    (h : Nonempty (p ⇝ q)) :
    q ∈ MayReachable p := by
  rcases h with ⟨hstep⟩
  exact ⟨ReducesStar.single hstep⟩

theorem outcomes_subset_mayReachable {p q : Pattern}
    (h : q ∈ Outcomes p) :
    q ∈ MayReachable p := by
  exact h.1

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
