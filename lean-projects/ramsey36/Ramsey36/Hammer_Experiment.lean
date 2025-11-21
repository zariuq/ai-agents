import Ramsey36.Basic
import Mathlib.Tactic
import Hammer

open SimpleGraph

/-- 
  The specific arithmetic/set-theory fact blocking Claim 1.
  If we have a set N of size ≤ 4 in a universe of size 18,
  the complement has size ≥ 14.
-/
lemma card_complement_bound (N : Finset (Fin 18)) (h : N.card ≤ 4) : 
  Fintype.card {x // x ∉ N} ≥ 14 := by
  -- "Hammer, smash this triviality!"
  hammer
