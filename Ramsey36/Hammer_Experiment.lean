import Ramsey36.Basic
import Mathlib.Tactic
import Hammer

open SimpleGraph

/-- The "Stuck Point" extracted as a standalone lemma. 
    We ask Hammer to bridge the gap between Finset.card, Fintype.card, and arithmetic. -/
lemma card_complement_bound (N : Finset (Fin 18)) (h : N.card ≤ 4) : 
  Fintype.card {x // x ∉ N} ≥ 14 := by
  -- We explicitly ask hammer to perform this "trivial" but syntactically heavy derivation.
  hammer
